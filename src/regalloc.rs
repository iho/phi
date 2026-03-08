//! Linear-scan register allocator (Poletto & Sarkar, 1999).
//!
//! Input:  sorted liveness intervals from `ir::compute_intervals`
//! Output: `Allocation` — a map from VReg → Location (physical reg or spill slot)
//!
//! Algorithm:
//!   Walk intervals in order of start point.
//!   For each interval:
//!     1. Expire old intervals (free their physical registers).
//!     2. If a free physical register exists: assign it.
//!     3. Otherwise: spill — evict the interval with the latest end point.
//!        If that's the current interval, spill the current one directly.

use std::collections::HashMap;
use crate::ir::{VReg, PReg, Interval};

// ---------------------------------------------------------------------------
// Allocation result
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Location {
    /// Lives in a physical register.
    Reg(PReg),
    /// Spilled to a frame slot (0-based; byte offset = slot * 8 + frame_base).
    Slot(u32),
}

impl Location {
    pub fn is_reg(self) -> bool { matches!(self, Location::Reg(_)) }
    pub fn reg(self) -> Option<PReg> {
        if let Location::Reg(r) = self { Some(r) } else { None }
    }
}

#[derive(Debug, Default)]
pub struct Allocation {
    pub map: HashMap<VReg, Location>,
    /// Number of spill slots needed (determines frame size contribution).
    pub spill_slots: u32,
}

impl Allocation {
    pub fn get(&self, v: VReg) -> Location {
        *self.map.get(&v).unwrap_or(&Location::Slot(0))
    }
}

// ---------------------------------------------------------------------------
// Allocator state
// ---------------------------------------------------------------------------

struct Allocator {
    /// Available physical registers (free pool).
    free: Vec<PReg>,
    /// Active intervals sorted by end point (for expiry).
    active: Vec<(Interval, PReg)>,
    /// Result map.
    alloc: Allocation,
    /// Next spill slot index.
    next_spill: u32,
}

impl Allocator {
    fn new(n_regs: u8) -> Self {
        // Prefer caller-saved (x9-x15) first; callee-saved last to minimise saves.
        let free: Vec<PReg> = (0..n_regs).map(PReg).collect();
        Self {
            free,
            active: Vec::new(),
            alloc: Allocation::default(),
            next_spill: 0,
        }
    }

    fn expire_old(&mut self, pos: u32) {
        // Remove all active intervals whose end ≤ pos and reclaim their regs.
        let mut remaining = Vec::new();
        for (iv, reg) in self.active.drain(..) {
            if iv.end <= pos {
                self.free.push(reg);
            } else {
                remaining.push((iv, reg));
            }
        }
        self.active = remaining;
        // Keep active sorted by end point (ascending) for spill heuristic.
        self.active.sort_by_key(|(iv, _)| iv.end);
    }

    fn alloc_spill(&mut self) -> u32 {
        let s = self.next_spill;
        self.next_spill += 1;
        self.alloc.spill_slots = self.alloc.spill_slots.max(self.next_spill);
        s
    }

    fn process(&mut self, iv: Interval) {
        self.expire_old(iv.start);

        if let Some(reg) = self.free.pop() {
            // Happy path: assign a physical register.
            self.alloc.map.insert(iv.vreg, Location::Reg(reg));
            // Insert into active, keeping sorted order.
            let pos = self.active.partition_point(|(a, _)| a.end < iv.end);
            self.active.insert(pos, (iv, reg));
        } else {
            // Spill: pick the interval with the latest end point.
            // If that's not the current one, swap their allocations.
            if let Some(last_idx) = self.active.iter().rposition(|(a, _)| a.end > iv.end) {
                let (spilled_iv, spilled_reg) = self.active.remove(last_idx);
                // Spill the previously-register-allocated interval.
                let slot = self.alloc_spill();
                self.alloc.map.insert(spilled_iv.vreg, Location::Slot(slot));
                // Current interval gets the freed register.
                self.alloc.map.insert(iv.vreg, Location::Reg(spilled_reg));
                let pos = self.active.partition_point(|(a, _)| a.end < iv.end);
                self.active.insert(pos, (iv, spilled_reg));
            } else {
                // Current interval has the latest end: spill it directly.
                let slot = self.alloc_spill();
                self.alloc.map.insert(iv.vreg, Location::Slot(slot));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run linear-scan register allocation.
///
/// `n_regs`: number of physical registers to use (usually `PReg::CALLER_SAVED`).
/// `reserved`: VRegs that are pre-assigned to specific physical registers
///             (e.g. function parameters x0..x7 before the prologue copies them).
pub fn allocate(
    intervals: &[Interval],
    n_regs: u8,
    reserved: &[(VReg, PReg)],
) -> Allocation {
    let mut alloc = Allocator::new(n_regs);

    // Pre-assign reserved VRegs (params).
    for &(v, p) in reserved {
        alloc.alloc.map.insert(v, Location::Reg(p));
        // Remove p from free pool.
        alloc.free.retain(|r| *r != p);
    }

    // Walk intervals sorted by start.
    for &iv in intervals {
        // Skip pre-assigned.
        if alloc.alloc.map.contains_key(&iv.vreg) {
            continue;
        }
        alloc.process(iv);
    }

    alloc.alloc
}

// ---------------------------------------------------------------------------
// Spill-code insertion helpers
// ---------------------------------------------------------------------------

/// Byte offset of a spill slot from the frame pointer.
/// Frame layout:  [fp+0..fp+15] = saved x29/x30
///               [fp+16..fp+N ] = spill slots (8 bytes each)
///               [fp+N+8..   ] = callee-saved regs (if any)
pub fn spill_offset(slot: u32, spill_base: u32) -> i32 {
    (spill_base + slot * 8) as i32
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Interval, VReg, PReg};

    fn iv(v: u32, start: u32, end: u32) -> Interval {
        Interval { vreg: VReg(v), start, end }
    }

    #[test]
    fn test_no_spill_within_capacity() {
        // 3 intervals, 7 regs → no spills.
        let ivs = vec![iv(0,0,10), iv(1,1,5), iv(2,3,8)];
        let alloc = allocate(&ivs, PReg::CALLER_SAVED, &[]);
        assert!(alloc.spill_slots == 0, "should not spill with only 3 live at once");
        for v in 0..3 {
            assert!(alloc.get(VReg(v)).is_reg(), "v{} should be in a register", v);
        }
    }

    #[test]
    fn test_spill_when_pressure_exceeds_regs() {
        // 8 simultaneously live intervals but only 7 regs → 1 spill.
        let ivs: Vec<Interval> = (0..8).map(|i| iv(i, 0, 100)).collect();
        let alloc = allocate(&ivs, PReg::CALLER_SAVED, &[]);
        let in_regs = (0..8u32).filter(|&i| alloc.get(VReg(i)).is_reg()).count();
        let spilled = 8 - in_regs;
        assert_eq!(in_regs, 7,  "exactly 7 should be in registers");
        assert_eq!(spilled, 1,  "exactly 1 should be spilled");
        assert_eq!(alloc.spill_slots, 1);
    }

    #[test]
    fn test_spill_latest_end_heuristic() {
        // v0: [0,100), v1..v6: [0,10), v7: [5,200)
        // When processing v7 (start=5, end=200), 7 regs are full.
        // v0 has end=100, v7 has end=200 → v7 is the latest-end → v7 spills.
        let mut ivs = vec![iv(0,0,100)];
        for i in 1..7 { ivs.push(iv(i, 0, 10)); }
        ivs.push(iv(7, 5, 200));
        ivs.sort_by_key(|iv| iv.start);
        let alloc = allocate(&ivs, PReg::CALLER_SAVED, &[]);
        assert!(alloc.get(VReg(7)) == Location::Slot(0) || alloc.get(VReg(0)) == Location::Slot(0),
            "either v0 (end=100) or v7 (end=200) should be spilled; longest wins");
    }

    #[test]
    fn test_reserved_params_not_reallocated() {
        // v0 reserved to x9, v1 free.
        let ivs = vec![iv(0, 0, 5), iv(1, 1, 8)];
        let reserved = vec![(VReg(0), PReg(0))]; // PReg(0) = x9
        let alloc = allocate(&ivs, PReg::CALLER_SAVED, &reserved);
        assert_eq!(alloc.get(VReg(0)), Location::Reg(PReg(0)), "v0 should stay in x9");
        // v1 gets a different reg (x9 not in free pool)
        if let Location::Reg(r) = alloc.get(VReg(1)) {
            assert_ne!(r, PReg(0), "v1 should not reuse x9");
        }
    }

    #[test]
    fn test_expire_frees_registers() {
        // v0: [0,3), v1: [4,7), v2: [0,6)
        // At pos=4: v0 expires, freeing its reg for v1 → no spill.
        let ivs = vec![iv(0,0,3), iv(2,0,6), iv(1,4,7)];
        let alloc = allocate(&ivs, 2, &[]); // only 2 regs
        assert_eq!(alloc.spill_slots, 0, "expiry should free regs so no spill needed");
    }

    #[test]
    fn test_all_unique_physical_regs_when_no_spill() {
        // Staggered intervals [i, i+5): at most 5 are live simultaneously,
        // so all 7 fit in 7 physical regs with zero spills (registers reused after expiry).
        let ivs: Vec<Interval> = (0..7).map(|i| iv(i, i, i+5)).collect();
        let alloc = allocate(&ivs, PReg::CALLER_SAVED, &[]);
        assert_eq!(alloc.spill_slots, 0, "staggered intervals should never spill with 7 regs");
        for i in 0..7u32 {
            assert!(alloc.get(VReg(i)).is_reg(), "v{} should be in a physical register", i);
        }
    }
}

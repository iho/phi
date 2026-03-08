//! Phi intermediate representation (3-address code).
//!
//! The lowering pipeline is:
//!   AST  →  IR (this module)  →  Liveness  →  Linear-scan RA  →  AArch64 emit
//!
//! Every value lives in a virtual register (VReg).  The IR is in
//! Administrative Normal Form: every sub-expression has a name, so there
//! are no nested expressions and evaluation order is fully explicit.

// ---------------------------------------------------------------------------
// Virtual / physical registers
// ---------------------------------------------------------------------------

/// Virtual register index.  Unlimited supply; RA maps these to PReg or spill slots.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VReg(pub u32);

impl std::fmt::Display for VReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// Physical AArch64 register index (0-based).
/// We use a fixed caller-saved bank: x9..x15  (indices 0..6 = 7 regs)
/// plus x19..x27 as callee-saved overflow (indices 7..15 = 9 regs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PReg(pub u8);

impl PReg {
    pub fn name(self) -> &'static str {
        match self.0 {
            0 => "x9",  1 => "x10", 2 => "x11", 3 => "x12",
            4 => "x13", 5 => "x14", 6 => "x15",
            // callee-saved overflow
            7 => "x19", 8 => "x20", 9 => "x21", 10 => "x22",
            11 => "x23", 12 => "x24", 13 => "x25", 14 => "x26",
            15 => "x27",
            _ => "xUNK",
        }
    }
    /// Number of caller-saved physical registers available for RA.
    pub const CALLER_SAVED: u8 = 7;
    /// Total physical registers (caller + callee saved).
    pub const TOTAL: u8 = 16;
}

// ---------------------------------------------------------------------------
// Labels
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Label(pub u32);

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ".L{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// Comparison conditions
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cond { Eq, Ne, Lt, Le, Gt, Ge }

impl Cond {
    pub fn arm_suffix(self) -> &'static str {
        match self {
            Cond::Eq => "eq", Cond::Ne => "ne",
            Cond::Lt => "lt", Cond::Le => "le",
            Cond::Gt => "gt", Cond::Ge => "ge",
        }
    }
    pub fn invert(self) -> Self {
        match self {
            Cond::Eq => Cond::Ne, Cond::Ne => Cond::Eq,
            Cond::Lt => Cond::Ge, Cond::Le => Cond::Gt,
            Cond::Gt => Cond::Le, Cond::Ge => Cond::Lt,
        }
    }
}

// ---------------------------------------------------------------------------
// IR instructions
// ---------------------------------------------------------------------------

/// Calling convention slot: args are passed in x0-x7 before the CALL instr.
/// The IR makes this explicit with `SetArg` and `GetArg`.
#[derive(Debug, Clone)]
pub enum Instr {
    // ---- Constants --------------------------------------------------------
    /// dst = tagged_integer(n)  i.e.  dst = (n << 1) | 1
    Int(VReg, i64),
    /// dst = 1  (nil / unit / false)
    Nil(VReg),
    /// dst = address of global symbol (function pointer or data label)
    Global(VReg, String),

    // ---- Data movement ----------------------------------------------------
    Mov(VReg, VReg),

    // ---- Arithmetic (tagged integers) ------------------------------------
    /// dst = lhs + rhs   (untag→op→retag)
    Add(VReg, VReg, VReg),
    Sub(VReg, VReg, VReg),
    Mul(VReg, VReg, VReg),
    Div(VReg, VReg, VReg),
    Neg(VReg, VReg),

    // ---- Bitwise (on raw tagged values) -----------------------------------
    And(VReg, VReg, VReg),
    Or(VReg, VReg, VReg),

    // ---- Comparisons (return tagged bool: 3=true, 1=false) ---------------
    Cmp(VReg, VReg, Cond, VReg),

    // ---- Memory -----------------------------------------------------------
    /// dst = *(base + byte_offset)
    Load(VReg, VReg, i32),
    /// *(base + byte_offset) = src
    Store(VReg, i32, VReg),

    // ---- Calls ------------------------------------------------------------
    /// Place argument in the i-th call slot (x0..x7).
    SetArg(u8, VReg),
    /// dst = direct call to named symbol with `n_args` args already in x0..
    CallDirect(VReg, String, u8),
    /// dst = indirect call through closure: fn-ptr at closure[1], n_args args in x0..
    CallFun(VReg, VReg, u8),

    // ---- Control flow -----------------------------------------------------
    Label(Label),
    Jump(Label),
    /// if vreg == imm (raw) goto lbl, else fall through
    BranchEq(VReg, i64, Label),
    /// if vreg != imm (raw) goto lbl, else fall through
    BranchNe(VReg, i64, Label),
    /// Conditional branch on a tagged bool (true=3, false=1)
    BranchTrue(VReg, Label),
    BranchFalse(VReg, Label),

    // ---- Return -----------------------------------------------------------
    Ret(VReg),
}

// ---------------------------------------------------------------------------
// IR function / module
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct IrFun {
    pub name: String,
    pub arity: u32,
    /// Param virtual registers (correspond to arg registers x0..xN)
    pub params: Vec<VReg>,
    pub body: Vec<Instr>,
    /// One past the highest VReg index used (for RA to allocate intervals)
    pub vreg_count: u32,
}

#[derive(Debug, Clone)]
pub struct IrModule {
    pub name: String,
    pub functions: Vec<IrFun>,
    /// Read-only string/atom literals: (label, content)
    pub string_literals: Vec<(String, String)>,
}

// ---------------------------------------------------------------------------
// Liveness intervals
// ---------------------------------------------------------------------------

/// Half-open interval [start, end) where start/end are instruction indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub vreg: VReg,
    pub start: u32,
    pub end: u32,
}

impl Interval {
    pub fn is_expired_before(&self, pos: u32) -> bool { self.end <= pos }
    pub fn starts_at_or_before(&self, pos: u32) -> bool { self.start <= pos }
}

/// Compute liveness intervals for all VRegs in a function.
/// Uses a linear scan over instructions; each VReg's interval spans
/// [first_def, last_use + 1).
pub fn compute_intervals(fun: &IrFun) -> Vec<Interval> {
    let n = fun.vreg_count as usize;
    let mut first_def = vec![u32::MAX; n];
    let mut last_use  = vec![0u32; n];

    for (pos, instr) in fun.body.iter().enumerate() {
        let pos = pos as u32;
        let (defs, uses) = instr_def_use(instr);
        for d in defs { first_def[d.0 as usize] = first_def[d.0 as usize].min(pos); }
        for u in uses { last_use [u.0 as usize] = last_use [u.0 as usize].max(pos + 1); }
    }

    // Params are live from instruction 0
    for &p in &fun.params {
        first_def[p.0 as usize] = 0;
        last_use[p.0 as usize] = last_use[p.0 as usize].max(1);
    }

    let mut intervals: Vec<Interval> = (0..n as u32)
        .filter(|&i| first_def[i as usize] != u32::MAX)
        .map(|i| Interval {
            vreg:  VReg(i),
            start: first_def[i as usize],
            end:   last_use[i as usize].max(first_def[i as usize] + 1),
        })
        .collect();

    intervals.sort_by_key(|iv| iv.start);
    intervals
}

fn instr_def_use(instr: &Instr) -> (Vec<VReg>, Vec<VReg>) {
    use Instr::*;
    match instr {
        Int(d, _)           => (vec![*d], vec![]),
        Nil(d)              => (vec![*d], vec![]),
        Global(d, _)        => (vec![*d], vec![]),
        Mov(d, s)           => (vec![*d], vec![*s]),
        Add(d,l,r) | Sub(d,l,r) | Mul(d,l,r) | Div(d,l,r)
                            => (vec![*d], vec![*l, *r]),
        And(d,l,r) | Or(d,l,r)
                            => (vec![*d], vec![*l, *r]),
        Neg(d, s)           => (vec![*d], vec![*s]),
        Cmp(d,l,_,r)        => (vec![*d], vec![*l, *r]),
        Load(d, b, _)       => (vec![*d], vec![*b]),
        Store(b, _, s)      => (vec![],   vec![*b, *s]),
        SetArg(_, s)        => (vec![],   vec![*s]),
        CallDirect(d, _, _) => (vec![*d], vec![]),
        CallFun(d, f, _)    => (vec![*d], vec![*f]),
        Label(_) | Jump(_)  => (vec![], vec![]),
        BranchEq(v,_,_) | BranchNe(v,_,_)
                            => (vec![], vec![*v]),
        BranchTrue(v,_) | BranchFalse(v,_)
                            => (vec![], vec![*v]),
        Ret(v)              => (vec![], vec![*v]),
    }
}

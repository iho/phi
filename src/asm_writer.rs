#![allow(dead_code)]
//! AArch64 (Apple M1 / ARM64) native assembly emitter for Phi.
//!
//! Value representation (tagged pointers, OCaml-style):
//!   Integer n  → (n << 1) | 1        (odd pointer, fits in register)
//!   Boolean    → 1 = true, 3 = false  (atoms are odd constants)
//!   Unit       → 1                    (same tag as integer 0)
//!   Heap ptr p → p                    (even, 8-byte aligned)
//!
//! Heap layout for closures:
//!   [arity:u64, fptr:*fn, n_free:u64, fv0, fv1, ...]
//!
//! Heap layout for tuples (ADT constructors):
//!   [tag_atom:u64, field0, field1, ...]   where tag is a string pointer or index
//!
//! Cons cell:
//!   [head:u64, tail:u64]   nil = 1 (tagged integer 0)
//!
//! Calling convention:
//!   - Args: x0..x7 (spill to stack beyond 8)
//!   - Return: x0
//!   - Callee-saved: x19..x28, x29 (fp), x30 (lr)
//!   - Caller-saved: x0..x15
//!   - Stack: 16-byte aligned at call site
//!
//! Each generated function has its own frame:
//!   stp  x29, x30, [sp, #-16]!
//!   mov  x29, sp
//!   ...
//!   ldp  x29, x30, [sp], #16
//!   ret

use std::collections::HashMap;
use crate::ast;
use crate::env::Env;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

pub fn generate_asm(module: &ast::Module, env: &Env) -> String {
    let mut emitter = AsmEmitter::new(module.name.clone(), env);
    emitter.emit_module(module);
    emitter.finish()
}

// ---------------------------------------------------------------------------
// Emitter state
// ---------------------------------------------------------------------------

struct AsmEmitter<'e> {
    module_name: String,
    env: &'e Env,
    out: String,
    rodata: String,       // .section __TEXT,__cstring for string/atom literals
    label_ctr: u32,
    /// string literal → label name
    string_cache: HashMap<String, String>,
    /// atom string → label name  
    atom_cache: HashMap<String, String>,
}

impl<'e> AsmEmitter<'e> {
    fn new(module_name: String, env: &'e Env) -> Self {
        Self {
            module_name,
            env,
            out: String::new(),
            rodata: String::new(),
            label_ctr: 0,
            string_cache: HashMap::new(),
            atom_cache: HashMap::new(),
        }
    }

    fn fresh_label(&mut self) -> String {
        let n = self.label_ctr;
        self.label_ctr += 1;
        format!("L{}_{}", self.module_name.replace('.', "_"), n)
    }

    fn mangle(&self, name: &str) -> String {
        // Apple Mach-O: leading underscore + dot→underscore
        format!("_Phi_{}_{}", self.module_name.replace('.', "_"), name.replace('.', "_"))
    }

    fn emit(&mut self, s: &str) {
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn finish(self) -> String {
        let mut result = String::new();
        // Text segment header
        result.push_str("\t.section\t__TEXT,__text,regular,pure_instructions\n");
        result.push_str("\t.p2align\t2\n\n");
        result.push_str(&self.out);
        // Read-only data (strings, atoms)
        if !self.rodata.is_empty() {
            result.push_str("\n\t.section\t__TEXT,__cstring,cstring_literals\n");
            result.push_str(&self.rodata);
        }
        result
    }

    // -----------------------------------------------------------------------
    // String / atom helpers
    // -----------------------------------------------------------------------

    fn emit_string_literal(&mut self, s: &str) -> String {
        if let Some(lbl) = self.string_cache.get(s) {
            return lbl.clone();
        }
        let lbl = self.fresh_label();
        let escaped = s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n");
        self.rodata.push_str(&format!("{}:\n\t.asciz\t\"{}\"\n", lbl, escaped));
        self.string_cache.insert(s.to_string(), lbl.clone());
        lbl
    }

    // -----------------------------------------------------------------------
    // Module-level emission
    // -----------------------------------------------------------------------

    fn emit_module(&mut self, module: &ast::Module) {
        self.emit(&format!("// Module: Phi.{}", module.name));
        self.emit("");

        for decl in &module.declarations {
            self.emit_top_decl(decl);
        }
    }

    fn emit_top_decl(&mut self, decl: &ast::Decl) {
        match decl {
            ast::Decl::Value(name, binders, body, _where) => {
                self.emit_function(name, binders, body);
            }
            ast::Decl::PatBind(binder, expr, _) => {
                // Top-level constant: emit as a 0-arg function
                if let ast::Binder::Var(name) = binder {
                    self.emit_function(name, &[], expr);
                }
            }
            // Data declarations, type aliases, imports: no code
            _ => {}
        }
    }

    // -----------------------------------------------------------------------
    // Function emission
    // -----------------------------------------------------------------------

    fn emit_function(&mut self, name: &str, binders: &[ast::Binder], body: &ast::Expr) {
        let label = self.mangle(name);

        // ── Step 1: lower AST → IR ───────────────────────────────────────────
        let mut builder = IrBuilder::new(self.module_name.clone(), self.label_ctr);

        // Allocate one VReg per parameter and bind its name
        let params: Vec<VReg> = binders.iter().enumerate().map(|(i, b)| {
            let v = builder.fresh();
            if let ast::Binder::Var(n) = b { builder.vars.insert(n.clone(), v); }
            let _ = i;
            v
        }).collect();

        let _result_v = builder.lower(body);
        let (fun, extra_rodata, next_label) = builder.build_fun(label.clone(), params);
        self.label_ctr = next_label;

        // Accumulate string literals from this function
        for (lbl, s) in extra_rodata {
            if !self.string_cache.contains_key(&s) {
                let escaped = s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n");
                self.rodata.push_str(&format!("{}:\n\t.asciz\t\"{}\"\n", lbl, escaped));
                self.string_cache.insert(s, lbl);
            }
        }

        // ── Step 2: liveness + linear-scan RA ───────────────────────────────
        let intervals = ir::compute_intervals(&fun);

        // Reserve physical regs for params: param[i] → arg reg is x0..x7 at call
        // but inside the function body we allocate them from the caller-saved bank.
        // No hard reservation needed; RA may assign them freely.
        let alloc = regalloc::allocate(&intervals, ir::PReg::CALLER_SAVED, &[]);

        // ── Step 3: emit ARM64 from allocated IR ─────────────────────────────
        emit_ir_fn(&fun, &alloc, alloc.spill_slots, &label, &mut self.out);
    }

    // -----------------------------------------------------------------------
    // Expression emission  →  result always ends up in x0
    // -----------------------------------------------------------------------

    fn emit_expr(&mut self, expr: &ast::Expr, ctx: &mut FnCtx) {
        match expr {
            // ------------------------------------------------------------------
            ast::Expr::Number(n) => {
                // Tagged integer: (n << 1) | 1
                let tagged = ((*n as i64) << 1) | 1;
                self.emit_load_imm("x0", tagged);
            }

            ast::Expr::Unit => {
                self.emit("\tmov\tx0, #1"); // same tag as integer 0
            }

            ast::Expr::Var(name) => {
                self.emit_var(name, ctx);
            }

            ast::Expr::BinOp(lhs, op, rhs) => {
                self.emit_binop(lhs, op, rhs, ctx);
            }

            ast::Expr::If(cond, then_e, else_e) => {
                self.emit_if(cond, then_e, else_e, ctx);
            }

            ast::Expr::App(func, arg) => {
                self.emit_app_chain(expr, ctx);
                let _ = (func, arg); // suppress unused warning
            }

            ast::Expr::Lam(binders, body) => {
                self.emit_closure(binders, body, ctx);
            }

            ast::Expr::Let(decls, body) => {
                self.emit_let(decls, body, ctx);
            }

            ast::Expr::String(s) => {
                let lbl = self.emit_string_literal(s);
                self.emit(&format!("\tadrp\tx0, {}@PAGE", lbl));
                self.emit(&format!("\tadd\tx0, x0, {}@PAGEOFF", lbl));
            }

            ast::Expr::Tuple(elems) => {
                self.emit_tuple(elems, ctx);
            }

            ast::Expr::List(elems, tail) => {
                self.emit_list(elems, tail.as_deref(), ctx);
            }

            ast::Expr::Case(scrutinees, branches) => {
                self.emit_case(scrutinees, branches, ctx);
            }

            ast::Expr::TypeAnn(inner, _) => {
                self.emit_expr(inner, ctx);
            }

            ast::Expr::Paren(inner) => {
                self.emit_expr(inner, ctx);
            }

            // Atoms, chars, floats: encode as immediate or pointer
            ast::Expr::Atom(a) => {
                let lbl = self.emit_string_literal(a);
                self.emit(&format!("\tadrp\tx0, {}@PAGE", lbl));
                self.emit(&format!("\tadd\tx0, x0, {}@PAGEOFF", lbl));
            }

            ast::Expr::Char(c) => {
                let tagged = ((*c as i64) << 1) | 1;
                self.emit_load_imm("x0", tagged);
            }

            ast::Expr::Negate(e) => {
                self.emit_expr(e, ctx);
                // untag, negate, retag
                self.emit("\tasr\tx0, x0, #1"); // untag
                self.emit("\tneg\tx0, x0");
                self.emit("\tlsl\tx1, x0, #1");
                self.emit("\torr\tx0, x1, #1");
            }

            _ => {
                // Unimplemented: emit a placeholder (returns tagged 0)
                self.emit("\tmov\tx0, #1 // TODO: unimplemented expr");
            }
        }
    }

    // -----------------------------------------------------------------------
    // Variable lookup
    // -----------------------------------------------------------------------

    fn emit_var(&mut self, name: &str, ctx: &mut FnCtx) {
        if name == "true" {
            self.emit("\tmov\tx0, #3"); // (1 << 1) | 1
            return;
        }
        if name == "false" {
            self.emit("\tmov\tx0, #1"); // (0 << 1) | 1  — we use 1=false
            return;
        }

        // Local variable?
        if let Some(slot) = ctx.lookup(name) {
            let off = slot * 8 + 16;
            self.emit(&format!("\tldr\tx0, [x29, #{}]", off));
            return;
        }

        // Global function reference — emit as function pointer
        let label = self.mangle(name);
        self.emit(&format!("\tadrp\tx0, {}@PAGE", label));
        self.emit(&format!("\tadd\tx0, x0, {}@PAGEOFF", label));
    }

    // -----------------------------------------------------------------------
    // Binary operations  (integers only for now)
    // -----------------------------------------------------------------------

    fn emit_binop(&mut self, lhs: &ast::Expr, op: &str, rhs: &ast::Expr, ctx: &mut FnCtx) {
        // Evaluate lhs → x0, save; rhs → x1
        self.emit_expr(lhs, ctx);
        let slot = ctx.alloc_temp();
        let off = slot * 8 + 16;
        self.emit(&format!("\tstr\tx0, [x29, #{}]", off));

        self.emit_expr(rhs, ctx);
        self.emit("\tmov\tx1, x0"); // rhs in x1
        self.emit(&format!("\tldr\tx0, [x29, #{}]", off)); // lhs back in x0
        ctx.free_temp();

        match op {
            "+" => {
                // Untagged add: (a-1) + (b-1) + 1 = a+b-1, but simpler:
                // untag both, add, retag
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tadd\tx0, x0, x1");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "-" => {
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tsub\tx0, x0, x1");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "*" => {
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tmul\tx0, x0, x1");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "/" => {
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tsdiv\tx0, x0, x1");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "==" => {
                self.emit("\tcmp\tx0, x1");
                self.emit("\tcset\tx0, eq");
                // encode: true=3, false=1
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "/=" => {
                self.emit("\tcmp\tx0, x1");
                self.emit("\tcset\tx0, ne");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "<" => {
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tcmp\tx0, x1");
                self.emit("\tcset\tx0, lt");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            ">" => {
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tcmp\tx0, x1");
                self.emit("\tcset\tx0, gt");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "<=" => {
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tcmp\tx0, x1");
                self.emit("\tcset\tx0, le");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            ">=" => {
                self.emit("\tasr\tx0, x0, #1");
                self.emit("\tasr\tx1, x1, #1");
                self.emit("\tcmp\tx0, x1");
                self.emit("\tcset\tx0, ge");
                self.emit("\tlsl\tx0, x0, #1");
                self.emit("\torr\tx0, x0, #1");
            }
            "&&" => {
                // Both are true(3) or false(1) — use bitwise and on raw tagged vals
                self.emit("\tand\tx0, x0, x1");
            }
            "||" => {
                self.emit("\torr\tx0, x0, x1");
                self.emit("\torr\tx0, x0, #1"); // ensure tag bit
            }
            _ => {
                self.emit(&format!("\t// unimplemented op: {}", op));
                self.emit("\tmov\tx0, #1");
            }
        }
    }

    // -----------------------------------------------------------------------
    // If / then / else
    // -----------------------------------------------------------------------

    fn emit_if(&mut self, cond: &ast::Expr, then_e: &ast::Expr, else_e: &ast::Expr, ctx: &mut FnCtx) {
        let else_lbl = self.fresh_label();
        let end_lbl  = self.fresh_label();

        self.emit_expr(cond, ctx);
        // false = 1 (tagged 0), true = 3 (tagged 1)
        self.emit("\tcmp\tx0, #1"); // is it false?
        self.emit(&format!("\tb.eq\t{}", else_lbl));

        self.emit_expr(then_e, ctx);
        self.emit(&format!("\tb\t{}", end_lbl));

        self.emit(&format!("{}:", else_lbl));
        self.emit_expr(else_e, ctx);

        self.emit(&format!("{}:", end_lbl));
    }

    // -----------------------------------------------------------------------
    // Application chains:  f a b c  →  collect args, call f
    // -----------------------------------------------------------------------

    fn emit_app_chain(&mut self, expr: &ast::Expr, ctx: &mut FnCtx) {
        // Collect the chain: f a0 a1 ... aN
        let mut chain = Vec::new();
        let mut cur = expr;
        loop {
            if let ast::Expr::App(func, arg) = cur {
                chain.push(arg.as_ref());
                cur = func.as_ref();
            } else {
                break;
            }
        }
        chain.reverse(); // now chain[0] is first arg

        // Evaluate function head into a temp slot
        let func_slot = ctx.alloc_temp();
        let func_off = func_slot * 8 + 16;
        self.emit_expr(cur, ctx);
        self.emit(&format!("\tstr\tx0, [x29, #{}]", func_off));

        // Evaluate args and save them
        let mut arg_slots = Vec::new();
        for arg in &chain {
            self.emit_expr(arg, ctx);
            let s = ctx.alloc_temp();
            let o = s * 8 + 16;
            self.emit(&format!("\tstr\tx0, [x29, #{}]", o));
            arg_slots.push((s, o));
        }

        // Load args into x0..x7
        for (i, (_, off)) in arg_slots.iter().enumerate() {
            let reg = arg_reg(i);
            self.emit(&format!("\tldr\t{}, [x29, #{}]", reg, off));
        }

        // Load function pointer and call
        self.emit(&format!("\tldr\tx8, [x29, #{}]", func_off));

        if let ast::Expr::Var(name) = cur {
            if !ctx.has_var(name) {
                // Known static call
                let label = self.mangle(name);
                // Pop temps first
                for (s, _) in arg_slots.iter().rev() { let _ = s; ctx.free_temp(); }
                ctx.free_temp(); // func_slot
                self.emit(&format!("\tbl\t{}", label));
                return;
            }
        }

        // Dynamic call via closure: x8 = closure ptr
        // Closure layout: [arity, fptr, n_free, fv0, ...]
        self.emit("\tldr\tx9, [x8, #8]"); // fptr
        self.emit("\tblr\tx9");

        for _ in arg_slots.iter() { ctx.free_temp(); }
        ctx.free_temp();
    }

    // -----------------------------------------------------------------------
    // Closures (lambda)
    // -----------------------------------------------------------------------

    fn emit_closure(&mut self, binders: &[ast::Binder], body: &ast::Expr, ctx: &mut FnCtx) {
        // Collect free variables
        let bound: std::collections::HashSet<String> = binders.iter().filter_map(|b| {
            if let ast::Binder::Var(v) = b { Some(v.clone()) } else { None }
        }).collect();
        let mut free: Vec<String> = Vec::new();
        collect_free_vars(body, &bound, ctx, &mut free);
        free.sort();
        free.dedup();

        // Emit the lambda body as a new function
        let lambda_label = {
            let n = self.label_ctr;
            self.label_ctr += 1;
            format!("_Phi_{}_lambda{}", self.module_name.replace('.', "_"), n)
        };

        // Save current output and ctx, emit lambda
        let saved_out = std::mem::take(&mut self.out);
        let arity = binders.len();
        let mut lambda_ctx = FnCtx::new(arity + free.len());

        // Lambda ABI: first `arity` args in x0..xN are real args;
        // last arg (xN+1) is the closure env pointer (free vars struct)
        let env_arg_idx = arity;

        self.emit(&format!("\t.globl\t{}", lambda_label));
        self.emit(&format!("{}:", lambda_label));
        let frame = lambda_ctx.frame_size();
        self.emit(&format!("\tsub\tsp, sp, #{}", frame + 16));
        self.emit("\tstp\tx29, x30, [sp]");
        self.emit("\tadd\tx29, sp, #0");

        // Save args
        for (i, b) in binders.iter().enumerate() {
            if let ast::Binder::Var(v) = b {
                let s = lambda_ctx.alloc_local(v.clone());
                self.emit(&format!("\tstr\t{}, [x29, #{}]", arg_reg(i), s * 8 + 16));
            }
        }

        // Load free vars from env struct (last arg = env ptr in x{env_arg_idx})
        let env_reg = arg_reg(env_arg_idx);
        for (fi, fv_name) in free.iter().enumerate() {
            let s = lambda_ctx.alloc_local(fv_name.clone());
            self.emit(&format!("\tldr\tx9, [{}, #{}]", env_reg, fi * 8));
            self.emit(&format!("\tstr\tx9, [x29, #{}]", s * 8 + 16));
        }

        self.emit_expr(body, &mut lambda_ctx);
        self.emit("\tldp\tx29, x30, [sp]");
        self.emit(&format!("\tadd\tsp, sp, #{}", frame + 16));
        self.emit("\tret\n");

        let lambda_code = std::mem::replace(&mut self.out, saved_out);
        // Append lambda code after current function (will be appended at end)
        self.out.push_str(&lambda_code);

        // --- Now allocate the closure object at runtime ---
        // Call phi_alloc(n_words) → x0 = heap ptr
        let n_words = 3 + free.len(); // arity, fptr, n_free, fvs...
        self.emit_load_imm("x0", n_words as i64);
        self.emit("\tbl\t_phi_alloc");
        let clo_slot = ctx.alloc_temp();
        let clo_off = clo_slot * 8 + 16;
        self.emit(&format!("\tstr\tx0, [x29, #{}]", clo_off));

        // Store arity
        self.emit_load_imm("x1", arity as i64);
        self.emit(&format!("\tldr\tx9, [x29, #{}]", clo_off));
        self.emit("\tstr\tx1, [x9, #0]");

        // Store function pointer
        self.emit(&format!("\tadrp\tx1, {}@PAGE", lambda_label));
        self.emit(&format!("\tadd\tx1, x1, {}@PAGEOFF", lambda_label));
        self.emit(&format!("\tldr\tx9, [x29, #{}]", clo_off));
        self.emit("\tstr\tx1, [x9, #8]");

        // Store n_free
        self.emit_load_imm("x1", free.len() as i64);
        self.emit(&format!("\tldr\tx9, [x29, #{}]", clo_off));
        self.emit("\tstr\tx1, [x9, #16]");

        // Store each free variable
        for (fi, fv_name) in free.iter().enumerate() {
            if let Some(s) = ctx.lookup(fv_name) {
                let off = s * 8 + 16;
                self.emit(&format!("\tldr\tx1, [x29, #{}]", off));
            } else {
                // global
                let lbl = self.mangle(fv_name);
                self.emit(&format!("\tadrp\tx1, {}@PAGE", lbl));
                self.emit(&format!("\tadd\tx1, x1, {}@PAGEOFF", lbl));
            }
            self.emit(&format!("\tldr\tx9, [x29, #{}]", clo_off));
            self.emit(&format!("\tstr\tx1, [x9, #{}]", 24 + fi * 8));
        }

        // Return closure pointer in x0
        self.emit(&format!("\tldr\tx0, [x29, #{}]", clo_off));
        ctx.free_temp();
    }

    // -----------------------------------------------------------------------
    // Let bindings
    // -----------------------------------------------------------------------

    fn emit_let(&mut self, decls: &[ast::Decl], body: &ast::Expr, ctx: &mut FnCtx) {
        for decl in decls {
            match decl {
                ast::Decl::Value(name, binders, rhs, _) if binders.is_empty() => {
                    self.emit_expr(rhs, ctx);
                    let slot = ctx.alloc_local(name.clone());
                    let off = slot * 8 + 16;
                    self.emit(&format!("\tstr\tx0, [x29, #{}]", off));
                }
                ast::Decl::PatBind(ast::Binder::Var(name), rhs, _) => {
                    self.emit_expr(rhs, ctx);
                    let slot = ctx.alloc_local(name.clone());
                    let off = slot * 8 + 16;
                    self.emit(&format!("\tstr\tx0, [x29, #{}]", off));
                }
                ast::Decl::Value(name, binders, rhs, _) => {
                    // Local function → closure
                    let lam = ast::Expr::Lam(binders.clone(), Box::new(rhs.clone()));
                    self.emit_expr(&lam, ctx);
                    let slot = ctx.alloc_local(name.clone());
                    let off = slot * 8 + 16;
                    self.emit(&format!("\tstr\tx0, [x29, #{}]", off));
                }
                _ => {}
            }
        }
        self.emit_expr(body, ctx);
    }

    // -----------------------------------------------------------------------
    // Tuples  →  heap-allocated array: [n_elems, e0, e1, ...]
    // -----------------------------------------------------------------------

    fn emit_tuple(&mut self, elems: &[ast::Expr], ctx: &mut FnCtx) {
        let n = elems.len();
        // Allocate
        self.emit_load_imm("x0", (n + 1) as i64);
        self.emit("\tbl\t_phi_alloc");
        let tup_slot = ctx.alloc_temp();
        let tup_off = tup_slot * 8 + 16;
        self.emit(&format!("\tstr\tx0, [x29, #{}]", tup_off));
        // Store length
        self.emit_load_imm("x1", n as i64);
        self.emit(&format!("\tldr\tx9, [x29, #{}]", tup_off));
        self.emit("\tstr\tx1, [x9, #0]");
        // Store elements
        for (i, elem) in elems.iter().enumerate() {
            self.emit_expr(elem, ctx);
            self.emit(&format!("\tldr\tx9, [x29, #{}]", tup_off));
            self.emit(&format!("\tstr\tx0, [x9, #{}]", 8 + i * 8));
        }
        self.emit(&format!("\tldr\tx0, [x29, #{}]", tup_off));
        ctx.free_temp();
    }

    // -----------------------------------------------------------------------
    // Lists  →  linked cons cells; nil = tagged 0 = 1
    // -----------------------------------------------------------------------

    fn emit_list(&mut self, elems: &[ast::Expr], tail: Option<&ast::Expr>, ctx: &mut FnCtx) {
        // Build from back to front
        // First evaluate tail
        if let Some(t) = tail {
            self.emit_expr(t, ctx);
        } else {
            self.emit("\tmov\tx0, #1"); // nil
        }
        let tail_slot = ctx.alloc_temp();
        let tail_off = tail_slot * 8 + 16;
        self.emit(&format!("\tstr\tx0, [x29, #{}]", tail_off));

        for elem in elems.iter().rev() {
            self.emit_expr(elem, ctx);
            let hd_slot = ctx.alloc_temp();
            let hd_off = hd_slot * 8 + 16;
            self.emit(&format!("\tstr\tx0, [x29, #{}]", hd_off));

            // alloc cons cell (2 words)
            self.emit("\tmov\tx0, #2");
            self.emit("\tbl\t_phi_alloc");
            // store head
            self.emit(&format!("\tldr\tx1, [x29, #{}]", hd_off));
            self.emit("\tstr\tx1, [x0, #0]");
            // store tail
            self.emit(&format!("\tldr\tx1, [x29, #{}]", tail_off));
            self.emit("\tstr\tx1, [x0, #8]");
            // new tail = this cons
            self.emit(&format!("\tstr\tx0, [x29, #{}]", tail_off));

            ctx.free_temp(); // hd_slot
        }
        self.emit(&format!("\tldr\tx0, [x29, #{}]", tail_off));
        ctx.free_temp(); // tail_slot
    }

    // -----------------------------------------------------------------------
    // Case expression (basic: single scrutinee, constructor/literal patterns)
    // -----------------------------------------------------------------------

    fn emit_case(&mut self, scrutinees: &[ast::Expr], branches: &[ast::CaseBranch], ctx: &mut FnCtx) {
        if scrutinees.len() != 1 {
            self.emit("\tmov\tx0, #1 // TODO: multi-scrutinee case");
            return;
        }
        self.emit_expr(&scrutinees[0], ctx);
        let scr_slot = ctx.alloc_temp();
        let scr_off = scr_slot * 8 + 16;
        self.emit(&format!("\tstr\tx0, [x29, #{}]", scr_off));

        let end_lbl = self.fresh_label();
        let mut next_labels: Vec<String> = (0..branches.len()).map(|_| self.fresh_label()).collect();
        next_labels.push(end_lbl.clone()); // sentinel

        for (bi, branch) in branches.iter().enumerate() {
            let next = next_labels[bi + 1].clone();
            let fail = next_labels[bi].clone(); // actually the branch label
            self.emit(&format!("{}:", next_labels[bi]));
            // Reload scrutinee
            self.emit(&format!("\tldr\tx0, [x29, #{}]", scr_off));
            // Match binder
            if branch.binders.len() == 1 {
                self.emit_match_binder(&branch.binders[0], "x0", &next, ctx);
            }
            // Emit body
            self.emit_expr(&branch.body, ctx);
            self.emit(&format!("\tb\t{}", end_lbl));
            let _ = fail;
        }

        self.emit(&format!("{}:", end_lbl));
        ctx.free_temp();
    }

    fn emit_match_binder(&mut self, binder: &ast::Binder, reg: &str, fail_lbl: &str, ctx: &mut FnCtx) {
        match binder {
            ast::Binder::Wildcard => {}
            ast::Binder::Number(n) => {
                let tagged = ((*n as i64) << 1) | 1;
                self.emit_load_imm("x9", tagged);
                self.emit(&format!("\tcmp\t{}, x9", reg));
                self.emit(&format!("\tb.ne\t{}", fail_lbl));
            }
            ast::Binder::Atom(a) => {
                // atom binders: compare against known atom constants
                if a == "true" {
                    self.emit(&format!("\tcmp\t{}, #3", reg));
                    self.emit(&format!("\tb.ne\t{}", fail_lbl));
                } else if a == "false" {
                    self.emit(&format!("\tcmp\t{}, #1", reg));
                    self.emit(&format!("\tb.ne\t{}", fail_lbl));
                }
            }
            ast::Binder::Var(n) => {
                let s = ctx.alloc_local(n.clone());
                let off = s * 8 + 16;
                self.emit(&format!("\tstr\t{}, [x29, #{}]", reg, off));
            }
            _ => {} // complex patterns: skip for now
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn emit_load_imm(&mut self, reg: &str, val: i64) {
        if val >= 0 && val <= 65535 {
            self.emit(&format!("\tmov\t{}, #{}", reg, val));
        } else if val >= -65535 && val < 0 {
            self.emit(&format!("\tmov\t{}, #{}", reg, val));
        } else {
            // Use movz + movk for larger values
            let lo = (val as u64) & 0xFFFF;
            let hi = ((val as u64) >> 16) & 0xFFFF;
            let hi2 = ((val as u64) >> 32) & 0xFFFF;
            let hi3 = ((val as u64) >> 48) & 0xFFFF;
            self.emit(&format!("\tmovz\t{}, #{}", reg, lo));
            if hi != 0 {
                self.emit(&format!("\tmovk\t{}, #{}, lsl #16", reg, hi));
            }
            if hi2 != 0 {
                self.emit(&format!("\tmovk\t{}, #{}, lsl #32", reg, hi2));
            }
            if hi3 != 0 {
                self.emit(&format!("\tmovk\t{}, #{}, lsl #48", reg, hi3));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Free variable collection helper
// ---------------------------------------------------------------------------

fn collect_free_vars(
    expr: &ast::Expr,
    bound: &std::collections::HashSet<String>,
    ctx: &FnCtx,
    free: &mut Vec<String>,
) {
    match expr {
        ast::Expr::Var(n) => {
            if !bound.contains(n) && ctx.has_var(n) && !free.contains(n) {
                free.push(n.clone());
            }
        }
        ast::Expr::App(f, a) => {
            collect_free_vars(f, bound, ctx, free);
            collect_free_vars(a, bound, ctx, free);
        }
        ast::Expr::Lam(binders, body) => {
            let mut new_bound = bound.clone();
            for b in binders {
                if let ast::Binder::Var(v) = b { new_bound.insert(v.clone()); }
            }
            collect_free_vars(body, &new_bound, ctx, free);
        }
        ast::Expr::BinOp(l, _, r) => {
            collect_free_vars(l, bound, ctx, free);
            collect_free_vars(r, bound, ctx, free);
        }
        ast::Expr::If(c, t, e) => {
            collect_free_vars(c, bound, ctx, free);
            collect_free_vars(t, bound, ctx, free);
            collect_free_vars(e, bound, ctx, free);
        }
        ast::Expr::Let(decls, body) => {
            let mut new_bound = bound.clone();
            for d in decls {
                match d {
                    ast::Decl::Value(n, _, rhs, _) => {
                        collect_free_vars(rhs, &new_bound, ctx, free);
                        new_bound.insert(n.clone());
                    }
                    ast::Decl::PatBind(ast::Binder::Var(n), rhs, _) => {
                        collect_free_vars(rhs, &new_bound, ctx, free);
                        new_bound.insert(n.clone());
                    }
                    _ => {}
                }
            }
            collect_free_vars(body, &new_bound, ctx, free);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Function context (stack frame layout)
// ---------------------------------------------------------------------------

struct FnCtx {
    /// name → slot index (0-based, each slot = 8 bytes, offset from fp = slot*8+16)
    locals: HashMap<String, usize>,
    /// next available slot
    next_slot: usize,
    /// temp stack (for saving intermediate values)
    temp_stack: Vec<usize>,
}

impl FnCtx {
    fn new(n_args: usize) -> Self {
        let mut ctx = Self {
            locals: HashMap::new(),
            next_slot: 0,
            temp_stack: Vec::new(),
        };
        // Reserve n_args slots even if not yet named (args stored by emit_function)
        ctx.next_slot = n_args.max(0);
        ctx
    }

    fn alloc_local(&mut self, name: String) -> usize {
        let s = self.next_slot;
        self.locals.insert(name, s);
        self.next_slot += 1;
        s
    }

    fn alloc_temp(&mut self) -> usize {
        let s = self.next_slot;
        self.temp_stack.push(s);
        self.next_slot += 1;
        s
    }

    fn free_temp(&mut self) {
        if let Some(_s) = self.temp_stack.pop() {
            // We don't reuse slots for simplicity (conservative)
        }
    }

    fn lookup(&self, name: &str) -> Option<usize> {
        self.locals.get(name).copied()
    }

    fn has_var(&self, name: &str) -> bool {
        self.locals.contains_key(name)
    }

    /// Frame size in bytes (multiple of 16, space for locals)
    fn frame_size(&self) -> usize {
        let slots = self.next_slot.max(8); // at least 8 slots
        // round up to 16-byte alignment: each slot 8 bytes
        let raw = slots * 8;
        (raw + 15) & !15
    }
}

// ---------------------------------------------------------------------------
// Register helpers
// ---------------------------------------------------------------------------

fn arg_reg(i: usize) -> &'static str {
    match i {
        0 => "x0", 1 => "x1", 2 => "x2", 3 => "x3",
        4 => "x4", 5 => "x5", 6 => "x6", 7 => "x7",
        _ => "x8", // spill not supported yet
    }
}

// ---------------------------------------------------------------------------
// IR-based emit path:  AST → ir::Instr (3-addr) → liveness → linear-scan RA → ARM64
// ---------------------------------------------------------------------------

use crate::ir::{self, VReg, Label as IrLabel};
use crate::regalloc::{self, Location};

// ---- IR builder -----------------------------------------------------------

struct IrBuilder {
    instrs: Vec<ir::Instr>,
    vars: HashMap<String, VReg>,
    next_vreg: u32,
    next_label: u32,
    module_name: String,
    rodata: Vec<(String, String)>, // (label, content)
    string_cache: HashMap<String, String>,
}

impl IrBuilder {
    fn new(module_name: String, next_label: u32) -> Self {
        Self {
            instrs: Vec::new(),
            vars: HashMap::new(),
            next_vreg: 0,
            next_label,
            module_name,
            rodata: Vec::new(),
            string_cache: HashMap::new(),
        }
    }

    fn fresh(&mut self) -> VReg {
        let v = VReg(self.next_vreg);
        self.next_vreg += 1;
        v
    }

    fn fresh_label(&mut self) -> IrLabel {
        let l = IrLabel(self.next_label);
        self.next_label += 1;
        l
    }

    fn mangle(&self, name: &str) -> String {
        format!("_Phi_{}_{}", self.module_name.replace('.', "_"), name.replace('.', "_"))
    }

    fn intern_string(&mut self, s: &str) -> String {
        if let Some(lbl) = self.string_cache.get(s) {
            return lbl.clone();
        }
        let lbl = format!("LStr_{}", self.next_label);
        self.next_label += 1;
        self.rodata.push((lbl.clone(), s.to_string()));
        self.string_cache.insert(s.to_string(), lbl.clone());
        lbl
    }

    fn push(&mut self, i: ir::Instr) { self.instrs.push(i); }

    /// Lower an expression; return the VReg that holds the result.
    fn lower(&mut self, expr: &ast::Expr) -> VReg {
        match expr {
            ast::Expr::Number(n) => {
                let v = self.fresh();
                self.push(ir::Instr::Int(v, *n));
                v
            }
            ast::Expr::Unit => {
                let v = self.fresh();
                self.push(ir::Instr::Nil(v));
                v
            }
            ast::Expr::Char(c) => {
                let v = self.fresh();
                self.push(ir::Instr::Int(v, *c as i64));
                v
            }
            ast::Expr::Var(name) => {
                match name.as_str() {
                    "true"  => { let v = self.fresh(); self.push(ir::Instr::Int(v, 1)); v }
                    "false" => { let v = self.fresh(); self.push(ir::Instr::Nil(v)); v }
                    _ => {
                        if let Some(&sv) = self.vars.get(name) {
                            sv // reuse existing VReg directly — no copy needed
                        } else {
                            let v = self.fresh();
                            self.push(ir::Instr::Global(v, self.mangle(name)));
                            v
                        }
                    }
                }
            }
            ast::Expr::TypeAnn(inner, _) => self.lower(inner),
            ast::Expr::Paren(inner) => self.lower(inner),
            ast::Expr::Negate(e) => {
                let s = self.lower(e);
                let v = self.fresh();
                self.push(ir::Instr::Neg(v, s));
                v
            }
            ast::Expr::BinOp(lhs, op, rhs) => self.lower_binop(lhs, op, rhs),
            ast::Expr::If(cond, then_e, else_e) => self.lower_if(cond, then_e, else_e),
            ast::Expr::Let(decls, body) => self.lower_let(decls, body),
            ast::Expr::App(..) => self.lower_app_chain(expr),
            ast::Expr::String(s) => {
                let lbl = self.intern_string(s);
                let v = self.fresh();
                self.push(ir::Instr::Global(v, lbl));
                v
            }
            ast::Expr::Atom(a) => {
                let lbl = self.intern_string(a);
                let v = self.fresh();
                self.push(ir::Instr::Global(v, lbl));
                v
            }
            ast::Expr::Tuple(elems) => self.lower_tuple(elems),
            ast::Expr::List(elems, tail) => self.lower_list(elems, tail.as_deref()),
            ast::Expr::Case(scrutinees, branches) => self.lower_case(scrutinees, branches),
            _ => {
                // Unimplemented: return nil
                let v = self.fresh();
                self.push(ir::Instr::Nil(v));
                v
            }
        }
    }

    fn lower_binop(&mut self, lhs: &ast::Expr, op: &str, rhs: &ast::Expr) -> VReg {
        let l = self.lower(lhs);
        let r = self.lower(rhs);
        let v = self.fresh();
        let cond = match op {
            "+"  => { self.push(ir::Instr::Add(v, l, r)); return v; }
            "-"  => { self.push(ir::Instr::Sub(v, l, r)); return v; }
            "*"  => { self.push(ir::Instr::Mul(v, l, r)); return v; }
            "/"  => { self.push(ir::Instr::Div(v, l, r)); return v; }
            "&&" => { self.push(ir::Instr::And(v, l, r)); return v; }
            "||" => { self.push(ir::Instr::Or(v, l, r));  return v; }
            "==" => ir::Cond::Eq,
            "/=" => ir::Cond::Ne,
            "<"  => ir::Cond::Lt,
            "<=" => ir::Cond::Le,
            ">"  => ir::Cond::Gt,
            ">=" => ir::Cond::Ge,
            _    => { self.push(ir::Instr::Nil(v)); return v; }
        };
        self.push(ir::Instr::Cmp(v, l, cond, r));
        v
    }

    fn lower_if(&mut self, cond: &ast::Expr, then_e: &ast::Expr, else_e: &ast::Expr) -> VReg {
        let c = self.lower(cond);
        let else_lbl = self.fresh_label();
        let end_lbl  = self.fresh_label();
        // branch if false (c == 1)
        self.push(ir::Instr::BranchFalse(c, else_lbl));
        let t = self.lower(then_e);
        // result VReg for then branch
        let res = self.fresh();
        self.push(ir::Instr::Mov(res, t));
        self.push(ir::Instr::Jump(end_lbl));
        self.push(ir::Instr::Label(else_lbl));
        let e = self.lower(else_e);
        self.push(ir::Instr::Mov(res, e));
        self.push(ir::Instr::Label(end_lbl));
        res
    }

    fn lower_let(&mut self, decls: &[ast::Decl], body: &ast::Expr) -> VReg {
        for decl in decls {
            match decl {
                ast::Decl::Value(name, binders, rhs, _) if binders.is_empty() => {
                    let v = self.lower(rhs);
                    self.vars.insert(name.clone(), v);
                }
                ast::Decl::PatBind(ast::Binder::Var(name), rhs, _) => {
                    let v = self.lower(rhs);
                    self.vars.insert(name.clone(), v);
                }
                _ => {}
            }
        }
        self.lower(body)
    }

    fn lower_app_chain(&mut self, expr: &ast::Expr) -> VReg {
        // Flatten  f a0 a1 ... aN  into (func, [a0..aN])
        let mut args: Vec<&ast::Expr> = Vec::new();
        let mut cur = expr;
        while let ast::Expr::App(f, a) = cur { args.push(a); cur = f; }
        args.reverse();

        let n = args.len() as u8;

        // Evaluate args → VRegs
        let arg_vregs: Vec<VReg> = args.iter().map(|a| self.lower(a)).collect();

        // Emit SetArg
        for (i, &av) in arg_vregs.iter().enumerate() {
            self.push(ir::Instr::SetArg(i as u8, av));
        }

        let dst = self.fresh();

        // Direct static call if func is a known global name
        if let ast::Expr::Var(name) = cur {
            if !self.vars.contains_key(name.as_str()) {
                let label = self.mangle(name);
                self.push(ir::Instr::CallDirect(dst, label, n));
                return dst;
            }
        }

        // Dynamic: load func VReg and call through closure
        let f = self.lower(cur);
        self.push(ir::Instr::CallFun(dst, f, n));
        dst
    }

    fn lower_tuple(&mut self, elems: &[ast::Expr]) -> VReg {
        let n_words = (elems.len() + 1) as i64; // +1 for length word
        let nw = self.fresh();
        self.push(ir::Instr::Int(nw, n_words - 1)); // store element count (untagged)
        // Call phi_alloc(n_words)
        let cnt = self.fresh();
        self.push(ir::Instr::Int(cnt, n_words));
        self.push(ir::Instr::SetArg(0, cnt));
        let ptr = self.fresh();
        self.push(ir::Instr::CallDirect(ptr, "_phi_alloc".to_string(), 1));
        // Store element count at [ptr+0]
        self.push(ir::Instr::Store(ptr, 0, nw));
        // Store elements
        for (i, elem) in elems.iter().enumerate() {
            let ev = self.lower(elem);
            self.push(ir::Instr::Store(ptr, (i as i32 + 1) * 8, ev));
        }
        ptr
    }

    fn lower_list(&mut self, elems: &[ast::Expr], tail: Option<&ast::Expr>) -> VReg {
        let mut cur = if let Some(t) = tail { self.lower(t) } else {
            let v = self.fresh(); self.push(ir::Instr::Nil(v)); v
        };
        for elem in elems.iter().rev() {
            let hd = self.lower(elem);
            // alloc 2-word cons cell
            let n2 = self.fresh(); self.push(ir::Instr::Int(n2, 2));
            self.push(ir::Instr::SetArg(0, n2));
            let cell = self.fresh();
            self.push(ir::Instr::CallDirect(cell, "_phi_alloc".to_string(), 1));
            self.push(ir::Instr::Store(cell, 0, hd));
            self.push(ir::Instr::Store(cell, 8, cur));
            cur = cell;
        }
        cur
    }

    fn lower_case(&mut self, scrutinees: &[ast::Expr], branches: &[ast::CaseBranch]) -> VReg {
        if scrutinees.len() != 1 || branches.is_empty() {
            let v = self.fresh(); self.push(ir::Instr::Nil(v)); return v;
        }
        let scr = self.lower(&scrutinees[0]);
        let end_lbl = self.fresh_label();
        let res = self.fresh(); self.push(ir::Instr::Nil(res)); // default

        for branch in branches {
            let next_lbl = self.fresh_label();
            if branch.binders.len() == 1 {
                // Emit pattern test; jump to next_lbl on failure
                match &branch.binders[0] {
                    ast::Binder::Wildcard => {}
                    ast::Binder::Number(n) => {
                        let tagged = (*n << 1) | 1;
                        self.push(ir::Instr::BranchNe(scr, tagged, next_lbl));
                    }
                    ast::Binder::Var(name) => {
                        self.vars.insert(name.clone(), scr);
                    }
                    _ => {} // complex: fall through
                }
            }
            let body_v = self.lower(&branch.body);
            self.push(ir::Instr::Mov(res, body_v));
            self.push(ir::Instr::Jump(end_lbl));
            self.push(ir::Instr::Label(next_lbl));
        }
        self.push(ir::Instr::Label(end_lbl));
        res
    }

    fn build_fun(mut self, name: String, params: Vec<VReg>) -> (ir::IrFun, Vec<(String,String)>, u32) {
        let result = match self.instrs.last() {
            Some(ir::Instr::Ret(_)) => { let _ = self.instrs.pop(); self.instrs.pop().map(|_| ()).is_none(); self.instrs.last().cloned() }
            _ => self.instrs.last().cloned(),
        };
        // Find last non-label instr to determine result VReg
        let ret_v = self.instrs.iter().rev()
            .find_map(|i| match i {
                ir::Instr::Int(v,_) | ir::Instr::Nil(v) | ir::Instr::Global(v,_)
                | ir::Instr::Mov(v,_) | ir::Instr::Add(v,_,_) | ir::Instr::Sub(v,_,_)
                | ir::Instr::Mul(v,_,_) | ir::Instr::Div(v,_,_) | ir::Instr::Neg(v,_)
                | ir::Instr::And(v,_,_) | ir::Instr::Or(v,_,_) | ir::Instr::Cmp(v,_,_,_)
                | ir::Instr::Load(v,_,_) | ir::Instr::CallDirect(v,_,_) | ir::Instr::CallFun(v,_,_)
                    => Some(*v),
                _ => None,
            })
            .unwrap_or(VReg(0));
        let _ = result;
        self.instrs.push(ir::Instr::Ret(ret_v));

        let vreg_count = self.next_vreg;
        let next_label = self.next_label;
        let fun = ir::IrFun { name, arity: params.len() as u32, params, body: self.instrs, vreg_count };
        (fun, self.rodata, next_label)
    }
}

// ---- ARM64 emission from allocated IR -------------------------------------

/// Frame offset for a spill slot (byte offset from x29).
const SPILL_BASE: i32 = 16; // right after saved x29/x30

fn spill_off(slot: u32) -> i32 { SPILL_BASE + slot as i32 * 8 }

/// Resolve a VReg to either a named physical register or a scratch + load instruction.
/// Returns (reg_name_to_use, Option<load_instruction_to_prepend>).
/// scratch = "x16" or "x17"
fn resolve_use(v: VReg, alloc: &regalloc::Allocation, scratch: &'static str) -> (String, Option<String>) {
    match alloc.get(v) {
        Location::Reg(p) => (p.name().to_string(), None),
        Location::Slot(s) => (
            scratch.to_string(),
            Some(format!("\tldr\t{}, [x29, #{}]", scratch, spill_off(s))),
        ),
    }
}

/// After a definition, store to spill slot if needed.
fn resolve_def_store(v: VReg, alloc: &regalloc::Allocation, result_reg: &str) -> Option<String> {
    match alloc.get(v) {
        Location::Reg(p) => {
            if p.name() != result_reg {
                Some(format!("\tmov\t{}, {}", p.name(), result_reg))
            } else { None }
        }
        Location::Slot(s) => Some(format!("\tstr\t{}, [x29, #{}]", result_reg, spill_off(s))),
    }
}

/// The register a definition ends up in before any store.
fn def_reg(v: VReg, alloc: &regalloc::Allocation) -> String {
    match alloc.get(v) {
        Location::Reg(p) => p.name().to_string(),
        Location::Slot(_) => "x16".to_string(), // compute into x16, then store
    }
}

fn emit_ir_fn(
    fun: &ir::IrFun,
    alloc: &regalloc::Allocation,
    spill_slots: u32,
    fn_label: &str,
    out: &mut String,
) {
    let frame_total = {
        let raw = 16 + spill_slots as usize * 8;
        ((raw + 15) & !15) as i32
    };

    // Prologue
    out.push_str(&format!("\t.globl\t{}\n{}:\n", fn_label, fn_label));
    out.push_str(&format!("\tsub\tsp, sp, #{}\n", frame_total));
    out.push_str("\tstp\tx29, x30, [sp]\n");
    out.push_str("\tadd\tx29, sp, #0\n");

    // Copy params from x0..xN into their allocated locations
    for (i, &p) in fun.params.iter().enumerate() {
        let arg = arg_reg(i);
        match alloc.get(p) {
            Location::Reg(pr) => {
                if pr.name() != arg {
                    out.push_str(&format!("\tmov\t{}, {}\n", pr.name(), arg));
                }
            }
            Location::Slot(s) => {
                out.push_str(&format!("\tstr\t{}, [x29, #{}]\n", arg, spill_off(s)));
            }
        }
    }

    macro_rules! line { ($s:expr) => { out.push_str(&$s); out.push('\n'); } }
    macro_rules! emit { ($fmt:literal $($args:tt)*) => { line!(format!($fmt $($args)*)) } }

    for instr in &fun.body {
        use ir::Instr::*;
        match instr {
            ir::Instr::Int(d, n) => {
                let dr = def_reg(*d, alloc);
                let tagged = ((*n as i64) << 1) | 1;
                emit_load_imm_to(out, &dr, tagged);
                if let Some(s) = resolve_def_store(*d, alloc, &dr) { line!(s); }
            }
            ir::Instr::Nil(d) => {
                let dr = def_reg(*d, alloc);
                emit!("\tmov\t{}, #1", dr);
                if let Some(s) = resolve_def_store(*d, alloc, &dr) { line!(s); }
            }
            ir::Instr::Global(d, lbl) => {
                let dr = def_reg(*d, alloc);
                emit!("\tadrp\t{}, {}@PAGE", dr, lbl);
                emit!("\tadd\t{}, {}, {}@PAGEOFF", dr, dr, lbl);
                if let Some(s) = resolve_def_store(*d, alloc, &dr) { line!(s); }
            }
            ir::Instr::Mov(d, s) => {
                let (sr, ld) = resolve_use(*s, alloc, "x16");
                if let Some(l) = ld { line!(l); }
                let dr = def_reg(*d, alloc);
                if dr != sr { emit!("\tmov\t{}, {}", dr, sr); }
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::Add(d, l, r) | ir::Instr::Sub(d, l, r)
            | ir::Instr::Mul(d, l, r) | ir::Instr::Div(d, l, r) => {
                let (lr, ld) = resolve_use(*l, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                let (rr, rd) = resolve_use(*r, alloc, "x17");
                if let Some(x) = rd { line!(x); }
                let dr = def_reg(*d, alloc);
                // untag
                emit!("\tasr\t{}, {}, #1", "x16", lr);
                emit!("\tasr\t{}, {}, #1", "x17", rr);
                let op = match instr {
                    ir::Instr::Add(..) => "add", ir::Instr::Sub(..) => "sub",
                    ir::Instr::Mul(..) => "mul", ir::Instr::Div(..) => "sdiv", _ => "add",
                };
                emit!("\t{}\t{}, x16, x17", op, dr);
                // retag
                emit!("\tlsl\t{}, {}, #1", dr, dr);
                emit!("\torr\t{}, {}, #1", dr, dr);
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::And(d, l, r) | ir::Instr::Or(d, l, r) => {
                let (lr, ld) = resolve_use(*l, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                let (rr, rd2) = resolve_use(*r, alloc, "x17");
                if let Some(x) = rd2 { line!(x); }
                let dr = def_reg(*d, alloc);
                let op = if matches!(instr, ir::Instr::And(..)) { "and" } else { "orr" };
                emit!("\t{}\t{}, {}, {}", op, dr, lr, rr);
                if matches!(instr, ir::Instr::Or(..)) {
                    emit!("\torr\t{}, {}, #1", dr, dr); // ensure tag bit
                }
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::Neg(d, s) => {
                let (sr, ld) = resolve_use(*s, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                let dr = def_reg(*d, alloc);
                emit!("\tasr\t{}, {}, #1", dr, sr);
                emit!("\tneg\t{}, {}", dr, dr);
                emit!("\tlsl\t{}, {}, #1", dr, dr);
                emit!("\torr\t{}, {}, #1", dr, dr);
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::Cmp(d, l, cond, r) => {
                let (lr, ld) = resolve_use(*l, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                let (rr, rd2) = resolve_use(*r, alloc, "x17");
                if let Some(x) = rd2 { line!(x); }
                let needs_untag = !matches!(cond, ir::Cond::Eq | ir::Cond::Ne);
                if needs_untag {
                    emit!("\tasr\tx16, {}, #1", lr);
                    emit!("\tasr\tx17, {}, #1", rr);
                    emit!("\tcmp\tx16, x17");
                } else {
                    emit!("\tcmp\t{}, {}", lr, rr);
                }
                let dr = def_reg(*d, alloc);
                emit!("\tcset\t{}, {}", dr, cond.arm_suffix());
                // encode bool: 0→1 (false), 1→3 (true)
                emit!("\tlsl\t{}, {}, #1", dr, dr);
                emit!("\torr\t{}, {}, #1", dr, dr);
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::Load(d, base, off) => {
                let (br, ld) = resolve_use(*base, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                let dr = def_reg(*d, alloc);
                emit!("\tldr\t{}, [{}, #{}]", dr, br, off);
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::Store(base, off, src) => {
                let (br, ld) = resolve_use(*base, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                let (sr, ls) = resolve_use(*src, alloc, "x17");
                if let Some(x) = ls { line!(x); }
                emit!("\tstr\t{}, [{}, #{}]", sr, br, off);
            }
            ir::Instr::SetArg(i, v) => {
                let (vr, ld) = resolve_use(*v, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                let ar = arg_reg(*i as usize);
                if vr != ar { emit!("\tmov\t{}, {}", ar, vr); }
            }
            ir::Instr::CallDirect(d, lbl, _n) => {
                emit!("\tbl\t{}", lbl);
                // result in x0; move to allocated reg
                let dr = def_reg(*d, alloc);
                if dr != "x0" { emit!("\tmov\t{}, x0", dr); }
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::CallFun(d, f, _n) => {
                let (fr, ld) = resolve_use(*f, alloc, "x8");
                if let Some(x) = ld { line!(x); }
                // fn ptr is at closure[1]
                emit!("\tldr\tx9, [{}, #8]", fr);
                emit!("\tblr\tx9");
                let dr = def_reg(*d, alloc);
                if dr != "x0" { emit!("\tmov\t{}, x0", dr); }
                if let Some(st) = resolve_def_store(*d, alloc, &dr) { line!(st); }
            }
            ir::Instr::Label(lbl) => { emit!("{}:", lbl); }
            ir::Instr::Jump(lbl)  => { emit!("\tb\t{}", lbl); }
            ir::Instr::BranchFalse(v, lbl) => {
                let (vr, ld) = resolve_use(*v, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                emit!("\tcmp\t{}, #1", vr); // false = 1
                emit!("\tb.eq\t{}", lbl);
            }
            ir::Instr::BranchTrue(v, lbl) => {
                let (vr, ld) = resolve_use(*v, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                emit!("\tcmp\t{}, #3", vr); // true = 3
                emit!("\tb.eq\t{}", lbl);
            }
            ir::Instr::BranchEq(v, imm, lbl) => {
                let (vr, ld) = resolve_use(*v, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                emit_load_imm_to(out, "x17", *imm);
                emit!("\tcmp\t{}, x17", vr);
                emit!("\tb.eq\t{}", lbl);
            }
            ir::Instr::BranchNe(v, imm, lbl) => {
                let (vr, ld) = resolve_use(*v, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                emit_load_imm_to(out, "x17", *imm);
                emit!("\tcmp\t{}, x17", vr);
                emit!("\tb.ne\t{}", lbl);
            }
            ir::Instr::Ret(v) => {
                let (vr, ld) = resolve_use(*v, alloc, "x16");
                if let Some(x) = ld { line!(x); }
                if vr != "x0" { emit!("\tmov\tx0, {}", vr); }
                emit!("\tldp\tx29, x30, [sp]");
                emit!("\tadd\tsp, sp, #{}", frame_total);
                emit!("\tret");
            }
        }
    }
    out.push('\n');
}

fn emit_load_imm_to(out: &mut String, reg: &str, val: i64) {
    if val >= 0 && val <= 65535 {
        out.push_str(&format!("\tmov\t{}, #{}\n", reg, val));
    } else if val < 0 && val >= -65535 {
        out.push_str(&format!("\tmov\t{}, #{}\n", reg, val));
    } else {
        let lo = (val as u64) & 0xFFFF;
        let h1 = ((val as u64) >> 16) & 0xFFFF;
        let h2 = ((val as u64) >> 32) & 0xFFFF;
        let h3 = ((val as u64) >> 48) & 0xFFFF;
        out.push_str(&format!("\tmovz\t{}, #{}\n", reg, lo));
        if h1 != 0 { out.push_str(&format!("\tmovk\t{}, #{}, lsl #16\n", reg, h1)); }
        if h2 != 0 { out.push_str(&format!("\tmovk\t{}, #{}, lsl #32\n", reg, h2)); }
        if h3 != 0 { out.push_str(&format!("\tmovk\t{}, #{}, lsl #48\n", reg, h3)); }
    }
}

// ---------------------------------------------------------------------------
// Runtime support (emitted once per binary, linked separately)
// ---------------------------------------------------------------------------

/// Emit the runtime support file: bump allocator + basic I/O.
pub fn emit_runtime() -> String {
    r#"// Phi AArch64 runtime support
// Assemble: clang -arch arm64 -c phi_runtime.s -o phi_runtime.o

    .section __TEXT,__text,regular,pure_instructions
    .p2align 2

// phi_alloc(n_words: x0) -> heap_ptr: x0
// Simple bump allocator backed by mmap. NOT thread-safe, no GC.
    .globl _phi_alloc
_phi_alloc:
    stp     x29, x30, [sp, #-32]!
    mov     x29, sp
    str     x19, [sp, #16]

    mov     x19, x0               // save n_words

    // Load heap_top from global
    adrp    x1, _phi_heap_top@PAGE
    add     x1, x1, _phi_heap_top@PAGEOFF
    ldr     x0, [x1]              // current top

    // If zero, initialize heap
    cbnz    x0, Lalloc_have_heap
    // mmap(NULL, 64MB, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANON, -1, 0)
    mov     x0, #0                // addr = NULL
    mov     x1, #0x4000000        // 64 MB
    mov     x2, #3                // PROT_READ|PROT_WRITE
    mov     x3, #0x1002           // MAP_PRIVATE|MAP_ANONYMOUS
    mov     x4, #-1               // fd = -1
    mov     x5, #0                // offset = 0
    mov     x16, #197             // SYS_mmap
    svc     #0x80
    // x0 = heap base; save as heap_base and heap_top
    adrp    x1, _phi_heap_base@PAGE
    add     x1, x1, _phi_heap_base@PAGEOFF
    str     x0, [x1]
    adrp    x1, _phi_heap_top@PAGE
    add     x1, x1, _phi_heap_top@PAGEOFF
    str     x0, [x1]

Lalloc_have_heap:
    // result = heap_top
    adrp    x1, _phi_heap_top@PAGE
    add     x1, x1, _phi_heap_top@PAGEOFF
    ldr     x0, [x1]
    // bump: heap_top += n_words * 8
    lsl     x2, x19, #3
    add     x2, x0, x2
    str     x2, [x1]

    ldr     x19, [sp, #16]
    ldp     x29, x30, [sp], #32
    ret

// phi_print_int(n: x0)   — prints untagged integer + newline
    .globl _phi_print_int
_phi_print_int:
    stp     x29, x30, [sp, #-48]!
    mov     x29, sp
    // x0 is already the integer value (untagged by caller)
    // convert to decimal string in buffer [sp+16..sp+40]
    add     x1, sp, #16
    mov     x2, #24
    bl      _phi_itoa
    // write(1, buf, len)
    add     x1, sp, #16
    mov     x0, #1
    mov     x2, x0              // length returned in x0 from itoa
    mov     x16, #4             // SYS_write
    svc     #0x80
    ldp     x29, x30, [sp], #48
    ret

// phi_itoa(n: x0, buf: x1, buflen: x2) -> len: x0
    .globl _phi_itoa
_phi_itoa:
    stp     x29, x30, [sp, #-64]!
    mov     x29, sp
    str     x19, [sp, #16]
    str     x20, [sp, #24]
    str     x21, [sp, #32]
    mov     x19, x0             // n
    mov     x20, x1             // buf
    mov     x21, x2             // buflen

    // handle negative
    mov     x3, #0              // neg flag
    cmp     x19, #0
    b.ge    Litoa_pos
    mov     x3, #1
    neg     x19, x19
    strb    w3, [x20], #1       // store '-'
    mov     x3, #45
    sub     x20, x20, #1
    strb    w3, [x20], #1
Litoa_pos:
    // write digits in reverse
    add     x4, x20, #23        // end of buffer
    mov     x5, x4              // ptr
    mov     x6, #0              // digit count
Litoa_loop:
    mov     x7, #10
    udiv    x8, x19, x7
    msub    x9, x8, x7, x19     // digit = n % 10
    add     x9, x9, #48         // '0'
    strb    w9, [x5, #-1]!
    mov     x19, x8
    add     x6, x6, #1
    cbnz    x19, Litoa_loop
    // copy reversed digits to buf
    mov     x7, #0
Litoa_copy:
    cmp     x7, x6
    b.ge    Litoa_done
    ldrb    w8, [x5], #1
    strb    w8, [x20, x7]
    add     x7, x7, #1
    b       Litoa_copy
Litoa_done:
    // append newline
    add     x8, x20, x6
    mov     x9, #10
    strb    w9, [x8]
    add     x0, x6, #1

    ldr     x19, [sp, #16]
    ldr     x20, [sp, #24]
    ldr     x21, [sp, #32]
    ldp     x29, x30, [sp], #64
    ret

    .section __DATA,__data
    .p2align 3
_phi_heap_base:
    .quad   0
_phi_heap_top:
    .quad   0
"#.to_string()
}

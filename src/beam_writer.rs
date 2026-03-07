#![allow(dead_code)]
//! Pure Rust BEAM binary file generator.
//!
//! Writes `.beam` files directly in the BEAM/IFF chunked format.
//! No ETF library, no Erlang calls, no temporary `.erl` text files.
//!
//! Reference:
//!   https://www.erlang.org/doc/apps/erts/beam_file_format.html
//!   lib/compiler/src/beam_asm.erl  (OTP source)
//!
//! ## BEAM file layout
//! ```text
//! "FOR1" ++ u32be(total_bytes - 8) ++ "BEAM"
//!   ++ chunk("AtU8", atoms_data)
//!   ++ chunk("Code", code_data)
//!   ++ chunk("StrT", strings_data)
//!   ++ chunk("ImpT", imports_data)
//!   ++ chunk("ExpT", exports_data)
//!   ++ chunk("LocT", locals_data)
//!   ++ chunk("FunT", lambdas_data)
//! ```
//!
//! ## Compact term encoding (arguments in Code chunk)
//! Tags (3 bits):
//!   0=u(unsigned literal)  1=i(integer)  2=a(atom index)
//!   3=x(X register)        4=y(Y register)  5=f(label/fail)
//!
//! Values 0..15:    1 byte  `(value << 4) | tag`
//! Values 16..2047: 2 bytes `((value>>3 & !7) | tag | 8), (value & 0xFF)`

use crate::ast;

#[derive(Clone, Debug)]
pub enum BeamGenError {
    Unsupported(&'static str),
    Internal(&'static str),
}

fn mono_arity(ty: &crate::type_sys::MonoType) -> u32 {
    use crate::type_sys::MonoType;
    // Arrow is encoded as App(App(Con("->"), domain), codomain)
    match ty {
        MonoType::App(f, codom) => {
            if let MonoType::App(inner_f, _dom) = &**f {
                if let MonoType::Con(n) = &**inner_f {
                    if n == "->" {
                        return 1 + mono_arity(codom);
                    }
                }
            }
            0
        }
        MonoType::Constrained(_c, _args, inner) => mono_arity(inner),
        _ => 0,
    }
}

fn desugar_comprehension(body: &ast::Expr, stmts: &[ast::CompStmt]) -> ast::Expr {
    fn go(curr: ast::Expr, stmts: &[ast::CompStmt]) -> ast::Expr {
        match stmts.split_last() {
            None => curr,
            Some((last, prefix)) => {
                let next = match last {
                    ast::CompStmt::Bind(binder, expr) => {
                        // expr >>= \binder -> curr
                        ast::Expr::App(
                            Box::new(ast::Expr::App(
                                Box::new(ast::Expr::Var(">>=".to_string())),
                                Box::new(expr.clone()),
                            )),
                            Box::new(ast::Expr::Lam(vec![binder.clone()], Box::new(curr))),
                        )
                    }
                    ast::CompStmt::Guard(expr) => {
                        // guard expr >>= \_ -> curr
                        let guard_call = ast::Expr::App(
                            Box::new(ast::Expr::Var("guard".to_string())),
                            Box::new(expr.clone()),
                        );
                        ast::Expr::App(
                            Box::new(ast::Expr::App(
                                Box::new(ast::Expr::Var(">>=".to_string())),
                                Box::new(guard_call),
                            )),
                            Box::new(ast::Expr::Lam(vec![ast::Binder::Wildcard], Box::new(curr))),
                        )
                    }
                    ast::CompStmt::Let(decls) => ast::Expr::Let(decls.clone(), Box::new(curr)),
                };
                go(next, prefix)
            }
        }
    }

    go(body.clone(), stmts)
}

fn desugar_do(stmts: &[ast::DoStatement]) -> ast::Expr {
    fn go(stmts: &[ast::DoStatement]) -> ast::Expr {
        match stmts.split_first() {
            None => ast::Expr::Unit,
            Some((first, rest)) => match first {
                ast::DoStatement::Expr(e) => {
                    if rest.is_empty() {
                        e.clone()
                    } else {
                        ast::Expr::App(
                            Box::new(ast::Expr::App(
                                Box::new(ast::Expr::Var(">>=".to_string())),
                                Box::new(e.clone()),
                            )),
                            Box::new(ast::Expr::Lam(
                                vec![ast::Binder::Wildcard],
                                Box::new(go(rest)),
                            )),
                        )
                    }
                }
                ast::DoStatement::Bind(binder, e) => {
                    ast::Expr::App(
                        Box::new(ast::Expr::App(
                            Box::new(ast::Expr::Var(">>=".to_string())),
                            Box::new(e.clone()),
                        )),
                        Box::new(ast::Expr::Lam(vec![binder.clone()], Box::new(go(rest)))),
                    )
                }
                ast::DoStatement::Let(decls) => {
                    // do { let decls; rest }  ==>  let decls in do {rest}
                    ast::Expr::Let(decls.clone(), Box::new(go(rest)))
                }
            },
        }
    }

    go(stmts)
}

fn desugar_receive(branches: &[ast::CaseBranch], after: &Option<Box<ast::AfterClause>>) -> ast::Expr {
    // Lower:
    //   receive { p1 -> e1; p2 -> e2; ... } after t -> et
    // to:
    //   Runtime.Receive.receiveWith (\msg -> case msg of
    //       p1 -> {ok, e1}
    //       p2 -> {ok, e2}
    //       _  -> nomatch)
    //     t
    //     (\() -> et)
    let msg_var = ast::Expr::Var("msg".to_string());

    let mut case_branches: Vec<ast::CaseBranch> = branches
        .iter()
        .map(|b| ast::CaseBranch {
            binders: b.binders.clone(),
            guards: b.guards.clone(),
            body: ast::Expr::Tuple(vec![ast::Expr::Atom("ok".to_string()), b.body.clone()]),
        })
        .collect();

    case_branches.push(ast::CaseBranch {
        binders: vec![ast::Binder::Wildcard],
        guards: vec![],
        body: ast::Expr::Atom("nomatch".to_string()),
    });

    let matcher = ast::Expr::Lam(
        vec![ast::Binder::Var("msg".to_string())],
        Box::new(ast::Expr::Case(vec![msg_var], case_branches)),
    );

    let (timeout_expr, timeout_fun) = if let Some(a) = after {
        (
            (*a.timeout).clone(),
            ast::Expr::Lam(vec![], Box::new(a.body.clone())),
        )
    } else {
        (
            ast::Expr::Number(-1),
            ast::Expr::Lam(vec![], Box::new(ast::Expr::Unit)),
        )
    };

    ast::Expr::App(
        Box::new(ast::Expr::App(
            Box::new(ast::Expr::App(
                Box::new(ast::Expr::Var("Runtime.Receive.receiveWith".to_string())),
                Box::new(matcher),
            )),
            Box::new(timeout_expr),
        )),
        Box::new(timeout_fun),
    )
}

// ─── Compact term tag constants ──────────────────────────────────────────────
const TAG_U : u8 = 0; // unsigned literal  (used for arity, indices)
const TAG_I : u8 = 1; // signed integer
const TAG_A : u8 = 2; // atom index
const TAG_X : u8 = 3; // X register
const TAG_Y : u8 = 4; // Y register (stack)
const TAG_F : u8 = 5; // label (f = fail)
const TAG_Z : u8 = 7; // extended tag (lists, floats)

// ─── Generic opcode numbers (stable since OTP 20) ────────────────────────────
// The Code chunk stores GENERIC opcodes; the BEAM loader specialises them.
const OP_LABEL        : u8 = 1;
const OP_FUNC_INFO    : u8 = 2;
const OP_INT_CODE_END : u8 = 3;
const OP_CALL         : u8 = 4;
const OP_CALL_LAST    : u8 = 5;
const OP_CALL_ONLY    : u8 = 6;
const OP_CALL_EXT     : u8 = 7;
const OP_CALL_EXT_LAST: u8 = 8;
const OP_BIF0         : u8 = 9;
const OP_BIF1         : u8 = 10;
const OP_BIF2         : u8 = 11;
const OP_ALLOCATE     : u8 = 12;
const OP_DEALLOCATE   : u8 = 18;
const OP_RETURN       : u8 = 19;
const OP_MOVE         : u8 = 64;
const OP_JUMP         : u8 = 61;
const _OP_PUT_LIST    : u8 = 69;
const OP_PUT_TUPLE    : u8 = 70;
const OP_GET_TUPLE_ELEMENT: u8 = 66;
const OP_GET_LIST        : u8 = 65;
const OP_CASE_END        : u8 = 74;
const OP_PUT          : u8 = 71;
const OP_CALL_FUN     : u8 = 75;  // 0x4B verified from beam binary
const OP_IF_END       : u8 = 73;
const OP_IS_TUPLE        : u8 = 57;
const OP_IS_NONEMPTY_LIST: u8 = 56;
const OP_IS_NIL          : u8 = 52;
const OP_TEST_ARITY      : u8 = 58;
const OP_TEST_HEAP     : u8 = 16;
const OP_PUT_TUPLE2   : u8 = 164;
const OP_MAKE_FUN3    : u8 = 171;
const OP_GC_BIF1       : u8 = 124;
const OP_GC_BIF2       : u8 = 125;
const OP_GC_BIF3       : u8 = 152;
const OP_IS_EQ_EXACT      : u8 = 43;
const _OP_IS_INTEGER       : u8 = 45;
const _OP_IS_ATOM          : u8 = 48;
const _OP_IS_LIST          : u8 = 55;
const _OP_IS_TUPLE         : u8 = 57;
const _OP_TEST_ARITY       : u8 = 58;
const _OP_SELECT_VAL       : u8 = 59;
const _OP_IS_TAGGED_TUPLE  : u8 = 159;

// ─── Helper types ─────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct Import {
    pub module:   u32, // atom index
    pub function: u32, // atom index
    pub arity:    u32,
}

#[derive(Clone, Debug)]
pub struct Export {
    pub function: u32, // atom index
    pub arity:    u32,
    pub label:    u32,
}

/// One entry in the FunT chunk (a lambda / fun-reference).
#[derive(Clone, Debug)]
pub struct FunEntry {
    pub function: u32, // atom index of the function name
    pub arity:    u32, // arity of the function
    pub label:    u32, // code label of the function
    pub index:    u32, // sequential index (0-based) among all funs
    pub num_free: u32, // number of free variables captured
    pub old_uniq: u32, // will be set to 0; loader fills from MD5
}

struct LiftedFun {
    name: String,
    arity: u32,
    num_free: u32,
    binders: Vec<ast::Binder>,
    body: ast::Expr,
    label_entry: u32,
    label_body: u32,
    free_vars: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Reg {
    X(u32),
    Y(u32),
}

impl Reg {
    fn y_index(&self) -> Option<u32> {
        if let Reg::Y(i) = self { Some(*i) } else { None }
    }
}

struct CodeGenCtx<'a> {
    vars: std::collections::HashMap<String, Reg>,
    stack_depth: u32,
    max_stack: u32,
    local_fns: &'a std::collections::HashMap<(String, u32), u32>,
    env: &'a crate::env::Env,
    next_x: u32,
    lifted_funs: &'a mut Vec<LiftedFun>,
    lambda_counter: &'a mut u32,
    arg_offset: u32,
}

impl<'a> CodeGenCtx<'a> {
    fn push_y(&mut self) -> Reg {
        let r = Reg::Y(self.stack_depth);
        self.stack_depth += 1;
        if self.stack_depth > self.max_stack {
            self.max_stack = self.stack_depth;
        }
        r
    }

    fn pop_y(&mut self) {
        if self.stack_depth > 0 {
            self.stack_depth -= 1;
        }
    }
}

// ─── BeamModule builder ──────────────────────────────────────────────────────

#[derive(Clone)]
pub struct BeamModule {
    pub atom_indices: std::collections::HashMap<String, u32>,
    pub atom_table: Vec<String>,
    pub imports: Vec<Import>,
    pub exports: Vec<Export>,
    pub num_functions: u32,
    pub num_labels: u32,
    pub code_buf: Vec<u8>,
    pub funs: Vec<FunEntry>,
}

impl BeamModule {
    pub fn new(name: &str) -> Self {
        let mut atoms = Vec::new();
        let mut indices = std::collections::HashMap::new();
        atoms.push(name.to_string());
        indices.insert(name.to_string(), 1);
        
        BeamModule {
            atom_table: atoms,
            atom_indices: indices,
            imports: Vec::new(),
            exports: Vec::new(),
            num_functions: 0,
            num_labels: 0,
            code_buf: Vec::new(),
            funs: Vec::new(),
        }
    }

    pub fn next_label_id(&mut self) -> u32 {
        self.num_labels += 1;
        self.num_labels
    }

    pub fn intern_atom(&mut self, s: &str) -> u32 {
        if let Some(&idx) = self.atom_indices.get(s) {
            return idx;
        }
        let idx = (self.atom_table.len() as u32) + 1;
        self.atom_table.push(s.to_string());
        self.atom_indices.insert(s.to_string(), idx);
        idx
    }

    pub fn intern_fun(&mut self, fun_atom: u32, arity: u32, label: u32, num_free: u32) -> u32 {
        // Re-use if identical entry exists
        if let Some(idx) = self.funs.iter().position(|f| {
            f.function == fun_atom && f.arity == arity && f.label == label && f.num_free == num_free
        }) {
            return idx as u32;
        }
        let idx = self.funs.len() as u32;
        self.funs.push(FunEntry {
            function: fun_atom,
            arity,
            label,
            index: idx,
            num_free,
            old_uniq: 0, 
        });
        idx
    }

    pub fn emit_make_fun3(&mut self, fun_idx: u32, _live_regs: u32, dst: Reg, free_vars: &[Reg]) {
        // test_heap using alloc-list format required by OTP 26+:
        //   {alloc, [{words, num_free}, {floats, 0}, {funs, 1}]}, live=num_free
        let num_free = free_vars.len() as u32;
        let live = num_free; // X registers holding captured values are live
        self.emit_op(OP_TEST_HEAP);
        // Alloc-list header: TAG_Z(3) = 0x37 = alloc_list type
        self.code_buf.push(0x37);
        self.emit_arg(TAG_U, 3); // 3 entries: words, floats, funs
        self.emit_arg(TAG_U, 0); self.emit_arg(TAG_U, num_free as u64); // {words, num_free}
        self.emit_arg(TAG_U, 1); self.emit_arg(TAG_U, 0);               // {floats, 0}
        self.emit_arg(TAG_U, 2); self.emit_arg(TAG_U, 1);               // {funs, 1}
        self.emit_arg(TAG_U, live as u64); // live X registers

        // OTP's JIT only supports X registers as make_fun3 destination (erlc always uses X(0)).
        // Always emit into X(0), then move to the actual dst if different.
        self.emit_op(OP_MAKE_FUN3);
        self.emit_arg(TAG_U, fun_idx as u64);
        self.emit_reg_arg(Reg::X(0));

        // Free variables: extended list — TAG_Z(1) is the list-type marker (always 0x17),
        // followed by TAG_U(count), then each register.
        self.emit_arg(TAG_Z, 1);
        self.emit_arg(TAG_U, free_vars.len() as u64);
        for &r in free_vars {
            self.emit_reg_arg(r);
        }

        // Move result from X(0) to actual destination if needed.
        if dst != Reg::X(0) {
            self.emit_move(Reg::X(0), dst);
        }
    }

    fn intern_import(&mut self, module: &str, function: &str, arity: u32) -> u32 {
        let m = self.intern_atom(module);
        let f = self.intern_atom(function);
        if let Some(idx) = self.imports.iter().position(|i| i.module == m && i.function == f && i.arity == arity) {
            return idx as u32;
        }
        let idx = self.imports.len() as u32;
        self.imports.push(Import { module: m, function: f, arity });
        idx
    }

    // ── Code emitters ─────────────────────────────────────────────────────────

    fn emit_op(&mut self, op: u8) {
        self.code_buf.push(op);
    }

    fn emit_arg(&mut self, tag: u8, value: u64) {
        if value < 16 {
            self.code_buf.push((value << 4) as u8 | tag);
        } else if value < 2048 {
            let b1 = ((value >> 3) & 0xE0u64) as u8 | tag | 8;
            let b2 = (value & 0xFF) as u8;
            self.code_buf.push(b1);
            self.code_buf.push(b2);
        } else {
            // Values ≥ 2048: variable-length big-endian multi-byte form.
            // b0 = tag | (len_code << 5) | 0x18, followed by `count` bytes.
            // Decoder reads count = len_code + 2 bytes; len_code is stored in b0 bits 5-7.
            let count: u32 = if value <= 0xFFFF { 2 }
                else if value <= 0xFF_FFFF { 3 }
                else if value <= 0xFFFF_FFFF { 4 }
                else if value <= 0xFF_FFFF_FFFF { 5 }
                else if value <= 0xFFFF_FFFF_FFFF { 6 }
                else if value <= 0xFF_FFFF_FFFF_FFFF { 7 }
                else { 8 };
            let len_code = (count - 2) as u8;
            self.code_buf.push(tag | (len_code << 5) | 0x18);
            for i in (0..count).rev() {
                self.code_buf.push((value >> (i * 8)) as u8);
            }
        }
    }

    fn emit_reg_arg(&mut self, reg: Reg) {
        match reg {
            Reg::X(n) => self.emit_arg(TAG_X, n as u64),
            Reg::Y(n) => self.emit_arg(TAG_Y, n as u64),
        }
    }

    fn emit_label(&mut self, n: u32) {
        self.emit_op(OP_LABEL);
        self.emit_arg(TAG_U, n as u64);
    }

    fn emit_func_info(&mut self, mod_atom: u32, fun_atom: u32, arity: u32) {
        self.emit_op(OP_FUNC_INFO);
        self.emit_arg(TAG_A, mod_atom as u64);
        self.emit_arg(TAG_A, fun_atom as u64);
        self.emit_arg(TAG_U, arity as u64);
    }

    fn emit_return(&mut self) {
        self.emit_op(OP_RETURN);
    }

    fn emit_int_code_end(&mut self) {
        self.emit_op(OP_INT_CODE_END);
    }

    /// `move Src, {x,Dst}`
    fn emit_move_int_to_x(&mut self, int_val: i64, x_reg: u32) {
        self.emit_op(OP_MOVE);
        // Source: integer literal
        if int_val >= 0 && int_val < 16 {
            self.emit_arg(TAG_I, int_val as u64);
        } else if int_val >= 0 {
            self.emit_arg(TAG_I, int_val as u64);
        } else {
            // Negative: use the 4-byte form with sign extension trick
            // For now, encode as a large literal
            self.emit_arg(TAG_I, (int_val as u32) as u64);
        }
        // Destination: X register
        self.emit_arg(TAG_X, x_reg as u64);
    }

    fn emit_move_atom_to_x(&mut self, atom_idx: u32, x_reg: u32) {
        self.emit_op(OP_MOVE);
        self.emit_arg(TAG_A, atom_idx as u64);
        self.emit_arg(TAG_X, x_reg as u64);
    }

    fn emit_move_x_to_x(&mut self, src: u32, dst: u32) {
        self.emit_op(OP_MOVE);
        self.emit_arg(TAG_X, src as u64);
        self.emit_arg(TAG_X, dst as u64);
    }

    fn emit_call_ext(&mut self, arity: u32, import_idx: u32) {
        self.emit_op(OP_CALL_EXT);
        self.emit_arg(TAG_U, arity as u64);
        self.emit_arg(TAG_U, import_idx as u64);
    }

    fn emit_call(&mut self, arity: u32, label: u32) {
        self.emit_op(OP_CALL);
        self.emit_arg(TAG_U, arity as u64);
        self.emit_arg(TAG_F, label as u64);  // call label
    }

    fn emit_call_fun(&mut self, arity: u32) {
        self.emit_op(OP_CALL_FUN);
        self.emit_arg(TAG_U, arity as u64);
    }

    fn emit_put_tuple2(&mut self, arity: u32, target: Reg, elements: &[Reg]) {
        self.emit_op(OP_PUT_TUPLE2);
        self.emit_reg_arg(target);
        self.emit_arg(TAG_Z, 1); // Extended tag with list_tag (1)
        self.emit_arg(TAG_U, arity as u64);
        for reg in elements {
            self.emit_reg_arg(*reg);
        }
    }

    fn emit_allocate(&mut self, stack_size: u32, live_regs: u32) {
        self.emit_op(OP_ALLOCATE);
        self.emit_arg(TAG_U, stack_size as u64);
        self.emit_arg(TAG_U, live_regs as u64);
    }

    /// Emit `allocate` with a 2-byte placeholder for `stack_size`.
    /// Returns the byte offset of the placeholder so it can be patched later
    /// once the actual Y-register high-water mark is known.
    fn begin_allocate(&mut self, live_regs: u32) -> usize {
        self.emit_op(OP_ALLOCATE);
        let offset = self.code_buf.len();
        // Reserve 2 bytes (2-byte compact encoding, value = 0 placeholder).
        self.code_buf.push(TAG_U | 8);  // b1: 2-byte form with value 0
        self.code_buf.push(0);           // b2
        self.emit_arg(TAG_U, live_regs as u64);
        offset
    }

    /// Patch the 2-byte stack_size arg previously written by `begin_allocate`.
    fn patch_alloc_size(&mut self, offset: usize, stack_size: u32) {
        let v = stack_size as u64;
        // Always write as 2-byte compact form (supports values 0..2047).
        self.code_buf[offset]     = (((v >> 3) & 0xE0u64) as u8) | TAG_U | 8;
        self.code_buf[offset + 1] = (v & 0xFF) as u8;
    }

    fn emit_deallocate(&mut self, stack_size: u32) {
        self.emit_op(OP_DEALLOCATE);
        self.emit_arg(TAG_U, stack_size as u64);
    }

    fn emit_test_heap(&mut self, heap_words: u32, live_regs: u32) {
        self.emit_op(OP_TEST_HEAP);
        self.emit_arg(TAG_U, heap_words as u64);
        self.emit_arg(TAG_U, live_regs as u64);
    }

    fn emit_move_x_to_y(&mut self, x: u32, y: u32) {
        self.emit_op(OP_MOVE);
        self.emit_arg(TAG_X, x as u64);
        self.emit_arg(TAG_Y, y as u64);
    }

    fn emit_move_y_to_x(&mut self, y: u32, x: u32) {
        self.emit_op(OP_MOVE);
        self.emit_arg(TAG_Y, y as u64);
        self.emit_arg(TAG_X, x as u64);
    }

    fn emit_move(&mut self, src: Reg, dst: Reg) {
        if src == dst { return; }
        self.emit_op(OP_MOVE);
        self.emit_reg_arg(src);
        self.emit_reg_arg(dst);
    }

    fn emit_move_to_reg(&mut self, val_tag: u8, val: u64, dst: Reg) {
        self.emit_op(OP_MOVE);
        self.emit_arg(val_tag, val);
        self.emit_reg_arg(dst);
    }

    fn emit_make_nil(&mut self, dst: Reg) {
        // Construct [] via runtime helper to avoid invalid literal encodings.
        // Phi.Runtime.List:nil/0 -> []
        let imp_idx = self.intern_import("Phi.Runtime.List", "nil", 0);
        self.emit_call_ext(0, imp_idx);
        self.emit_move(Reg::X(0), dst);
    }

    fn emit_jump(&mut self, label: u32) {
        self.emit_op(OP_JUMP);
        self.emit_arg(TAG_F, label as u64);
    }

    fn emit_if_end(&mut self) {
        self.emit_op(OP_IF_END);
    }

    fn emit_is_eq_exact(&mut self, fail_label: u32, arg1: Reg, arg2_tag: u8, arg2_val: u64) {
        self.emit_op(OP_IS_EQ_EXACT);
        self.emit_arg(TAG_F, fail_label as u64);
        self.emit_reg_arg(arg1);
        self.emit_arg(arg2_tag, arg2_val);
    }

    fn emit_is_tuple(&mut self, fail_label: u32, reg: Reg) {
        self.emit_op(OP_IS_TUPLE);
        self.emit_arg(TAG_F, fail_label as u64);
        self.emit_reg_arg(reg);
    }

    fn emit_test_arity(&mut self, fail_label: u32, reg: Reg, arity: u32) {
        self.emit_op(OP_TEST_ARITY);
        self.emit_arg(TAG_F, fail_label as u64);
        self.emit_reg_arg(reg);
        self.emit_arg(TAG_U, arity as u64);
    }

    fn emit_get_tuple_element(&mut self, src: Reg, index: u32, dst: Reg) {
        self.emit_op(OP_GET_TUPLE_ELEMENT);
        self.emit_reg_arg(src);
        self.emit_arg(TAG_U, index as u64);
        self.emit_reg_arg(dst);
    }

    fn emit_is_nonempty_list(&mut self, fail_label: u32, reg: Reg) {
        self.emit_op(OP_IS_NONEMPTY_LIST);
        self.emit_arg(TAG_F, fail_label as u64);
        self.emit_reg_arg(reg);
    }

    fn emit_get_list(&mut self, src: Reg, head: Reg, tail: Reg) {
        self.emit_op(OP_GET_LIST);
        self.emit_reg_arg(src);
        self.emit_reg_arg(head);
        self.emit_reg_arg(tail);
    }

    fn emit_put_list(&mut self, head: Reg, tail: Reg, dst: Reg) {
        self.emit_op(_OP_PUT_LIST);
        self.emit_reg_arg(head);
        self.emit_reg_arg(tail);
        self.emit_reg_arg(dst);
    }

    fn emit_is_nil(&mut self, fail_label: u32, reg: Reg) {
        self.emit_op(OP_IS_NIL);
        self.emit_arg(TAG_F, fail_label as u64);
        self.emit_reg_arg(reg);
    }

    fn emit_case_end(&mut self, reg: Reg) {
        self.emit_op(OP_CASE_END);
        self.emit_reg_arg(reg);
    }

    // ── Serialisation: individual chunks ─────────────────────────────────────

    fn build_atu8_chunk(&self) -> Vec<u8> {
        let mut d = Vec::new();
        d.extend_from_slice(&(self.atom_table.len() as u32).to_be_bytes());
        for atom in &self.atom_table {
            let b = atom.as_bytes();
            d.push(b.len() as u8);
            d.extend_from_slice(b);
        }
        d
    }

    fn build_impt_chunk(&self) -> Vec<u8> {
        let mut d = Vec::new();
        d.extend_from_slice(&(self.imports.len() as u32).to_be_bytes());
        for imp in &self.imports {
            d.extend_from_slice(&imp.module.to_be_bytes());
            d.extend_from_slice(&imp.function.to_be_bytes());
            d.extend_from_slice(&imp.arity.to_be_bytes());
        }
        d
    }

    fn build_expt_chunk(&self) -> Vec<u8> {
        let mut d = Vec::new();
        d.extend_from_slice(&(self.exports.len() as u32).to_be_bytes());
        for exp in &self.exports {
            d.extend_from_slice(&exp.function.to_be_bytes());
            d.extend_from_slice(&exp.arity.to_be_bytes());
            d.extend_from_slice(&exp.label.to_be_bytes());
        }
        d
    }

    fn build_loct_chunk(&self) -> Vec<u8> {
        // zero local functions exposed for now
        0u32.to_be_bytes().to_vec()
    }

    fn build_funt_chunk(&self) -> Vec<u8> {
        let mut d = Vec::new();
        d.extend_from_slice(&(self.funs.len() as u32).to_be_bytes());
        for fun in &self.funs {
            d.extend_from_slice(&fun.function.to_be_bytes());
            d.extend_from_slice(&fun.arity.to_be_bytes());
            d.extend_from_slice(&fun.label.to_be_bytes());
            d.extend_from_slice(&fun.index.to_be_bytes());
            d.extend_from_slice(&fun.num_free.to_be_bytes());
            d.extend_from_slice(&fun.old_uniq.to_be_bytes()); // loader fills from MD5
        }
        d
    }

    fn build_code_chunk(&self) -> Vec<u8> {
        let info_size: u32 = 16; // size of remaining sub-header fields (4 × 4 bytes)
        let instruction_set: u32 = 0;
        let opcode_max: u32 = 171; // use 171 for make_fun3
        let labels: u32 = self.num_labels + 1; // loader requires label_id < num_labels
        let functions: u32 = self.num_functions;

        let mut d = Vec::new();
        d.extend_from_slice(&info_size.to_be_bytes());
        d.extend_from_slice(&instruction_set.to_be_bytes());
        d.extend_from_slice(&opcode_max.to_be_bytes());
        d.extend_from_slice(&labels.to_be_bytes());
        d.extend_from_slice(&functions.to_be_bytes());
        d.extend_from_slice(&self.code_buf);
        d
    }

    // ── Final BEAM binary serialisation ──────────────────────────────────────

    fn chunk(id: &[u8; 4], data: &[u8]) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(id);
        v.extend_from_slice(&(data.len() as u32).to_be_bytes());
        v.extend_from_slice(data);
        // Pad to 4-byte alignment
        let pad = (4 - (data.len() % 4)) % 4;
        for _ in 0..pad { v.push(0); }
        v
    }

    pub fn to_beam_bytes(self) -> Vec<u8> {
        let mut chunks: Vec<u8> = [
            Self::chunk(b"AtU8", &self.build_atu8_chunk()),
            Self::chunk(b"Code", &self.build_code_chunk()),
            Self::chunk(b"StrT", &[]),
            Self::chunk(b"ImpT", &self.build_impt_chunk()),
            Self::chunk(b"ExpT", &self.build_expt_chunk()),
        ].into_iter().flatten().collect();

        // Omit LocT if we don't have any local functions exposed
        // if !self.locals.is_empty() {
        //     chunks.extend(Self::chunk(b"LocT", &self.build_loct_chunk()));
        // }

        if !self.funs.is_empty() {
            chunks.extend(Self::chunk(b"FunT", &self.build_funt_chunk()));
        }

        let mut out = Vec::new();
        out.extend_from_slice(b"FOR1");
        // File size = size of everything after this u32 field
        out.extend_from_slice(&((chunks.len() + 4) as u32).to_be_bytes()); // +4 for "BEAM"
        out.extend_from_slice(b"BEAM");
        out.extend_from_slice(&chunks);
        out
    }
}

// ─── Public entry point ───────────────────────────────────────────────────────

/// Try to generate a `.beam` binary directly from a Phi module.
/// Returns `None` if the module uses constructs too complex for simple codegen
/// (the caller falls back to `erlc` in that case).
pub fn generate_beam(module: &ast::Module, env: &crate::env::Env) -> Result<Vec<u8>, BeamGenError> {
    // Build a per-module env: clone global env but override module_aliases with only
    // this module's own Import declarations. The global env merges aliases from ALL
    // modules (last writer wins), so e.g. `Test/Data/Map.phi`'s `import Data.Map as M`
    // would clobber `Test.phi`'s `import Test.Data.Map as M`.
    let mut local_env = env.clone();
    local_env.module_aliases.clear();
    for decl in &module.declarations {
        if let crate::ast::Decl::Import(m, _items, Some(alias), _) = decl {
            local_env.module_aliases.insert(alias.clone(), m.clone());
        }
    }
    let env = &local_env;

    let erl_mod_name = format!("Phi.{}", module.name);
    let mut beam = BeamModule::new(&erl_mod_name);
    let mod_atom = beam.intern_atom(&erl_mod_name);

    let mut all_decls = Vec::new();
    collect_all_decls(&module.declarations, &mut all_decls);

    let mut groups: Vec<(String, u32, Vec<ast::Decl>)> = Vec::new();
    for decl in all_decls {
        let (name, arity) = match &decl {
            ast::Decl::Value(n, binders, _, _) => (n.clone(), binders.len() as u32),
            ast::Decl::ValueGuarded(n, binders, _guards, _) => (n.clone(), binders.len() as u32),
            ast::Decl::PatBind(binder, _expr, _) => {
                if let ast::Binder::Var(n) = binder {
                    (n.clone(), 0)
                } else {
                    continue;
                }
            }
            ast::Decl::ForeignImport(original, local, ty) => {
                let name = if local.is_empty() { original.clone() } else { local.clone() };
                (name, type_arity(ty))
            }
            _ => continue,
        };
        if let Some(group) = groups.iter_mut().find(|(n, a, _)| n == &name && *a == arity) {
            group.2.push(decl);
        } else {
            groups.push((name, arity, vec![decl]));
        }
    }

    let mut local_fns = std::collections::HashMap::new();
    let mut lambda_counter = 0;
    let mut work_queue = std::collections::VecDeque::new();

    struct WorkItem {
        name: String,
        arity: u32,
        num_free: u32,
        decls: Vec<ast::Decl>,
        lam_body: Option<(Vec<ast::Binder>, ast::Expr, Vec<String>)>,
        label_entry: u32,
        label_body: u32,
    }

    for (name, arity, decls) in &groups {
        let entry_label = beam.next_label_id();
        let body_label = beam.next_label_id();
        local_fns.insert((name.clone(), *arity), body_label);
        work_queue.push_back(WorkItem {
            name: name.clone(),
            arity: *arity,
            num_free: 0,
            decls: decls.clone(),
            lam_body: None,
            label_entry: entry_label,
            label_body: body_label,
        });
    }

    while let Some(item) = work_queue.pop_front() {
        let fun_atom = beam.intern_atom(&item.name);
        beam.num_functions += 1;
        beam.emit_label(item.label_entry);
        beam.emit_func_info(mod_atom, fun_atom, item.arity);
        beam.emit_label(item.label_body);

        let mut current_lifted = Vec::new();

        if let Some((binders, body, free_vars_list)) = item.lam_body {
            let mut ctx = CodeGenCtx {
                env, vars: std::collections::HashMap::new(),
                local_fns: &local_fns, stack_depth: 0, max_stack: 0,
                next_x: item.arity,
                lifted_funs: &mut current_lifted,
                lambda_counter: &mut lambda_counter,
                arg_offset: item.num_free,
            };

            // emit allocate BEFORE any pattern check: tuple binders emit
            // get_tuple_element to Y registers which requires an allocated frame.
            ctx.max_stack = 0;
            let lam_alloc_off = beam.begin_allocate(item.arity);

            // Real fail label for pattern checks: using {f,0} (TAG_p) after allocate
            // crashes the OTP JIT during loading; a real label is required.
            let lam_fail_label = beam.next_label_id();

            // Bind lambda parameters to X registers (may write Y regs for tuple binders)
            for (i, binder) in binders.iter().enumerate() {
                let x_reg = Reg::X(i as u32);
                emit_pattern_check(&mut beam, binder, x_reg, lam_fail_label, &mut ctx)?
            }

            // Bind free variables to X registers after parameters.
            // In BEAM, when call_fun invokes a closure: X(0..user_arity-1) = explicit args,
            // X(user_arity..total_arity-1) = free vars extracted from the fun object.
            let user_arity = item.arity - item.num_free;
            for (i, var) in free_vars_list.iter().enumerate() {
                ctx.vars.insert(var.clone(), Reg::X(user_arity + i as u32));
            }

            emit_expr(&mut beam, &body, &mut ctx, Reg::X(0))?;
            let lam_alloc = ctx.max_stack.max(1);
            beam.patch_alloc_size(lam_alloc_off, lam_alloc);
            beam.emit_deallocate(lam_alloc);
            beam.emit_return();
            // Pattern-match failure handler: raise case_clause exception.
            // This must come after return so it's only reached via the fail label.
            beam.emit_label(lam_fail_label);
            beam.emit_case_end(Reg::X(0));
        } else {
            let decls = item.decls;
            let clause_labels: Vec<u32> = (0..decls.len()).map(|_| beam.next_label_id()).collect();
            let fail_all = beam.next_label_id();

            for (idx, decl) in decls.iter().enumerate() {
                beam.emit_label(clause_labels[idx]);
                let fail_to = if idx + 1 < decls.len() { clause_labels[idx + 1] } else { fail_all };

                match decl {
                    ast::Decl::Value(_n, binders, expr, where_decls) => {
                        let mut ctx = CodeGenCtx {
                            env, vars: std::collections::HashMap::new(),
                            local_fns: &local_fns, stack_depth: 0, max_stack: 0,
                            next_x: item.arity,
                            lifted_funs: &mut current_lifted,
                            lambda_counter: &mut lambda_counter,
                            arg_offset: 0,
                        };

                        let alloc_off = beam.begin_allocate(item.arity);
                        ctx.max_stack = 0;

                        for (i, binder) in binders.iter().enumerate() {
                            let y_reg = ctx.push_y();
                            beam.emit_move_x_to_y(i as u32, y_reg.y_index().unwrap());
                            emit_pattern_check(&mut beam, binder, y_reg, fail_to, &mut ctx)?;
                        }

                        for where_decl in where_decls {
                            match where_decl {
                                ast::Decl::PatBind(binder, rhs_expr, _) => {
                                    let y = ctx.push_y();
                                    emit_expr(&mut beam, rhs_expr, &mut ctx, y)?;
                                    let fail_lbl = beam.next_label_id();
                                    let ok_lbl = beam.next_label_id();
                                    emit_pattern_check(&mut beam, binder, y, fail_lbl, &mut ctx)?;
                                    beam.emit_jump(ok_lbl);
                                    beam.emit_label(fail_lbl);
                                    beam.emit_case_end(y);
                                    beam.emit_label(ok_lbl);
                                }
                                ast::Decl::Value(name, sub_binders, rhs_expr, _) if sub_binders.is_empty() => {
                                    let y = ctx.push_y();
                                    emit_expr(&mut beam, rhs_expr, &mut ctx, y)?;
                                    ctx.vars.insert(name.clone(), y);
                                }
                                _ => {}
                            }
                        }

                        emit_expr(&mut beam, expr, &mut ctx, Reg::X(0))?;
                        let alloc = ctx.max_stack.max(1);
                        beam.patch_alloc_size(alloc_off, alloc);
                        beam.emit_deallocate(alloc);
                        beam.emit_return();
                    }
                    ast::Decl::PatBind(binder, expr, _) => {
                        // Treat `x = expr` at top-level as a 0-arity function returning expr.
                        let mut ctx = CodeGenCtx {
                            env, vars: std::collections::HashMap::new(),
                            local_fns: &local_fns, stack_depth: 0, max_stack: 0,
                            next_x: item.arity,
                            lifted_funs: &mut current_lifted,
                            lambda_counter: &mut lambda_counter,
                            arg_offset: 0,
                        };

                        if let ast::Binder::Var(_name) = binder {
                            let alloc_off = beam.begin_allocate(item.arity);
                            ctx.max_stack = 0;
                            emit_expr(&mut beam, expr, &mut ctx, Reg::X(0))?;
                            let alloc = ctx.max_stack.max(1);
                            beam.patch_alloc_size(alloc_off, alloc);
                            beam.emit_deallocate(alloc);
                            beam.emit_return();
                        } else {
                            return Err(BeamGenError::Unsupported("top_patbind"));
                        }
                    }
                    ast::Decl::ValueGuarded(_n, binders, guards, where_decls) => {
                        let mut ctx = CodeGenCtx {
                            env, vars: std::collections::HashMap::new(),
                            local_fns: &local_fns, stack_depth: 0, max_stack: 0,
                            next_x: item.arity,
                            lifted_funs: &mut current_lifted,
                            lambda_counter: &mut lambda_counter,
                            arg_offset: 0,
                        };

                        let alloc_off = beam.begin_allocate(item.arity);
                        ctx.max_stack = 0;
                        for (i, binder) in binders.iter().enumerate() {
                            let y_reg = ctx.push_y();
                            beam.emit_move_x_to_y(i as u32, y_reg.y_index().unwrap());
                            emit_pattern_check(&mut beam, binder, y_reg, fail_to, &mut ctx)?;
                        }

                        for where_decl in where_decls {
                            match where_decl {
                                ast::Decl::PatBind(binder, rhs_expr, _) => {
                                    let y = ctx.push_y();
                                    emit_expr(&mut beam, rhs_expr, &mut ctx, y)?;
                                    let fail_lbl = beam.next_label_id();
                                    let ok_lbl = beam.next_label_id();
                                    emit_pattern_check(&mut beam, binder, y, fail_lbl, &mut ctx)?;
                                    beam.emit_jump(ok_lbl);
                                    beam.emit_label(fail_lbl);
                                    beam.emit_case_end(y);
                                    beam.emit_label(ok_lbl);
                                }
                                ast::Decl::Value(name, sub_binders, rhs_expr, _) if sub_binders.is_empty() => {
                                    let y = ctx.push_y();
                                    emit_expr(&mut beam, rhs_expr, &mut ctx, y)?;
                                    ctx.vars.insert(name.clone(), y);
                                }
                                _ => {}
                            }
                        }

                        // Each guarded branch becomes: if all conds true -> body
                        // otherwise fallthrough to next guard branch, else to fail_to.
                        let true_atom = beam.intern_atom("true");
                        let mut next_guard_label = beam.next_label_id();
                        let end_label = beam.next_label_id();

                        for (g_idx, vg) in guards.iter().enumerate() {
                            beam.emit_label(next_guard_label);
                            next_guard_label = beam.next_label_id();

                            // Evaluate guard conditions
                            for cond in &vg.conditions {
                                let y = ctx.push_y();
                                emit_expr(&mut beam, cond, &mut ctx, y)?;
                                beam.emit_is_eq_exact(next_guard_label, y, TAG_A, true_atom as u64);
                                ctx.pop_y();
                            }

                            emit_expr(&mut beam, &vg.body, &mut ctx, Reg::X(0))?;
                            beam.emit_jump(end_label);

                            if g_idx + 1 == guards.len() {
                                // last guard branch failure should go to next clause
                                beam.emit_label(next_guard_label);
                                beam.emit_jump(fail_to);
                            }
                        }

                        beam.emit_label(end_label);
                        let alloc = ctx.max_stack.max(1);
                        beam.patch_alloc_size(alloc_off, alloc);
                        beam.emit_deallocate(alloc);
                        beam.emit_return();
                    }
                    ast::Decl::ForeignImport(original, _, _) => {
                        let ffi_mod_name = format!("Phi.{}.FFI", module.name);
                        let imp_idx = beam.intern_import(&ffi_mod_name, original, item.arity);
                        beam.emit_call_ext(item.arity, imp_idx);
                        beam.emit_return();
                    }
                    _ => {}
                }
            }
            beam.emit_label(fail_all);
            beam.emit_if_end();
            
            // Export top-level functions
            beam.exports.push(Export { function: fun_atom, arity: item.arity, label: item.label_body });
        }

        for lifted in current_lifted {
            local_fns.insert((lifted.name.clone(), lifted.arity), lifted.label_body);
            work_queue.push_back(WorkItem {
                name: lifted.name,
                arity: lifted.arity,
                num_free: lifted.num_free,
                decls: Vec::new(),
                lam_body: Some((lifted.binders, lifted.body, lifted.free_vars)),
                label_entry: lifted.label_entry,
                label_body: lifted.label_body,
            });
        }
    }

    beam.emit_int_code_end();
    // Some modules may contain only types/classes/instances and no runtime values.
    // It's still useful to emit a BEAM module so dependent compilation can proceed.
    Ok(beam.to_beam_bytes())
}

fn collect_binder_names(binder: &ast::Binder, names: &mut std::collections::HashSet<String>) {
    match binder {
        ast::Binder::Var(n) => {
            if n != "true" && n != "false" && n != "unit" {
                names.insert(n.clone());
            }
        }
        ast::Binder::Tuple(binders) | ast::Binder::List(binders) => {
            for b in binders { collect_binder_names(b, names); }
        }
        ast::Binder::Constructor(_, binders) => {
            for b in binders { collect_binder_names(b, names); }
        }
        ast::Binder::Named(n, b) => {
            names.insert(n.clone());
            collect_binder_names(b, names);
        }
        ast::Binder::TypeAnn(b, _) => collect_binder_names(b, names),
        _ => {}
    }
}

fn free_vars_list(expr: &ast::Expr) -> Vec<String> {
    let mut free = std::collections::HashSet::new();
    let mut bound = std::collections::HashSet::new();
    free_vars(expr, &mut bound, &mut free);
    let mut v: Vec<_> = free.into_iter().collect();
    v.sort();
    v
}

fn free_vars(
    expr: &ast::Expr,
    bound: &mut std::collections::HashSet<String>,
    free: &mut std::collections::HashSet<String>
) {
    match expr {
        ast::Expr::Var(n) => {
            if !bound.contains(n) && !n.chars().next().map_or(false, |c| c.is_uppercase())
               && n != "true" && n != "false" && n != "unit" {
                free.insert(n.clone());
            }
        }
        ast::Expr::Number(_) | ast::Expr::Float(_) | ast::Expr::String(_) | ast::Expr::Char(_) | ast::Expr::Atom(_) | ast::Expr::Unit => {}
        ast::Expr::App(f, a) => {
            free_vars(f, bound, free);
            free_vars(a, bound, free);
        }
        ast::Expr::BinOp(l, _, r) => {
            free_vars(l, bound, free);
            free_vars(r, bound, free);
        }
        ast::Expr::If(c, t, e) => {
            free_vars(c, bound, free);
            free_vars(t, bound, free);
            free_vars(e, bound, free);
        }
        ast::Expr::Case(exprs, branches) => {
            for e in exprs { free_vars(e, bound, free); }
            for b in branches {
                let mut new_bound = bound.clone();
                for binder in &b.binders { collect_binder_names(binder, &mut new_bound); }
                for g in &b.guards { free_vars(g, &mut new_bound, free); }
                free_vars(&b.body, &mut new_bound, free);
            }
        }
        ast::Expr::Lam(binders, body) => {
            let mut new_bound = bound.clone();
            for b in binders { collect_binder_names(b, &mut new_bound); }
            free_vars(body, &mut new_bound, free);
        }
        ast::Expr::Let(decls, body) => {
            let mut new_bound = bound.clone();
            for decl in decls {
                match decl {
                    ast::Decl::Value(n, binders, rhs, _) => {
                        // RHS is evaluated in the outer scope (before name is bound)
                        free_vars(rhs, &mut new_bound, free);
                        new_bound.insert(n.clone());
                        for b in binders { collect_binder_names(b, &mut new_bound); }
                    }
                    ast::Decl::PatBind(binder, rhs, _) => {
                        // RHS is evaluated in the current scope (before binder vars are bound)
                        free_vars(rhs, &mut new_bound, free);
                        collect_binder_names(binder, &mut new_bound);
                    }
                    ast::Decl::TypeSignature(_, _) => {}
                    _ => {}
                }
            }
            free_vars(body, &mut new_bound, free);
        }
        ast::Expr::Tuple(exprs) | ast::Expr::Binary(exprs) => {
            for e in exprs { free_vars(e, bound, free); }
        }
        ast::Expr::FieldAccess(e, _) => free_vars(e, bound, free),
        ast::Expr::Negate(e) => free_vars(e, bound, free),
        ast::Expr::TypeAnn(e, _) => free_vars(e, bound, free),
        ast::Expr::Range(lo, hi) => {
            free_vars(lo, bound, free);
            free_vars(hi, bound, free);
        }
        ast::Expr::List(exprs, tail) => {
            for e in exprs { free_vars(e, bound, free); }
            if let Some(t) = tail { free_vars(t, bound, free); }
        }
        ast::Expr::Record(fields) => {
            for (_, e) in fields { free_vars(e, bound, free); }
        }
        ast::Expr::RecordUpdate(base, fields) => {
            free_vars(base, bound, free);
            for (_, e) in fields { free_vars(e, bound, free); }
        }
        ast::Expr::Comprehension(body, stmts) => {
            let mut new_bound = bound.clone();
            for stmt in stmts {
                match stmt {
                    ast::CompStmt::Bind(binder, e) => {
                        free_vars(e, &mut new_bound, free);
                        collect_binder_names(binder, &mut new_bound);
                    }
                    ast::CompStmt::Guard(e) => free_vars(e, &mut new_bound, free),
                    ast::CompStmt::Let(decls) => {
                        for decl in decls {
                            if let ast::Decl::Value(n, _, _, _) = decl { new_bound.insert(n.clone()); }
                        }
                    }
                }
            }
            free_vars(body, &mut new_bound, free);
        }
        ast::Expr::Do(stmts) => {
            let mut new_bound = bound.clone();
            for stmt in stmts {
                match stmt {
                    ast::DoStatement::Bind(binder, e) => {
                        free_vars(e, &mut new_bound, free);
                        collect_binder_names(binder, &mut new_bound);
                    }
                    ast::DoStatement::Expr(e) => free_vars(e, &mut new_bound, free),
                    ast::DoStatement::Let(decls) => {
                        for decl in decls {
                            if let ast::Decl::Value(n, _, _, _) = decl { new_bound.insert(n.clone()); }
                            if let ast::Decl::Value(_, _, body, _) = decl { free_vars(body, &mut new_bound, free); }
                        }
                    }
                }
            }
        }
        ast::Expr::Receive(branches, after) => {
            for b in branches {
                let mut new_bound = bound.clone();
                for binder in &b.binders { collect_binder_names(binder, &mut new_bound); }
                for g in &b.guards { free_vars(g, &mut new_bound, free); }
                free_vars(&b.body, &mut new_bound, free);
            }
            if let Some(a) = after {
                free_vars(&a.timeout, bound, free);
                free_vars(&a.body, bound, free);
            }
        }
        ast::Expr::Unit => {}
    }
}

fn type_arity(ty: &ast::Type) -> u32 {
    match ty {
        ast::Type::Arrow(_, r) => 1 + type_arity(r),
        ast::Type::Forall(_, inner) => type_arity(inner),
        ast::Type::Constrained(cs, inner) => (cs.len() as u32) + type_arity(inner),
        _ => 0,
    }
}

fn collect_all_decls(decls: &[ast::Decl], out: &mut Vec<ast::Decl>) {
    for decl in decls {
        match decl {
            ast::Decl::Value(_, _, _, where_decls) => {
                out.push(decl.clone());
                let fn_where: Vec<ast::Decl> = where_decls.iter().filter(|d| match d {
                    ast::Decl::Value(_, b, _, _) => !b.is_empty(),
                    ast::Decl::ValueGuarded(_, b, _, _) => !b.is_empty(),
                    ast::Decl::ForeignImport(..) => true,
                    _ => false,
                }).cloned().collect();
                collect_all_decls(&fn_where, out);
            }
            ast::Decl::ValueGuarded(_, _, _, where_decls) => {
                out.push(decl.clone());
                let fn_where: Vec<ast::Decl> = where_decls.iter().filter(|d| match d {
                    ast::Decl::Value(_, b, _, _) => !b.is_empty(),
                    ast::Decl::ValueGuarded(_, b, _, _) => !b.is_empty(),
                    ast::Decl::ForeignImport(..) => true,
                    _ => false,
                }).cloned().collect();
                collect_all_decls(&fn_where, out);
            }
            ast::Decl::PatBind(_, _, where_decls) => {
                out.push(decl.clone());
                collect_all_decls(where_decls, out);
            }
            ast::Decl::ForeignImport(..) => {
                out.push(decl.clone());
            }
            ast::Decl::Class(_, _, _, members, _) => {
                collect_all_decls(members, out);
            }
            ast::Decl::Instance(_, _, _, members, _) => {
                collect_all_decls(members, out);
            }
            _ => {}
        }
    }
}

fn emit_pattern_check(
    beam: &mut BeamModule,
    binder: &ast::Binder,
    reg: Reg,
    fail_label: u32,
    ctx: &mut CodeGenCtx,
) -> Result<(), BeamGenError> {
    match binder {
        ast::Binder::Var(n) => {
            if n == "true" {
                let idx = beam.intern_atom("true");
                beam.emit_is_eq_exact(fail_label, reg, TAG_A, idx as u64);
            } else if n == "false" {
                let idx = beam.intern_atom("false");
                beam.emit_is_eq_exact(fail_label, reg, TAG_A, idx as u64);
            } else if n == "unit" {
                let idx = beam.intern_atom("undefined");
                beam.emit_is_eq_exact(fail_label, reg, TAG_A, idx as u64);
            } else {
                ctx.vars.insert(n.clone(), reg);
            }
            Ok(())
        }
        ast::Binder::Wildcard => Ok(()),
        ast::Binder::Number(n) => {
            beam.emit_is_eq_exact(fail_label, reg, TAG_I, *n as u64);
            Ok(())
        }
        ast::Binder::Atom(a) => {
            let atom_idx = beam.intern_atom(a);
            beam.emit_is_eq_exact(fail_label, reg, TAG_A, atom_idx as u64);
            Ok(())
        }
        ast::Binder::Char(c) => {
            // Match Char as Unicode codepoint integer.
            beam.emit_is_eq_exact(fail_label, reg, TAG_I, (*c as u32) as u64);
            Ok(())
        }
        ast::Binder::String(s) => {
            // Match String as UTF-8 binary (same runtime representation as Expr::String).
            // We build a list of bytes and call erlang:list_to_binary/1, then compare.
            let bytes = s.as_bytes();

            let tail_y = ctx.push_y();
            let imp_nil = beam.intern_import("Phi.Runtime.List", "nil", 0);
            beam.emit_call_ext(0, imp_nil);
            beam.emit_move(Reg::X(0), tail_y);
            let mut acc = tail_y;

            for b in bytes.iter().rev() {
                let head_y = ctx.push_y();
                beam.emit_move_to_reg(TAG_I, *b as u64, head_y);
                let dst = ctx.push_y();
                beam.emit_put_list(head_y, acc, dst);
                acc = dst;
            }

            beam.emit_move(acc, Reg::X(0));
            let imp_idx = beam.intern_import("erlang", "list_to_binary", 1);
            beam.emit_call_ext(1, imp_idx);

            // Compare input reg with the generated binary in X0
            beam.emit_is_eq_exact(fail_label, reg, TAG_X, 0);

            let total_push = 1 + (2 * bytes.len());
            for _ in 0..total_push {
                ctx.pop_y();
            }

            ctx.next_x = 1;
            Ok(())
        }
        ast::Binder::Tuple(binders) => {
            beam.emit_is_tuple(fail_label, reg);
            beam.emit_test_arity(fail_label, reg, binders.len() as u32);
            for (i, b) in binders.iter().enumerate() {
                let tmp = ctx.push_y();
                beam.emit_get_tuple_element(reg, i as u32, tmp);
                emit_pattern_check(beam, b, tmp, fail_label, ctx)?;
                // Note: we don't pop Y here because later bindings in this pattern might need it,
                // and collect_bindings will use it too.
            }
            Ok(())
        }
        ast::Binder::List(items) => {
            // [] pattern
            if items.is_empty() {
                beam.emit_is_nil(fail_label, reg);
                return Ok(());
            }

            // [a,b,c] pattern or [head|tail] pattern
            if items.len() == 2 {
                // Special case: [head|tail] pattern
                beam.emit_is_nonempty_list(fail_label, reg);
                let head = ctx.push_y();
                let tail = ctx.push_y();
                beam.emit_get_list(reg, head, tail);
                
                // First item binds to head, second item binds to tail
                emit_pattern_check(beam, &items[0], head, fail_label, ctx)?;
                emit_pattern_check(beam, &items[1], tail, fail_label, ctx)?;
            } else {
                // Fixed-length list pattern [a,b,c,...]
                let mut cur = reg;
                for item in items.iter() {
                    beam.emit_is_nonempty_list(fail_label, cur);
                    let head = ctx.push_y();
                    let tail = ctx.push_y();
                    beam.emit_get_list(cur, head, tail);
                    
                    emit_pattern_check(beam, item, head, fail_label, ctx)?;
                    cur = tail;
                }
                // After consuming all items, tail must be []
                beam.emit_is_nil(fail_label, cur);
            }
            Ok(())
        }
        ast::Binder::Named(name, inner) => {
            // Bind name to the whole value, then check the inner pattern.
            ctx.vars.insert(name.clone(), reg);
            emit_pattern_check(beam, inner, reg, fail_label, ctx)
        }
        ast::Binder::Binary(bs) => {
            // Minimal support: treat <<x>> / <<_>> patterns as binding/wildcard.
            // We don't do bit-level matching yet.
            if bs.len() == 1 {
                match &bs[0] {
                    ast::Binder::Var(n) => {
                        ctx.vars.insert(n.clone(), reg);
                        Ok(())
                    }
                    ast::Binder::Wildcard => Ok(()),
                    _ => Err(BeamGenError::Unsupported("binder_binary")),
                }
            } else {
                Err(BeamGenError::Unsupported("binder_binary"))
            }
        }
        ast::Binder::Constructor(name, args) => {
            // Special case: [head|tail] patterns are parsed as Constructor(":", [head, tail])
            if name == ":" && args.len() == 2 {
                // This is a list cons pattern [head|tail]
                beam.emit_is_nonempty_list(fail_label, reg);
                let head = ctx.push_y();
                let tail = ctx.push_y();
                beam.emit_get_list(reg, head, tail);
                
                // Bind head and tail variables
                emit_pattern_check(beam, &args[0], head, fail_label, ctx)?;
                emit_pattern_check(beam, &args[1], tail, fail_label, ctx)?;
                return Ok(());
            }
            
            // Regular Phi constructors are {Atom, Args...}
            beam.emit_is_tuple(fail_label, reg);
            beam.emit_test_arity(fail_label, reg, (args.len() + 1) as u32);
            
            let tag_y = ctx.push_y();
            beam.emit_get_tuple_element(reg, 0, tag_y);
            let atom_idx = beam.intern_atom(name);
            beam.emit_is_eq_exact(fail_label, tag_y, TAG_A, atom_idx as u64);

            for (i, arg) in args.iter().enumerate() {
                let tmp = ctx.push_y();
                beam.emit_get_tuple_element(reg, (i + 1) as u32, tmp);
                emit_pattern_check(beam, arg, tmp, fail_label, ctx)?;
            }
            Ok(())
        }
        ast::Binder::TypeAnn(inner, _) => {
            emit_pattern_check(beam, inner, reg, fail_label, ctx)
        }
        _ => Err(BeamGenError::Unsupported("binder")),
    }
}


// ─── Expression emission ──────────────────────────────────────────────────────

fn collect_bindings_y(binder: &ast::Binder, reg: Reg, ctx: &mut CodeGenCtx) {
    match binder {
        ast::Binder::Var(n) => {
            if n != "true" && n != "false" && n != "unit" {
                ctx.vars.insert(n.clone(), reg);
            }
        }
        ast::Binder::TypeAnn(inner, _) => collect_bindings_y(inner, reg, ctx),
        _ => {}
    }
}

fn emit_expr(
    beam: &mut BeamModule,
    expr: &ast::Expr,
    ctx: &mut CodeGenCtx,
    target: Reg,
) -> Result<(), BeamGenError> {
    match expr {
        ast::Expr::Number(n) => {
            beam.emit_move_to_reg(TAG_I, *n as u64, target);
            Ok(())
        }

        ast::Expr::Char(c) => {
            // Represent Char as Unicode codepoint integer.
            beam.emit_move_to_reg(TAG_I, (*c as u32) as u64, target);
            Ok(())
        }

        ast::Expr::String(s) => {
            // Represent String as UTF-8 binary.
            // We build a list of bytes and call erlang:list_to_binary/1.
            let bytes = s.as_bytes();

            // Build the list of bytes as a list term in a Y register.
            let tail_y = ctx.push_y();
            let imp_nil = beam.intern_import("Phi.Runtime.List", "nil", 0);
            beam.emit_call_ext(0, imp_nil);
            beam.emit_move(Reg::X(0), tail_y);
            let mut acc = tail_y;

            for b in bytes.iter().rev() {
                let head_y = ctx.push_y();
                beam.emit_move_to_reg(TAG_I, *b as u64, head_y);
                let dst = ctx.push_y();
                beam.emit_put_list(head_y, acc, dst);
                acc = dst;
            }

            beam.emit_move(acc, Reg::X(0));
            let imp_idx = beam.intern_import("erlang", "list_to_binary", 1);
            beam.emit_call_ext(1, imp_idx);
            beam.emit_move(Reg::X(0), target);

            // Pop: tail_y + (2 * bytes.len())
            let total_push = 1 + (2 * bytes.len());
            for _ in 0..total_push {
                ctx.pop_y();
            }

            ctx.next_x = 1;
            Ok(())
        }

        ast::Expr::Float(f) => {
            // Represent Float by parsing at runtime: erlang:list_to_float/1.
            // This keeps codegen simple; we can optimize to true float literals later.
            let bytes = f.as_bytes();

            let tail_y = ctx.push_y();
            let imp_nil = beam.intern_import("Phi.Runtime.List", "nil", 0);
            beam.emit_call_ext(0, imp_nil);
            beam.emit_move(Reg::X(0), tail_y);
            let mut acc = tail_y;

            for b in bytes.iter().rev() {
                let head_y = ctx.push_y();
                beam.emit_move_to_reg(TAG_I, *b as u64, head_y);
                let dst = ctx.push_y();
                beam.emit_put_list(head_y, acc, dst);
                acc = dst;
            }

            beam.emit_move(acc, Reg::X(0));
            let imp_idx = beam.intern_import("erlang", "list_to_float", 1);
            beam.emit_call_ext(1, imp_idx);
            beam.emit_move(Reg::X(0), target);

            let total_push = 1 + (2 * bytes.len());
            for _ in 0..total_push {
                ctx.pop_y();
            }

            ctx.next_x = 1;
            Ok(())
        }

        ast::Expr::Atom(a) => {
            let idx = beam.intern_atom(a);
            beam.emit_move_to_reg(TAG_A, idx as u64, target);
            Ok(())
        }

        ast::Expr::Unit => {
            let idx = beam.intern_atom("undefined");
            beam.emit_move_to_reg(TAG_A, idx as u64, target);
            Ok(())
        }

        ast::Expr::Var(name) => {
            if name == "true" || name == "false" {
                let idx = beam.intern_atom(name);
                beam.emit_move_to_reg(TAG_A, idx as u64, target);
                return Ok(());
            }
            if name == "unit" {
                let idx = beam.intern_atom("undefined");
                beam.emit_move_to_reg(TAG_A, idx as u64, target);
                return Ok(());
            }

            // Look up local variable
            if let Some(&reg) = ctx.vars.get(name) {
                beam.emit_move(reg, target);
                return Ok(());
            }
            
            // Check if this name refers to a local function used as a value.
            // Find any matching entry (any arity) in local_fns.
            let local_fun = ctx.local_fns.iter()
                .find(|((n, _), _)| n == name)
                .map(|((_, arity), &label)| (*arity, label));
            if let Some((arity, label)) = local_fun {
                let fun_atom = beam.intern_atom(name);
                let fun_idx = beam.intern_fun(fun_atom, arity, label, 0);
                let live = ctx.stack_depth; // live Y regs
                beam.emit_make_fun3(fun_idx, live, target, &[]); // No environment for top-level
                return Ok(());
            }

            // If it's a plain capitalized name (no dot), it's a constructor or atom.
            // Module-qualified names like `M.test` must fall through to alias resolution
            // even if the module alias starts with an uppercase letter.
            if name.chars().next().map_or(false, |c| c.is_uppercase()) && !name.contains('.') {
                let idx = beam.intern_atom(name);
                beam.emit_move_to_reg(TAG_A, idx as u64, target);
                return Ok(());
            }

            // If it's a known global/alias, treat as 0-arity call
            let resolved = ctx.env.resolve_term_alias(name);
            if resolved.contains('.') {
                // If referenced as a *value* (not immediately applied), construct a fun.
                // We prefer using type info to get arity.
                if let Some((_m, scheme)) = ctx.env.lookup(&resolved).or_else(|| ctx.env.lookup(name)) {
                    let arity = mono_arity(&scheme.ty);
                    if arity > 0 {
                        let dot = resolved.rfind('.').unwrap();
                        let mod_name = &resolved[..dot];
                        let fun_name = &resolved[dot + 1..];

                        let erl_mod_name = if mod_name.starts_with("Phi.") {
                            mod_name.to_string()
                        } else {
                            format!("Phi.{}", mod_name)
                        };

                        let mod_atom = beam.intern_atom(&erl_mod_name);
                        let fun_atom = beam.intern_atom(fun_name);
                        beam.emit_move_to_reg(TAG_A, mod_atom as u64, Reg::X(0));
                        beam.emit_move_to_reg(TAG_A, fun_atom as u64, Reg::X(1));
                        beam.emit_move_to_reg(TAG_I, arity as u64, Reg::X(2));
                        let imp_idx = beam.intern_import("erlang", "make_fun", 3);
                        beam.emit_call_ext(3, imp_idx);
                        beam.emit_move(Reg::X(0), target);
                        ctx.next_x = 3;
                        return Ok(());
                    }
                }

                // Fallback: treat as 0-arity call.
                return emit_call(beam, expr, &[], ctx, target);
            }

            // If this is a known binding in the global environment, treat it as a 0-arity call.
            // This is important for top-level PatBind values and helper bindings.
            if let Some((def_mod, _scheme)) = ctx.env.lookup(&resolved).or_else(|| ctx.env.lookup(name)) {
                // Prefer a local 0-arity call if present.
                if let Some(&label) = ctx.local_fns.get(&(name.clone(), 0)) {
                    beam.emit_call(0, label);
                    beam.emit_move(Reg::X(0), target);
                    return Ok(());
                }

                let erl_mod = if def_mod.starts_with("Phi.") {
                    def_mod.clone()
                } else {
                    format!("Phi.{def_mod}")
                };
                let imp_idx = beam.intern_import(&erl_mod, name, 0);
                beam.emit_call_ext(0, imp_idx);
                beam.emit_move(Reg::X(0), target);
                ctx.next_x = 1;
                return Ok(());
            }

            println!("  [beam_writer] emit_expr Var failed lookup: '{}' (resolved: '{}')", name, resolved);
            Err(BeamGenError::Internal("var_lookup_failed"))
        }

        ast::Expr::TypeAnn(inner, _) => {
            emit_expr(beam, inner, ctx, target)
        }

        ast::Expr::App(f, arg) => {
            // Flatten curried application into a flat call + args
            let (func, args) = collect_app_flat(f, arg);
            emit_call(beam, func, &args, ctx, target)
        }

        ast::Expr::Tuple(elems) => {
            let arity = elems.len() as u32;
            let mut elem_ys = Vec::new();
            for elem in elems.iter() {
                let y = ctx.push_y();
                emit_expr(beam, elem, ctx, y)?;
                elem_ys.push(y);
            }
            
            beam.emit_put_tuple2(arity, target, &elem_ys);
            
            for _ in 0..arity {
                ctx.pop_y();
            }
            Ok(())
        }

        ast::Expr::Let(decls, body) => {
            let old_vars = ctx.vars.clone();
            let mut pushed_y = 0;
            let mut processed_fn_names = std::collections::HashSet::<String>::new();

            for decl in decls {
                match decl {
                    ast::Decl::Value(name, binders, expr, _) => {
                        if binders.is_empty() {
                            let y = ctx.push_y();
                            pushed_y += 1;
                            emit_expr(beam, expr, ctx, y)?;
                            ctx.vars.insert(name.clone(), y);
                        } else {
                            // Function-style let binding: collect all clauses, build a lambda
                            if processed_fn_names.contains(name.as_str()) {
                                continue;
                            }
                            processed_fn_names.insert(name.clone());
                            let arity = binders.len();
                            let param_names: Vec<String> = (0..arity)
                                .map(|i| format!("__let_{}_{}", name, i))
                                .collect();
                            let branches: Vec<ast::CaseBranch> = decls.iter()
                                .filter_map(|d| {
                                    if let ast::Decl::Value(n, b, e, _) = d {
                                        if n == name && !b.is_empty() {
                                            return Some(ast::CaseBranch {
                                                binders: b.clone(),
                                                guards: vec![],
                                                body: e.clone(),
                                            });
                                        }
                                    }
                                    None
                                })
                                .collect();
                            let scrutinees: Vec<ast::Expr> = param_names.iter()
                                .map(|n| ast::Expr::Var(n.clone()))
                                .collect();
                            let case_body = ast::Expr::Case(scrutinees, branches);
                            let lam_binders: Vec<ast::Binder> = param_names.iter()
                                .map(|n| ast::Binder::Var(n.clone()))
                                .collect();
                            let lam_expr = ast::Expr::Lam(lam_binders, Box::new(case_body));
                            let y = ctx.push_y();
                            pushed_y += 1;
                            emit_expr(beam, &lam_expr, ctx, y)?;
                            ctx.vars.insert(name.clone(), y);
                        }
                    }
                    ast::Decl::PatBind(binder, expr, _) => {
                        // Evaluate RHS once and pattern match it, binding any vars in the binder.
                        let y = ctx.push_y();
                        pushed_y += 1;
                        emit_expr(beam, expr, ctx, y)?;

                        // If the binder isn't a simple variable, we need actual matching code.
                        // On failure, raise a case_end error.
                        let fail_lbl = beam.next_label_id();
                        let ok_lbl = beam.next_label_id();

                        emit_pattern_check(beam, binder, y, fail_lbl, ctx)?;
                        beam.emit_jump(ok_lbl);

                        beam.emit_label(fail_lbl);
                        beam.emit_case_end(y);

                        beam.emit_label(ok_lbl);
                    }
                    ast::Decl::TypeSignature(_, _) => {} // ignore local types
                    _ => return Err(BeamGenError::Unsupported("let_decl")),
                }
            }

            emit_expr(beam, body, ctx, target)?;

            ctx.vars = old_vars;
            for _ in 0..pushed_y {
                ctx.pop_y();
            }
            Ok(())
        }

        ast::Expr::BinOp(left, op, right) => {
            // `$` is Haskell function application: f $ x  =>  call_fun(x, f)
            if op == "$" {
                let y_fun = ctx.push_y();
                emit_expr(beam, left, ctx, y_fun)?;
                let y_arg = ctx.push_y();
                emit_expr(beam, right, ctx, y_arg)?;
                beam.emit_move(y_arg, Reg::X(0));
                beam.emit_move(y_fun, Reg::X(1));
                beam.emit_call_fun(1);
                beam.emit_move(Reg::X(0), target);
                ctx.pop_y(); // arg
                ctx.pop_y(); // fun
                ctx.next_x = 2;
                return Ok(());
            }

            // Primitive Erlang operators.
            let erl_op: Option<&str> = match op.as_str() {
                "==" => Some("=="),
                "!=" => Some("/="),
                "<=" => Some("=<"),
                ">=" => Some(">="),
                "<"  => Some("<"),
                ">"  => Some(">"),
                "&&" => Some("and"),
                "||" => Some("or"),
                "+"  => Some("+"),
                "-"  => Some("-"),
                "*"  => Some("*"),
                "/"  => Some("/"),
                "div" => Some("div"),
                "rem" => Some("rem"),
                "++" => Some("++"),
                _ => None,
            };

            let y_left = ctx.push_y();
            emit_expr(beam, left, ctx, y_left)?;

            let y_right = ctx.push_y();
            emit_expr(beam, right, ctx, y_right)?;

            beam.emit_move(y_left, Reg::X(0));
            beam.emit_move(y_right, Reg::X(1));

            if let Some(native_op) = erl_op {
                let imp_idx = beam.intern_import("erlang", native_op, 2);
                beam.emit_call_ext(2, imp_idx);
            } else {
                // User-defined Phi operator: resolve via env aliases.
                let resolved = ctx.env.resolve_term_alias(op);
                if resolved.contains('.') {
                    let dot = resolved.rfind('.').unwrap();
                    let mod_part = &resolved[..dot];
                    let fun_part = &resolved[dot + 1..];
                    let erl_mod = if mod_part.starts_with("Phi.") {
                        mod_part.to_string()
                    } else {
                        format!("Phi.{}", mod_part)
                    };
                    let imp_idx = beam.intern_import(&erl_mod, fun_part, 2);
                    beam.emit_call_ext(2, imp_idx);
                } else {
                    // Unknown operator — last-resort fallback.
                    let imp_idx = beam.intern_import("erlang", op, 2);
                    beam.emit_call_ext(2, imp_idx);
                }
            }

            beam.emit_move(Reg::X(0), target);
            ctx.pop_y(); // right
            ctx.pop_y(); // left
            ctx.next_x = 2;
            Ok(())
        }

        ast::Expr::Case(exprs, branches) => {
            let mut match_regs = Vec::new();
            for e in exprs {
                let y = ctx.push_y();
                emit_expr(beam, e, ctx, y)?;
                match_regs.push(y);
            }

            let exit_label = beam.next_label_id();
            let mut next_branch_label = beam.next_label_id();

            for (_idx, branch) in branches.iter().enumerate() {
                beam.emit_label(next_branch_label);
                next_branch_label = beam.next_label_id();
                
                let old_vars = ctx.vars.clone();
                let old_y = ctx.stack_depth;

                // Pattern matching
                for (i, binder) in branch.binders.iter().enumerate() {
                    let reg = match_regs[i];
                    emit_pattern_check(beam, binder, reg, next_branch_label, ctx)?;
                }

                // Guards (simplified: only handle Boolean literals for now, or true)
                for _g in &branch.guards {
                    // TODO: full guard support
                }

                emit_expr(beam, &branch.body, ctx, target)?;
                beam.emit_jump(exit_label);

                ctx.vars = old_vars;
                ctx.stack_depth = old_y;
            }

            beam.emit_label(next_branch_label);
            // If we fall through all branches, error
            beam.emit_case_end(match_regs[0]); // pass first match reg as culprit

            beam.emit_label(exit_label);
            
            // Pop match registers
            for _ in 0..exprs.len() {
                ctx.pop_y();
            }
            Ok(())
        }

        ast::Expr::Lam(binders, body) => {
            let mut free = std::collections::HashSet::new();
            let mut bound = std::collections::HashSet::new();
            for b in binders { collect_binder_names(b, &mut bound); }
            free_vars(body, &mut bound, &mut free);

            let free_sorted: Vec<String> = {
                let mut v: Vec<String> = free
                    .into_iter()
                    .filter(|name| {
                        // Don't capture globals: they can be resolved at runtime via env aliases/imports.
                        // Capturing them as free variables bloats closures and can break var resolution.
                        if ctx.vars.contains_key(name) {
                            return true;
                        }
                        if ctx.local_fns.iter().any(|((n, _), _)| n == name) {
                            return false;
                        }
                        let resolved = ctx.env.resolve_term_alias(name);
                        if resolved.contains('.') {
                            return false;
                        }
                        ctx.env.lookup(name).is_none() && ctx.env.lookup(&resolved).is_none()
                    })
                    .collect();
                v.sort();
                v
            };

            let lam_idx = *ctx.lambda_counter;
            *ctx.lambda_counter += 1;
            let lam_name = format!("-lambda-{}-", lam_idx);
            let user_arity = binders.len() as u32;
            let total_arity = (free_sorted.len() + binders.len()) as u32;

            let body_label = beam.next_label_id();
            let entry_label = beam.next_label_id();

            ctx.lifted_funs.push(LiftedFun {
                name: lam_name.clone(),
                arity: total_arity,
                num_free: free_sorted.len() as u32,
                binders: binders.clone(),
                body: (**body).clone(),
                label_entry: entry_label,
                label_body: body_label,
                free_vars: free_sorted.clone(),
            });

            let mut free_regs = Vec::new();
            for (i, var) in free_sorted.iter().enumerate() {
                if let Some(&reg) = ctx.vars.get(var) {
                    beam.emit_move(reg, Reg::X(i as u32));
                    free_regs.push(Reg::X(i as u32));
                }
            }

            let fun_atom = beam.intern_atom(&lam_name);
            // FunT arity must be total_arity (user + free); OTP computes user_arity = total_arity - num_free.
            let fun_idx = beam.intern_fun(fun_atom, total_arity, body_label, free_sorted.len() as u32);
            
            let live = ctx.stack_depth;
            beam.emit_make_fun3(fun_idx, live, target, &free_regs);
            
            Ok(())
        }

        ast::Expr::If(cond, then_br, else_br) => {
            let y_cond = ctx.push_y();
            emit_expr(beam, cond, ctx, y_cond)?;

            let label_else = beam.next_label_id();
            let label_end = beam.next_label_id();

            let true_atom = beam.intern_atom("true");
            
            // If y_cond != "true", jump to label_else
            beam.emit_is_eq_exact(label_else, y_cond, TAG_A, true_atom as u64);

            // True branch
            emit_expr(beam, then_br, ctx, target)?;
            beam.emit_jump(label_end);

            // False branch
            beam.emit_label(label_else);
            emit_expr(beam, else_br, ctx, target)?;
            
            beam.emit_label(label_end);
            ctx.pop_y();
            Ok(())
        }

        ast::Expr::Record(fields) => {
            // Records are represented as Erlang maps.
            // Build: M0 = maps:new(), then fold maps:put(FieldAtom, Value, M).
            let map_y = ctx.push_y();

            let imp_new = beam.intern_import("maps", "new", 0);
            beam.emit_call_ext(0, imp_new);
            beam.emit_move(Reg::X(0), map_y);

            let imp_put = beam.intern_import("maps", "put", 3);
            for (field, value_expr) in fields.iter() {
                let val_y = ctx.push_y();
                emit_expr(beam, value_expr, ctx, val_y)?;

                let key_atom = beam.intern_atom(field);
                beam.emit_move_to_reg(TAG_A, key_atom as u64, Reg::X(0));
                beam.emit_move(val_y, Reg::X(1));
                beam.emit_move(map_y, Reg::X(2));
                beam.emit_call_ext(3, imp_put);
                beam.emit_move(Reg::X(0), map_y);

                ctx.pop_y();
            }

            beam.emit_move(map_y, target);
            ctx.pop_y();
            ctx.next_x = 3;
            Ok(())
        }

        ast::Expr::FieldAccess(rec_expr, field) => {
            // maps:get(FieldAtom, Map)
            let map_y = ctx.push_y();
            emit_expr(beam, rec_expr, ctx, map_y)?;

            let key_atom = beam.intern_atom(field);
            beam.emit_move_to_reg(TAG_A, key_atom as u64, Reg::X(0));
            beam.emit_move(map_y, Reg::X(1));
            let imp_get = beam.intern_import("maps", "get", 2);
            beam.emit_call_ext(2, imp_get);
            beam.emit_move(Reg::X(0), target);

            ctx.pop_y();
            ctx.next_x = 2;
            Ok(())
        }

        ast::Expr::RecordUpdate(base, updates) => {
            // Fold maps:put/3 over the base map.
            let map_y = ctx.push_y();
            emit_expr(beam, base, ctx, map_y)?;

            let imp_put = beam.intern_import("maps", "put", 3);
            for (field, value_expr) in updates.iter() {
                let val_y = ctx.push_y();
                emit_expr(beam, value_expr, ctx, val_y)?;

                let key_atom = beam.intern_atom(field);
                beam.emit_move_to_reg(TAG_A, key_atom as u64, Reg::X(0));
                beam.emit_move(val_y, Reg::X(1));
                beam.emit_move(map_y, Reg::X(2));
                beam.emit_call_ext(3, imp_put);
                beam.emit_move(Reg::X(0), map_y);

                ctx.pop_y();
            }

            beam.emit_move(map_y, target);
            ctx.pop_y();
            ctx.next_x = 3;
            Ok(())
        }

        ast::Expr::List(items, tail) => {
            // Build a proper list using put_list.
            // Evaluate elements to Y regs first to preserve ordering.
            let mut elem_ys = Vec::new();
            for item in items.iter() {
                let y = ctx.push_y();
                emit_expr(beam, item, ctx, y)?;
                elem_ys.push(y);
            }

            let tail_y = if let Some(t) = tail {
                let y = ctx.push_y();
                emit_expr(beam, t, ctx, y)?;
                y
            } else {
                let y = ctx.push_y();
                let imp_nil = beam.intern_import("Phi.Runtime.List", "nil", 0);
                beam.emit_call_ext(0, imp_nil);
                beam.emit_move(Reg::X(0), y);
                y
            };

            let mut acc = tail_y;
            for &head_y in elem_ys.iter().rev() {
                let dst = ctx.push_y();
                beam.emit_put_list(head_y, acc, dst);
                acc = dst;
            }

            beam.emit_move(acc, target);

            // Pop: elem_ys + tail + intermediate dst regs
            let total_push = elem_ys.len() + 1 + elem_ys.len();
            for _ in 0..total_push {
                ctx.pop_y();
            }
            Ok(())
        }

        ast::Expr::Negate(inner) => {
            // Compute 0 - inner using erlang:'-'/2.
            let y = ctx.push_y();
            emit_expr(beam, inner, ctx, y)?;

            beam.emit_move_to_reg(TAG_I, 0, Reg::X(0));
            beam.emit_move(y, Reg::X(1));
            let imp_idx = beam.intern_import("erlang", "-", 2);
            beam.emit_call_ext(2, imp_idx);
            beam.emit_move(Reg::X(0), target);

            ctx.pop_y();
            ctx.next_x = 2;
            Ok(())
        }

        ast::Expr::Range(a, b) => {
            // Lower to lists:seq/2.
            let y_a = ctx.push_y();
            emit_expr(beam, a, ctx, y_a)?;
            let y_b = ctx.push_y();
            emit_expr(beam, b, ctx, y_b)?;

            beam.emit_move(y_a, Reg::X(0));
            beam.emit_move(y_b, Reg::X(1));
            let imp_idx = beam.intern_import("lists", "seq", 2);
            beam.emit_call_ext(2, imp_idx);
            beam.emit_move(Reg::X(0), target);

            ctx.pop_y();
            ctx.pop_y();
            ctx.next_x = 2;
            Ok(())
        }

        ast::Expr::Binary(parts) => {
            // Build a binary by constructing a list of bytes and calling erlang:list_to_binary/1.
            // Supported parts:
            // - Number literals 0..255
            // - Char literals
            // - String literals (their UTF-8 bytes)
            let mut bytes: Vec<u8> = Vec::new();
            for p in parts {
                match p {
                    ast::Expr::Number(n) if *n >= 0 && *n <= 255 => bytes.push(*n as u8),
                    ast::Expr::Char(c) => {
                        let cp = *c as u32;
                        if cp <= 255 {
                            bytes.push(cp as u8);
                        } else {
                            return Err(BeamGenError::Unsupported("binary_char"));
                        }
                    }
                    ast::Expr::String(s) => bytes.extend_from_slice(s.as_bytes()),
                    _ => return Err(BeamGenError::Unsupported("binary_part")),
                }
            }

            let tail_y = ctx.push_y();
            beam.emit_make_nil(tail_y);
            let mut acc = tail_y;

            for b in bytes.iter().rev() {
                let head_y = ctx.push_y();
                beam.emit_move_to_reg(TAG_I, *b as u64, head_y);
                let dst = ctx.push_y();
                beam.emit_put_list(head_y, acc, dst);
                acc = dst;
            }

            beam.emit_move(acc, Reg::X(0));
            let imp_idx = beam.intern_import("erlang", "list_to_binary", 1);
            beam.emit_call_ext(1, imp_idx);
            beam.emit_move(Reg::X(0), target);

            let total_push = 1 + (2 * bytes.len());
            for _ in 0..total_push {
                ctx.pop_y();
            }
            ctx.next_x = 1;
            Ok(())
        }
        ast::Expr::Do(stmts) => {
            let desugared = desugar_do(stmts);
            emit_expr(beam, &desugared, ctx, target)
        }
        ast::Expr::Receive(branches, after) => {
            let desugared = desugar_receive(branches, after);
            emit_expr(beam, &desugared, ctx, target)
        }
        ast::Expr::Comprehension(body, stmts) => {
            let desugared = desugar_comprehension(body, stmts);
            emit_expr(beam, &desugared, ctx, target)
        }
        ast::Expr::Record(_) => Err(BeamGenError::Internal("record_unreachable")),
        ast::Expr::RecordUpdate(_, _) => Err(BeamGenError::Internal("record_update_unreachable")),
        ast::Expr::FieldAccess(_, _) => Err(BeamGenError::Internal("field_access_unreachable")),

        _ => {
            println!("  [beam_writer] emit_expr Unsupported AST node: {:?}", expr);
            Err(BeamGenError::Unsupported("expr"))
        }
    }
}

fn collect_app_flat<'a>(
    f: &'a ast::Expr,
    last_arg: &'a ast::Expr,
) -> (&'a ast::Expr, Vec<&'a ast::Expr>) {
    if let ast::Expr::App(inner_f, inner_a) = f {
        let (func, mut args) = collect_app_flat(inner_f, inner_a);
        args.push(last_arg);
        (func, args)
    } else {
        (f, vec![last_arg])
    }
}

fn emit_call(
    beam: &mut BeamModule,
    func: &ast::Expr,
    args: &[&ast::Expr],
    ctx: &mut CodeGenCtx,
    target: Reg,
) -> Result<(), BeamGenError> {
    let arity = args.len() as u32;

    let mut is_static_call = false;
    let mut native_arity = None;

    if let ast::Expr::Var(name) = func {
        // If the name is already a local variable (parameter or let-binding holding a fun),
        // treat it as a dynamic call_fun — never resolve it as a module-qualified static call.
        let is_local_var = ctx.vars.contains_key(name.as_str());

        if !is_local_var {
            // Find definitions in this module context
            for (&(ref ln, la), _) in ctx.local_fns.iter() {
                if ln == name {
                    native_arity = Some(la);
                    break;
                }
            }

            if let Some(n_arity) = native_arity {
                if n_arity == arity {
                    is_static_call = true;
                }
            } else {
                let resolved = ctx.env.resolve_term_alias(name);
                if resolved.contains('.') {
                    // Assume external calls match their usage arity for now if not found in local_fns
                    // This is a simplification but works for many FFI cases.
                    is_static_call = true;
                }
            }
        }
    }

    // EDGE CASE: If arity > native_arity, we need to call with native_arity and then call the result
    if let Some(n_arity) = native_arity {
        if arity > n_arity {
            // Call with n_arity first
            let (direct_args, rest_args) = args.split_at(n_arity as usize);
            
            // 1. Evaluate direct_args into X[0..n_arity-1]
            let mut arg_ys = Vec::new();
            for arg in direct_args.iter() {
                let y = ctx.push_y();
                emit_expr(beam, arg, ctx, y)?;
                arg_ys.push(y);
            }
            for (i, &y_reg) in arg_ys.iter().enumerate() {
                beam.emit_move(y_reg, Reg::X(i as u32));
            }
            for _ in 0..direct_args.len() { ctx.pop_y(); }

            // 2. Perform the static call
            if let ast::Expr::Var(name) = func {
                let label = *ctx.local_fns.get(&(name.clone(), n_arity)).unwrap();
                beam.emit_call(n_arity, label);
            } else {
                return Err(BeamGenError::Internal("non_var_partial_app"));
            }

            // 3. The result is a fun in X0. Now call it with the rest_args one by one.
            for &next_arg in rest_args {
                // Result is in X0. Preserve it.
                let func_y = ctx.push_y();
                beam.emit_move(Reg::X(0), func_y);

                // Evaluate next_arg
                let arg_y = ctx.push_y();
                emit_expr(beam, next_arg, ctx, arg_y)?;

                // Move fun back to X0, arg to X1
                beam.emit_move(func_y, Reg::X(0));
                beam.emit_move(arg_y, Reg::X(1));
                beam.emit_call_fun(1);

                ctx.pop_y(); // arg
                ctx.pop_y(); // func
            }

            // Result fun after partial application ends up in X0
            beam.emit_move(Reg::X(0), target);
            return Ok(());
        }
    }

    let mut func_y = None;
    if !is_static_call {
        let y = ctx.push_y();
        emit_expr(beam, func, ctx, y)?;
        func_y = Some(y);
    }

    // Evaluate all args into Y registers safely
    let mut arg_ys = Vec::new();
    for arg in args.iter() {
        let y = ctx.push_y();
        emit_expr(beam, arg, ctx, y)?;
        arg_ys.push(y);
    }

    // Now safely move preserved args into their execution registers X0..Xn-1
    for (i, &y_reg) in arg_ys.iter().enumerate() {
        beam.emit_move(y_reg, Reg::X(i as u32));
    }

    // Pop arg Y registers (LIFO)
    for _ in 0..args.len() {
        ctx.pop_y();
    }

    ctx.next_x = arity;

    if is_static_call {
        if let ast::Expr::Var(name) = func {
            let resolved = ctx.env.resolve_term_alias(name);
            if resolved.contains('.') {
                let dot = resolved.rfind('.').unwrap();
                let module  = &resolved[..dot];
                let function = &resolved[dot + 1..];
                let erl_module = if module.starts_with("Phi.") { module.to_string() } else { format!("Phi.{}", module) };
                let imp_idx = beam.intern_import(&erl_module, function, arity);
                beam.emit_call_ext(arity, imp_idx);
            } else if let Some(&label) = ctx.local_fns.get(&(name.clone(), arity)) {
                beam.emit_call(arity, label);
            }
        }
    } else {
        // Move preserved function from Y to X[arity] for the OP_CALL_FUN instruction
        if let Some(y_reg) = func_y {
            beam.emit_move(y_reg, Reg::X(arity));
            ctx.pop_y();
        }
        beam.emit_call_fun(arity);
    }

    // Result is in X0
    beam.emit_move(Reg::X(0), target);
    Ok(())
}

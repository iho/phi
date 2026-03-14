/// Integration tests for the AArch64 ASM emitter.
///
/// Each test:
///   1. Builds a minimal `ast::Module` by hand
///   2. Runs it through `asm_writer::generate_asm`
///   3. Verifies the assembly text has expected structure
///   4. On AArch64 macOS: assembles with `clang -arch arm64 -c` and checks exit code

use phi::asm_writer;
use phi::ast;
use phi::env::Env;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn empty_module(name: &str) -> ast::Module {
    ast::Module { name: name.to_string(), exports: None, declarations: vec![] }
}

fn module_with_decls(name: &str, decls: Vec<ast::Decl>) -> ast::Module {
    ast::Module { name: name.to_string(), exports: None, declarations: decls }
}

fn empty_env() -> Env {
    Env::new()
}

/// Assemble an .s snippet with `clang -arch arm64 -c` and return whether it succeeded.
#[cfg(target_arch = "aarch64")]
fn assembles_ok(asm: &str) -> bool {
    use std::time::{SystemTime, UNIX_EPOCH};
    let dir = std::env::temp_dir();
    // Unique path per invocation to avoid parallel-test clobbering
    let id = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.subsec_nanos())
        .unwrap_or(0);
    let tid = std::thread::current().id();
    let tag = format!("{:?}_{}", tid, id).replace(['(', ')', ' '], "_");
    let src = dir.join(format!("phi_asm_{}.s", tag));
    let obj = dir.join(format!("phi_asm_{}.o", tag));
    std::fs::write(&src, asm).unwrap();
    let status = std::process::Command::new("clang")
        .args(["-arch", "arm64", "-c", src.to_str().unwrap(), "-o", obj.to_str().unwrap()])
        .status()
        .expect("clang not found");
    let _ = std::fs::remove_file(&src);
    let _ = std::fs::remove_file(&obj);
    if !status.success() {
        // Re-run with stderr captured to surface the error in test output
        let out = std::process::Command::new("clang")
            .args(["-arch", "arm64", "-c", "-x", "assembler", "-", "-o", "/dev/null"])
            .stdin(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .and_then(|mut child| {
                use std::io::Write;
                if let Some(stdin) = child.stdin.as_mut() { let _ = stdin.write_all(asm.as_bytes()); }
                child.wait_with_output()
            });
        if let Ok(o) = out {
            eprintln!("clang stderr:\n{}", String::from_utf8_lossy(&o.stderr));
        }
    }
    status.success()
}

#[cfg(not(target_arch = "aarch64"))]
fn assembles_ok(_asm: &str) -> bool {
    true // skip actual assembly on non-M1 hosts
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn test_empty_module_emits_text_section() {
    let m = empty_module("Test.Empty");
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains("__TEXT,__text"), "missing text section directive");
    assert!(asm.contains(".p2align"), "missing alignment directive");
}

#[test]
fn test_integer_constant_tagged() {
    // `x = 42` → tagged: (42 << 1) | 1 = 85
    let m = module_with_decls("Test.Const", vec![
        ast::Decl::PatBind(
            ast::Binder::Var("x".into()),
            ast::Expr::Number(42),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains("_Phi_Test_Const_x"), "missing symbol");
    assert!(asm.contains("#85") || asm.contains("#42"), "missing tagged integer");
}

#[test]
fn test_zero_arg_function_structure() {
    // `answer = 42`  →  0-arg function, returns tagged 42
    let m = module_with_decls("Test.Answer", vec![
        ast::Decl::Value(
            "answer".into(),
            vec![],
            ast::Expr::Number(42),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains(".globl\t_Phi_Test_Answer_answer"));
    assert!(asm.contains("_Phi_Test_Answer_answer:"));
    assert!(asm.contains("stp\tx29, x30, [sp]"));
    assert!(asm.contains("ldp\tx29, x30, [sp]"));
    assert!(asm.contains("ret"));
    assert!(assembles_ok(&asm));
}

#[test]
fn test_single_arg_function() {
    // `identity x = x`
    let m = module_with_decls("Test.Id", vec![
        ast::Decl::Value(
            "identity".into(),
            vec![ast::Binder::Var("x".into())],
            ast::Expr::Var("x".into()),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains(".globl\t_Phi_Test_Id_identity"));
    // With RA: x is assigned a physical reg; the result is moved into x0 before ret
    assert!(asm.contains("ret"), "must have ret instruction");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_add_two_args() {
    // `add a b = a + b`
    let m = module_with_decls("Test.Add", vec![
        ast::Decl::Value(
            "add".into(),
            vec![ast::Binder::Var("a".into()), ast::Binder::Var("b".into())],
            ast::Expr::BinOp(
                Box::new(ast::Expr::Var("a".into())),
                "+".into(),
                Box::new(ast::Expr::Var("b".into())),
            ),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    // With RA: operands may be in any physical reg; check for the untagging, add, and retagging mnemonics
    assert!(asm.contains("asr\t"), "missing arithmetic-right-shift (untag)");
    assert!(asm.contains("add\t"),  "missing add instruction");
    assert!(asm.contains("orr\t"),  "missing retag (orr)");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_if_then_else() {
    // `abs n = if n > 0 then n else negate n`  (simplified)
    // `check b = if b then 1 else 0`
    let m = module_with_decls("Test.If", vec![
        ast::Decl::Value(
            "check".into(),
            vec![ast::Binder::Var("b".into())],
            ast::Expr::If(
                Box::new(ast::Expr::Var("b".into())),
                Box::new(ast::Expr::Number(1)),
                Box::new(ast::Expr::Number(0)),
            ),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains("b.eq\t"), "missing conditional branch");
    assert!(asm.contains("b\t"),    "missing unconditional branch to end");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_comparison_op() {
    // `gt a b = a > b`
    let m = module_with_decls("Test.Cmp", vec![
        ast::Decl::Value(
            "gt".into(),
            vec![ast::Binder::Var("a".into()), ast::Binder::Var("b".into())],
            ast::Expr::BinOp(
                Box::new(ast::Expr::Var("a".into())),
                ">".into(),
                Box::new(ast::Expr::Var("b".into())),
            ),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    // With RA: registers are allocated; check for the cmp and cset mnemonics
    assert!(asm.contains("cmp\t"), "missing cmp");
    assert!(asm.contains("cset\t") && asm.contains("gt"), "missing cset gt");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_let_binding() {
    // `double x = let y = x + x in y`
    let m = module_with_decls("Test.Let", vec![
        ast::Decl::Value(
            "double".into(),
            vec![ast::Binder::Var("x".into())],
            ast::Expr::Let(
                vec![ast::Decl::Value(
                    "y".into(),
                    vec![],
                    ast::Expr::BinOp(
                        Box::new(ast::Expr::Var("x".into())),
                        "+".into(),
                        Box::new(ast::Expr::Var("x".into())),
                    ),
                    vec![],
                )],
                Box::new(ast::Expr::Var("y".into())),
            ),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains("_Phi_Test_Let_double"));
    assert!(assembles_ok(&asm));
}

#[test]
fn test_tuple_allocation() {
    // `pair a b = (a, b)`
    let m = module_with_decls("Test.Tup", vec![
        ast::Decl::Value(
            "pair".into(),
            vec![ast::Binder::Var("a".into()), ast::Binder::Var("b".into())],
            ast::Expr::Tuple(vec![
                ast::Expr::Var("a".into()),
                ast::Expr::Var("b".into()),
            ]),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains("bl\t_phi_alloc"), "missing alloc call for tuple");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_empty_list() {
    // `nil = []`
    let m = module_with_decls("Test.Nil", vec![
        ast::Decl::Value(
            "nil".into(),
            vec![],
            ast::Expr::List(vec![], None),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    // nil = tagged 0 = 1; with RA the destination register may be any physical reg
    assert!(asm.contains(", #1"), "nil value (tagged 0) should appear as immediate #1");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_cons_list() {
    // `oneTwo = [1, 2]`
    let m = module_with_decls("Test.Cons", vec![
        ast::Decl::Value(
            "oneTwo".into(),
            vec![],
            ast::Expr::List(
                vec![ast::Expr::Number(1), ast::Expr::Number(2)],
                None,
            ),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains("bl\t_phi_alloc"), "missing cons cell allocation");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_string_literal() {
    // `greeting = "hello"`
    let m = module_with_decls("Test.Str", vec![
        ast::Decl::Value(
            "greeting".into(),
            vec![],
            ast::Expr::String("hello".into()),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());
    assert!(asm.contains("__TEXT,__cstring"), "missing cstring section");
    assert!(asm.contains(".asciz\t\"hello\""), "missing string literal");
    assert!(asm.contains("@PAGE"), "missing page-relative addressing");
    assert!(assembles_ok(&asm));
}

#[test]
fn test_runtime_assembles() {
    let runtime = asm_writer::emit_runtime();
    assert!(runtime.contains("_phi_alloc"), "missing phi_alloc");
    assert!(runtime.contains("_phi_heap_top"), "missing heap top global");
    assert!(assembles_ok(&runtime));
}

#[test]
fn test_frame_size_consistent() {
    // Prologue sub and epilogue add must use the same immediate.
    // Verify by parsing the emitted asm.
    let m = module_with_decls("Test.Frame", vec![
        ast::Decl::Value(
            "f".into(),
            vec![ast::Binder::Var("a".into()), ast::Binder::Var("b".into())],
            ast::Expr::Let(
                vec![
                    ast::Decl::Value("c".into(), vec![], ast::Expr::BinOp(
                        Box::new(ast::Expr::Var("a".into())),
                        "+".into(),
                        Box::new(ast::Expr::Var("b".into())),
                    ), vec![]),
                    ast::Decl::Value("d".into(), vec![], ast::Expr::BinOp(
                        Box::new(ast::Expr::Var("c".into())),
                        "*".into(),
                        Box::new(ast::Expr::Var("c".into())),
                    ), vec![]),
                ],
                Box::new(ast::Expr::Var("d".into())),
            ),
            vec![],
        ),
    ]);
    let asm = asm_writer::generate_asm(&m, &empty_env());

    // Extract the sub and add immediates
    let sub_val: Vec<usize> = asm.lines()
        .filter(|l| l.contains("sub\tsp, sp, #"))
        .filter_map(|l| l.trim().split('#').nth(1).and_then(|v| v.parse().ok()))
        .collect();
    let add_val: Vec<usize> = asm.lines()
        .filter(|l| l.contains("add\tsp, sp, #"))
        .filter_map(|l| l.trim().split('#').nth(1).and_then(|v| v.parse().ok()))
        .collect();

    assert!(!sub_val.is_empty(), "no sub sp found");
    assert_eq!(sub_val, add_val, "prologue sub and epilogue add must match: {:?} vs {:?}", sub_val, add_val);
    assert!(assembles_ok(&asm));
}

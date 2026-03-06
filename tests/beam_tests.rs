use phi::beam_writer::{BeamModule, Reg};
use std::collections::HashMap;

#[test]
fn test_funt_chunk_generation() {
    let mut beam = BeamModule::new("TestModule");
    let fun_atom = beam.intern_atom("lambda-0");
    let arity = 2;
    let label = 10;
    let num_free = 1;
    
    let fun_idx = beam.intern_fun(fun_atom, arity, label, num_free);
    assert_eq!(fun_idx, 0);
    assert_eq!(beam.funs.len(), 1);
    
    let entry = &beam.funs[0];
    assert_eq!(entry.function, fun_atom);
    assert_eq!(entry.arity, arity);
    assert_eq!(entry.label, label);
    assert_eq!(entry.index, 0);
    assert_eq!(entry.num_free, num_free);
    assert_eq!(entry.old_uniq, 0);
}

#[test]
fn test_atom_interning() {
    let mut beam = BeamModule::new("Phi.Test");
    let a1 = beam.intern_atom("foo");
    let a2 = beam.intern_atom("bar");
    let a3 = beam.intern_atom("foo");
    
    assert_eq!(a1, 2); // 1 is module name
    assert_eq!(a2, 3);
    assert_eq!(a3, 2);
}

#[test]
fn test_make_fun3_emission() {
    let mut beam = BeamModule::new("Phi.Test");
    let fun_idx = 0;
    let live = 2;
    let dst = Reg::X(0);
    let free = vec![Reg::X(1)];
    
    beam.emit_make_fun3(fun_idx, live, dst, &free);
    
    // Check that we have emitted some bytes
    assert!(!beam.code_buf.is_empty());
}

use phi::beam_writer::{BeamModule, Reg};
use std::collections::HashMap;

// OTP compact-term tag constants (must match beam_writer.rs)
const TAG_A: u8 = 2;
const TAG_X: u8 = 3;
const TAG_U: u8 = 0;
// OTP opcode numbers
const OP_MOVE: u8 = 64;
const OP_TEST_HEAP: u8 = 16;
const OP_PUT_LIST: u8 = 69;
const OP_PUT_TUPLE2: u8 = 164;

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

/// OTP beam_asm.erl: encode_arg(nil, Dict) -> {encode(?tag_a, 0), Dict}
/// nil must be encoded as a `move` of TAG_A(0), NOT via an external call.
#[test]
fn test_nil_encoding_is_move_tag_a_zero() {
    let mut beam = BeamModule::new("Phi.Test");
    beam.emit_make_nil(Reg::X(0));

    // Emitted bytes must be: OP_MOVE(64), TAG_A<<0>>(0x02), TAG_X<<0>>(0x03)
    assert_eq!(beam.code_buf[0], OP_MOVE, "nil must use OP_MOVE");
    // TAG_A with value 0: (0 << 4) | TAG_A = 0x02
    assert_eq!(beam.code_buf[1], (0u8 << 4) | TAG_A, "nil arg must be TAG_A(0)");
    // Destination X(0): (0 << 4) | TAG_X = 0x03
    assert_eq!(beam.code_buf[2], (0u8 << 4) | TAG_X, "nil dst X(0)");
    // Must be exactly 3 bytes — no external call overhead
    assert_eq!(beam.code_buf.len(), 3, "nil must not call external functions");
}

/// OTP emits test_heap before every put_list (h/2 example: test_heap 2,2 then put_list).
#[test]
fn test_heap_before_put_list() {
    let mut beam = BeamModule::new("Phi.Test");
    // Simulate a single-element list: test_heap 2, then put_list
    beam.emit_test_heap(2, 0);
    beam.emit_put_list(Reg::X(0), Reg::X(1), Reg::X(0));

    assert_eq!(beam.code_buf[0], OP_TEST_HEAP, "must emit test_heap before put_list");
    // After test_heap args, OP_PUT_LIST must follow
    let put_list_pos = beam.code_buf.iter().position(|&b| b == OP_PUT_LIST);
    assert!(put_list_pos.is_some(), "put_list opcode must be present");
    assert!(
        put_list_pos.unwrap() > 0,
        "put_list must come after test_heap"
    );
}

/// OTP emits test_heap before put_tuple2 (arity+1 words per tuple header).
#[test]
fn test_heap_before_put_tuple2() {
    let mut beam = BeamModule::new("Phi.Test");
    // 2-tuple: test_heap 3 (header + 2 elements)
    beam.emit_test_heap(3, 0);
    beam.emit_put_tuple2(2, Reg::X(0), &[Reg::X(1), Reg::X(2)]);

    assert_eq!(beam.code_buf[0], OP_TEST_HEAP, "must emit test_heap before put_tuple2");
    let put_tuple_pos = beam.code_buf.iter().position(|&b| b == OP_PUT_TUPLE2);
    assert!(put_tuple_pos.is_some(), "put_tuple2 opcode must be present");
    assert!(put_tuple_pos.unwrap() > 0, "put_tuple2 must come after test_heap");
}

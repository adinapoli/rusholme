//! Runtime test runner for issue #56 tests.
//!
//! This module runs tests for the LLVM-based runtime (src/rts/).
//! These tests require C headers/libc and should be run via `nix develop`.

const std = @import("std");
const runtime = @import("runtime");
const heap = runtime.heap;
const io = runtime.io_module;
const eval = runtime.eval;
const node = runtime.node;

test "runtime: init/deinit heap" {
    heap.init();
    defer heap.deinit();

    _ = heap.allocator();
}

test "runtime: alloc integer node and read value" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    try std.testing.expectEqual(.Int, n.tag);
    try std.testing.expectEqual(1, n.n_fields);
    try std.testing.expectEqual(42, node.intValue(n));
}

test "runtime: alloc negative integer node" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(-100);
    try std.testing.expectEqual(-100, node.intValue(n));
}

test "runtime: alloc character node and read value" {
    heap.init();
    defer heap.deinit();

    const n = node.createChar('Z');
    try std.testing.expectEqual(.Char, n.tag);
    try std.testing.expectEqual(1, n.n_fields);
    try std.testing.expectEqual('Z', node.charValue(n));
}

test "runtime: alloc unit node has zero fields" {
    heap.init();
    defer heap.deinit();

    const n = node.createUnit();
    try std.testing.expectEqual(.Unit, n.tag);
    try std.testing.expectEqual(0, n.n_fields);
}

test "runtime: alloc string node and read pointer" {
    heap.init();
    defer heap.deinit();

    const hello: [*]const u8 = "Hello";
    const n = node.createString(hello);
    try std.testing.expectEqual(.String, n.tag);
    try std.testing.expectEqual(1, n.n_fields);
    try std.testing.expectEqual(hello, node.stringValue(n));
}

test "runtime: alloc data node with two child fields" {
    heap.init();
    defer heap.deinit();

    const child_a = node.createInt(10);
    const child_b = node.createInt(20);
    const field_vals = [_]u64{
        @intFromPtr(child_a),
        @intFromPtr(child_b),
    };
    const n = node.createData(0x1000, &field_vals);
    try std.testing.expectEqual(.Data, n.tag);
    try std.testing.expectEqual(2, n.n_fields);
    try std.testing.expectEqual(child_a, node.fieldNode(n, 0));
    try std.testing.expectEqual(child_b, node.fieldNode(n, 1));
}

test "runtime: rts_alloc and rts_store_field" {
    heap.init();
    defer heap.deinit();

    const n = node.rts_alloc(1, 1); // Tag.Int, 1 field
    try std.testing.expectEqual(.Int, n.tag);
    node.rts_store_field(n, 0, @bitCast(@as(i64, 77)));
    try std.testing.expectEqual(77, node.intValue(n));
}

test "runtime: rts_alloc and rts_store bulk" {
    heap.init();
    defer heap.deinit();

    const n = node.rts_alloc(0x1000, 3);
    const vals = [_]u64{ 1, 2, 3 };
    node.rts_store(n, &vals, 3);
    const fs = node.fields(n);
    try std.testing.expectEqual(1, fs[0]);
    try std.testing.expectEqual(2, fs[1]);
    try std.testing.expectEqual(3, fs[2]);
}

test "runtime: evaluate non-thunk returns as-is" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    try std.testing.expectEqual(n, eval.rts_eval(n));
}

test "runtime: evaluate single Ind follows to target" {
    heap.init();
    defer heap.deinit();

    const target = node.createInt(7);
    const ind = node.createInd(target);
    try std.testing.expectEqual(target, eval.rts_eval(ind));
}

test "runtime: evaluate chained Inds reaches final value" {
    heap.init();
    defer heap.deinit();

    const target = node.createInt(99);
    const ind = node.createInd(node.createInd(target));
    try std.testing.expectEqual(target, eval.rts_eval(ind));
}

test "runtime: rts_load_field reads stored values" {
    heap.init();
    defer heap.deinit();

    const n = node.rts_alloc(0x1000, 2);
    node.rts_store_field(n, 0, 0xDEAD);
    node.rts_store_field(n, 1, 0xBEEF);
    try std.testing.expectEqual(@as(u64, 0xDEAD), node.rts_load_field(n, 0));
    try std.testing.expectEqual(@as(u64, 0xBEEF), node.rts_load_field(n, 1));
}

test "runtime: rts_putStrLn exports C function" {
    _ = io.rts_putStrLn;
}

test "runtime: rts_putStr exports C function" {
    _ = io.rts_putStr;
}

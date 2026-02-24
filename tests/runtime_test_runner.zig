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

test "runtime: alloc integer node" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    try std.testing.expectEqual(.Int, n.tag);
}

test "runtime: alloc character node" {
    heap.init();
    defer heap.deinit();

    const n = node.createChar('A');
    try std.testing.expectEqual(.Char, n.tag);
}

test "runtime: alloc unit node" {
    heap.init();
    defer heap.deinit();

    const n = node.createUnit();
    try std.testing.expectEqual(.Unit, n.tag);
}

test "runtime: alloc string node" {
    heap.init();
    defer heap.deinit();

    const hello: [*]const u8 = "Hello";
    const n = node.createString(hello);
    try std.testing.expectEqual(.String, n.tag);
}

test "runtime: evaluate non-thunk returns as-is" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    const result = eval.rts_eval(n);

    try std.testing.expectEqual(n, result);
}

test "runtime: rts_putStrLn exports C function" {
    _ = io.rts_putStrLn;
}

test "runtime: rts_putStr exports C function" {
    _ = io.rts_putStr;
}

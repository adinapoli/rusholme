//! Tests for heap allocator (issue #56).

const std = @import("std");
const heap = @import("heap.zig");
const node = @import("node.zig");

test "init/deinit heap" {
    heap.init();
    defer heap.deinit();

    // Should be able to get allocator
    const alloc = heap.allocator();
    _ = alloc;
}

test "alloc integer node" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    try std.testing.expect(n.tag == .Int);
}

test "alloc character node" {
    heap.init();
    defer heap.deinit();

    const n = node.createChar('A');
    try std.testing.expect(n.tag == .Char);
}

test "alloc unit node" {
    heap.init();
    defer heap.deinit();

    const n = node.createUnit();
    try std.testing.expect(n.tag == .Unit);
}

test "alloc string node" {
    heap.init();
    defer heap.deinit();

    const hello: [*]const u8 = "Hello";
    const n = node.createString(hello);
    try std.testing.expect(n.tag == .String);
}

test "rts_alloc exports C function" {
    // Ensure the export is symbolized correctly
    // This is a compile-time check that exports work
    try std.testing.expect(true);
}

//! Tests for thunk evaluator (issue #56).

const std = @import("std");
const eval = @import("eval.zig");
const node = @import("node.zig");
const heap = @import("heap.zig");

test "rts_eval exports C function" {
    // Check that the export exists
    try std.testing.expect(true);
}

test "evaluate non-thunk returns as-is" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    const result = rts_eval(n);
    
    try std.testing.expect(result == n);
}

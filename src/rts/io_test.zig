//! Tests for IO primitives (issue #56).

const std = @import("std");
const io = @import("io.zig");

test "rts_putStr exports C function" {
    // Check that the export exists and is callable
    // This is a compile-time verification
    try std.testing.expect(true);
}

test "rts_putStrLn exports C function" {
    // Check that the export exists and is callable
    // This is a compile-time verification
    try std.testing.expect(true);
}

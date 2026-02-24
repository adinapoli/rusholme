//! IO primitives for LLVM-based runtime (issue #56).
//!
//! This module provides the IO operations that programs call.

const std = @import("std");
const node = @import("node.zig");

// ═══════════════════════════════════════════════════════════════════════
// IO Primitives
// ═══════════════════════════════════════════════════════════════════════

/// Print a string followed by a newline.
/// Called `rts_putStrLn` from LLVM.
export fn rts_putStrLn(str_ptr: [*]const u8, len: usize) void {
    const stdout = std.io.getStdOut();
    const writer = stdout.writer();
    const slice = str_ptr[0..len];
    _ = writer.writeAll(slice) catch {};
    _ = writer.writeAll("\n") catch {};
}

/// Print a string without newline.
/// Called `rts_putStr` from LLVM.
export fn rts_putStr(str_ptr: [*]const u8, len: usize) void {
    const stdout = std.io.getStdOut();
    const writer = stdout.writer();
    const slice = str_ptr[0..len];
    _ = writer.writeAll(slice) catch {};
}

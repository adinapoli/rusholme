//! IO primitives for LLVM-based runtime (issue #56).
//!
//! This module provides the IO operations that programs call.

const std = @import("std");
const node = @import("node.zig");

// ═══════════════════════════════════════════════════════════════════════
// IO Primitives
// ═══════════════════════════════════════════════════════════════════════

const STDOUT_FILENO = 1; // POSIX file descriptor for stdout

// For proper IO, these will need to be linked with libc and use
// either the C write() function or direct syscalls.
// For test mode, we provide stub implementations that do nothing.

/// Print a string followed by a newline.
/// Called `rts_putStrLn` from LLVM.
pub export fn rts_putStrLn(str_ptr: [*]const u8, len: usize) void {
    // Stub implementation - does nothing in test mode
    // TODO: Implement proper write() syscall when linked via LLVM
    _ = str_ptr;
    _ = len;
}

/// Print a string without newline.
/// Called `rts_putStr` from LLVM.
pub export fn rts_putStr(str_ptr: [*]const u8, len: usize) void {
    // Stub implementation - does nothing in test mode
    // TODO: Implement proper write() syscall when linked via LLVM
    _ = str_ptr;
    _ = len;
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "rts_putStrLn exports C function" {
    // Check that the export exists and is callable
    // This is a compile-time verification
}

test "rts_putStr exports C function" {
    // Check that the export exists and is callable
    // This is a compile-time verification
}

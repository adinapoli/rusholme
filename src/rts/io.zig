//! IO primitives for LLVM-based runtime (issue #56).
//!
//! These functions are called from LLVM-generated code via the PrimOpMapping
//! in `grin_to_llvm.zig`.  The same source compiles correctly for every
//! supported target:
//!   - Native (Linux/macOS): `std.posix.system.write` → OS write() syscall
//!   - wasm32-wasi:          `std.os.wasi.fd_write`   → WASI fd_write import
//!
//! No backend-specific adaptations are needed.  (Issue #477.)

const std = @import("std");
const builtin = @import("builtin");

// ═══════════════════════════════════════════════════════════════════════
// Internal helpers
// ═══════════════════════════════════════════════════════════════════════

/// Write `bytes` to the given file descriptor.
///
/// Branches at comptime on the OS so only the relevant syscall path is
/// emitted for each target.
fn writeBytesToFd(fd: u32, bytes: []const u8) void {
    switch (builtin.target.os.tag) {
        .wasi => {
            const iov = [1]std.os.wasi.ciovec_t{
                .{ .base = bytes.ptr, .len = bytes.len },
            };
            var nwritten: usize = 0;
            _ = std.os.wasi.fd_write(@intCast(fd), &iov, 1, &nwritten);
        },
        else => {
            _ = std.posix.system.write(@intCast(fd), bytes.ptr, bytes.len);
        },
    }
}

fn writeBytes(bytes: []const u8) void {
    writeBytesToFd(1, bytes);
}

fn writeBytesErr(bytes: []const u8) void {
    writeBytesToFd(2, bytes);
}

// ═══════════════════════════════════════════════════════════════════════
// IO Primitives
// ═══════════════════════════════════════════════════════════════════════

/// Print a null-terminated string followed by a newline to stdout.
///
/// Called `rts_putStrLn` from LLVM-generated code (PrimOp for `putStrLn`).
/// Returns 0 on success (return value matches the `puts()` convention used
/// by the LLVM codegen's LibcFunction descriptor).
pub export fn rts_putStrLn(str: [*:0]const u8) i32 {
    writeBytes(std.mem.span(str));
    writeBytes("\n");
    return 0;
}

/// Print a null-terminated string without a trailing newline to stdout.
///
/// Called `rts_putStr` from LLVM-generated code (PrimOp for `putStr`).
/// Returns 0 on success.
pub export fn rts_putStr(str: [*:0]const u8) i32 {
    writeBytes(std.mem.span(str));
    return 0;
}

/// Print an error message to stderr and terminate the program with exit code 1.
///
/// Implements the `error :: String -> a` Haskell primitive.  Called
/// `rts_error` from LLVM-generated code (PrimOp for `error`).
/// Never returns — `std.process.exit` calls `proc_exit` on WASI and the
/// `exit` syscall on native targets.
pub export fn rts_error(str: [*:0]const u8) i32 {
    writeBytesErr("error: ");
    writeBytesErr(std.mem.span(str));
    writeBytesErr("\n");
    std.process.exit(1);
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "rts_putStrLn is callable" {
    // Compile-time verification that the export exists and has the right type.
    _ = &rts_putStrLn;
}

test "rts_putStr is callable" {
    _ = &rts_putStr;
}

test "rts_error is callable" {
    _ = &rts_error;
}

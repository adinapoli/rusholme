//! IO primitives for the RTS.
//!
//! These primitives handle input/output operations:
//! - Writing to stdout/stderr
//! - Reading from stdin
//!
//! All IO operations are implemented as Zig functions that perform
//! the actual side effects.
//!
//! NOTE: For M1, we use the std.posix write() directly to avoid the
//! complexity of the new buffered Io API in Zig 0.16. This can be
//! refactored later to use the buffered API if needed.

const std = @import("std");
const posix = std.posix;
const value = @import("value.zig");
const Value = value.Value;
const EvalError = value.EvalError;

// ── IO Primitives ────────────────────────────────────────────────────────

/// Write a string to stdout.
///
/// Args: [String]
/// Returns: Unit
pub fn writeStdout(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;

    posix.write(1, str) catch return EvalError.IOError;

    return Value.unit;
}

/// Write a string to stderr.
///
/// Args: [String]
/// Returns: Unit
pub fn writeStderr(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;

    posix.write(2, str) catch return EvalError.IOError;

    return Value.unit;
}

/// Write a string to stdout with a newline.
///
/// Args: [String]
/// Returns: Unit
///
/// This is the RTS implementation for Prelude's `putStrLn`.
pub fn putStrLn(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;

    posix.write(1, str) catch return EvalError.IOError;
    posix.write(1, "\n") catch return EvalError.IOError;

    return Value.unit;
}

/// Read a line from stdin.
///
/// Args: []
/// Returns: String
///
/// The returned string is allocated using the provided allocator
/// and must be freed by the caller (or managed by the heap).
pub fn readStdin(allocator: std.mem.Allocator, args: []const Value) EvalError!Value {
    if (args.len != 0) return EvalError.ArityMismatch;

    // Simple implementation: read byte by byte until newline
    var line = std.ArrayList(u8).init(allocator);
    errdefer line.deinit(allocator);

    var buf: [1]u8 = undefined;
    while (true) {
        const n = posix.read(0, &buf) catch return EvalError.IOError;
        if (n == 0) break; // EOF
        if (buf[0] == '\n') break;
        line.append(allocator, buf[0]) catch return EvalError.OutOfMemory;
    }

    // Copy to a new slice that we own
    const owned = allocator.dupe(u8, line.items) catch return EvalError.OutOfMemory;
    line.deinit(allocator);

    return .{ .String = owned };
}

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

test "writeStdout: basic" {
    const args = [_]Value{.{ .String = "Hello, World!" }};
    const result = try writeStdout(&args);
    try testing.expect(result.isUnit());
}

test "writeStderr: basic" {
    const args = [_]Value{.{ .String = "Error message" }};
    const result = try writeStderr(&args);
    try testing.expect(result.isUnit());
}

test "putStrLn: basic" {
    const args = [_]Value{.{ .String = "Hello" }};
    const result = try putStrLn(&args);
    try testing.expect(result.isUnit());
}

test "writeStdout: wrong type" {
    const args = [_]Value{.{ .Int = 42 }};
    const result = writeStdout(&args);
    try testing.expectError(EvalError.TypeError, result);
}

test "writeStdout: wrong arity" {
    const args = [_]Value{.{ .String = "a" }, .{ .String = "b" }};
    const result = writeStdout(&args);
    try testing.expectError(EvalError.ArityMismatch, result);
}

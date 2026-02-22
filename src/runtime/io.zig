//! IO primitives for the RTS.
//!
//! These primitives handle input/output operations:
//! - Writing to stdout/stderr
//! - Reading from stdin
//!
//! All IO operations are implemented as Zig functions that perform
//! the actual side effects.

const std = @import("std");
const Allocator = std.mem.Allocator;
const File = std.Io.File;
const value = @import("value.zig");
const Value = value.Value;
const EvalError = value.EvalError;

// ── IO Primitives ────────────────────────────────────────────────────────

/// Write a string to stdout using the provided Io interface.
///
/// Args: [String]
/// Returns: Unit
pub fn writeStdout(io: std.Io, args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;

    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    const w = &fw.interface;
    w.writeAll(str) catch return EvalError.IOError;
    w.flush() catch return EvalError.IOError;

    return Value.unit;
}

/// Write a string to stderr using the provided Io interface.
///
/// Args: [String]
/// Returns: Unit
pub fn writeStderr(io: std.Io, args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;

    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stderr(), io, &buf);
    const w = &fw.interface;
    w.writeAll(str) catch return EvalError.IOError;
    w.flush() catch return EvalError.IOError;

    return Value.unit;
}

/// Write a string to stdout with a newline using the provided Io interface.
///
/// Args: [String]
/// Returns: Unit
///
/// This is the RTS implementation for Prelude's `putStrLn`.
pub fn putStrLn(io: std.Io, args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;

    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    const w = &fw.interface;
    w.writeAll(str) catch return EvalError.IOError;
    w.writeByte('\n') catch return EvalError.IOError;
    w.flush() catch return EvalError.IOError;

    return Value.unit;
}

/// Read a line from stdin using the provided Io interface.
///
/// Args: []
/// Returns: String
///
/// The returned string is allocated using the provided allocator
/// and must be freed by the caller (or managed by the heap).
pub fn readStdin(io: std.Io, allocator: Allocator, args: []const Value) EvalError!Value {
    if (args.len != 0) return EvalError.ArityMismatch;

    const stdin = File.stdin();
    var read_buf: [4096]u8 = undefined;
    var rdr = stdin.reader(io, &read_buf);
    const r = &rdr.interface;

    // Read until newline or EOF
    var line = try std.ArrayList(u8).initCapacity(allocator, 128);
    errdefer line.deinit(allocator);

    while (true) {
        const byte = r.readByte() catch |err| switch (err) {
            error.EndOfStream => break,
            else => return EvalError.IOError,
        };
        if (byte == '\n') break;
        try line.append(allocator, byte);
    }

    // Copy to a new slice that we own
    const owned = allocator.dupe(u8, line.items) catch return EvalError.OutOfMemory;
    line.deinit(allocator);

    return .{ .String = owned };
}

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

test "writeStdout: arity check" {
    const io = testing.io;
    // Test arity mismatch - no actual IO needed
    const args = [_]Value{.{ .String = "a" }, .{ .String = "b" }};
    const result = writeStdout(io, &args);
    try testing.expectError(EvalError.ArityMismatch, result);
}

test "writeStdout: type check" {
    const io = testing.io;
    // Test type error - no actual IO needed
    const args = [_]Value{.{ .Int = 42 }};
    const result = writeStdout(io, &args);
    try testing.expectError(EvalError.TypeError, result);
}

test "writeStderr: arity check" {
    const io = testing.io;
    const args = [_]Value{.{ .String = "a" }, .{ .String = "b" }};
    const result = writeStderr(io, &args);
    try testing.expectError(EvalError.ArityMismatch, result);
}

test "putStrLn: arity check" {
    const io = testing.io;
    const args = [_]Value{.{ .String = "a" }, .{ .String = "b" }};
    const result = putStrLn(io, &args);
    try testing.expectError(EvalError.ArityMismatch, result);
}

test "putStrLn: type check" {
    const io = testing.io;
    const args = [_]Value{.{ .Int = 42 }};
    const result = putStrLn(io, &args);
    try testing.expectError(EvalError.TypeError, result);
}

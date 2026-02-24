//! String primitives for the RTS.
//!
//! These primitives handle string operations on the `[Char]` representation:
//! - cons: prepend a character
//! - head: first character
//! - tail: rest of string
//! - null: is empty?

const std = @import("std");
const Allocator = std.mem.Allocator;
const value = @import("value.zig");
const Value = value.Value;
const EvalError = value.EvalError;

// ── String Primitives ────────────────────────────────────────────────────

/// Prepend a character to a string.
///
/// Args: [Char, String]
/// Returns: String
pub fn strCons(allocator: Allocator, args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const char = switch (args[0]) {
        .Char => |c| c,
        else => return EvalError.TypeError,
    };
    const str = args[1].asString() orelse return EvalError.TypeError;

    // Encode the character as UTF-8 and prepend
    var char_buf: [4]u8 = undefined;
    const char_len = std.unicode.utf8Encode(char, &char_buf) catch return EvalError.TypeError;

    const new_len = char_len + str.len;
    const new_str = allocator.alloc(u8, new_len) catch return EvalError.OutOfMemory;
    @memcpy(new_str[0..char_len], char_buf[0..char_len]);
    @memcpy(new_str[char_len..], str);

    return .{ .String = new_str };
}

/// Get the first character of a string.
///
/// Args: [String]
/// Returns: Char
pub fn strHead(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;
    if (str.len == 0) return EvalError.RuntimeError;

    const seq_len = std.unicode.utf8ByteSequenceLength(str[0]) catch
        return EvalError.TypeError;
    if (str.len < seq_len) return EvalError.TypeError;
    const decoded = std.unicode.utf8Decode(str[0..seq_len]) catch
        return EvalError.TypeError;
    return .{ .Char = decoded };
}

/// Get the tail of a string (everything after the first character).
///
/// Args: [String]
/// Returns: String
pub fn strTail(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;
    if (str.len == 0) return EvalError.RuntimeError;

    const first_len = std.unicode.utf8ByteSequenceLength(str[0]) catch
        return EvalError.TypeError;
    return .{ .String = str[first_len..] };
}

/// Check if a string is empty.
///
/// Args: [String]
/// Returns: Bool
pub fn strNull(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const str = args[0].asString() orelse return EvalError.TypeError;
    return Value.fromBool(str.len == 0);
}

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

test "strCons: prepend ASCII" {
    const args = [_]Value{ .{ .Char = 'H' }, .{ .String = "ello" } };
    const result = try strCons(testing.allocator, &args);
    defer testing.allocator.free(result.String);
    try testing.expectEqualStrings("Hello", result.String);
}

test "strCons: prepend to empty" {
    const args = [_]Value{ .{ .Char = 'x' }, .{ .String = "" } };
    const result = try strCons(testing.allocator, &args);
    defer testing.allocator.free(result.String);
    try testing.expectEqualStrings("x", result.String);
}

test "strHead: first char" {
    const args = [_]Value{.{ .String = "Hello" }};
    const result = try strHead(&args);
    try testing.expectEqual(@as(u21, 'H'), result.Char);
}

test "strHead: empty string errors" {
    const args = [_]Value{.{ .String = "" }};
    const result = strHead(&args);
    try testing.expectError(EvalError.RuntimeError, result);
}

test "strTail: rest of string" {
    const args = [_]Value{.{ .String = "Hello" }};
    const result = try strTail(&args);
    try testing.expectEqualStrings("ello", result.String);
}

test "strTail: empty string errors" {
    const args = [_]Value{.{ .String = "" }};
    const result = strTail(&args);
    try testing.expectError(EvalError.RuntimeError, result);
}

test "strNull: empty" {
    const args = [_]Value{.{ .String = "" }};
    const result = try strNull(&args);
    try testing.expect(result.Bool);
}

test "strNull: non-empty" {
    const args = [_]Value{.{ .String = "hi" }};
    const result = try strNull(&args);
    try testing.expect(!result.Bool);
}

test "strCons: arity check" {
    const args = [_]Value{.{ .Char = 'x' }};
    const result = strCons(testing.allocator, &args);
    try testing.expectError(EvalError.ArityMismatch, result);
}

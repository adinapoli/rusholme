//! Arithmetic primitives for the RTS.
//!
//! These primitives handle integer and floating-point arithmetic:
//! - Basic operations: add, sub, mul, div
//! - Negation
//! - Absolute value
//! - Quotient and remainder

const std = @import("std");
const value = @import("value.zig");
const Value = value.Value;
const EvalError = value.EvalError;

// ── Integer Arithmetic ───────────────────────────────────────────────────

/// Add two integers.
///
/// Args: [Int, Int]
/// Returns: Int
pub fn addInt(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = args[0].asInt() orelse return EvalError.TypeError;
    const b = args[1].asInt() orelse return EvalError.TypeError;

    return Value.fromInt(a + b);
}

/// Subtract two integers.
///
/// Args: [Int, Int]
/// Returns: Int
pub fn subInt(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = args[0].asInt() orelse return EvalError.TypeError;
    const b = args[1].asInt() orelse return EvalError.TypeError;

    return Value.fromInt(a - b);
}

/// Multiply two integers.
///
/// Args: [Int, Int]
/// Returns: Int
pub fn mulInt(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = args[0].asInt() orelse return EvalError.TypeError;
    const b = args[1].asInt() orelse return EvalError.TypeError;

    return Value.fromInt(a * b);
}

/// Negate an integer.
///
/// Args: [Int]
/// Returns: Int
pub fn negInt(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const a = args[0].asInt() orelse return EvalError.TypeError;

    return Value.fromInt(-a);
}

/// Absolute value of an integer.
///
/// Args: [Int]
/// Returns: Int
pub fn absInt(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const a = args[0].asInt() orelse return EvalError.TypeError;

    // Handle i64::min specially since @abs returns u64
    if (a == std.math.minInt(i64)) {
        return Value.fromInt(std.math.minInt(i64));
    }
    return Value.fromInt(@abs(a));
}

/// Integer quotient (truncates toward zero).
///
/// Args: [Int, Int]
/// Returns: Int
pub fn quotInt(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = args[0].asInt() orelse return EvalError.TypeError;
    const b = args[1].asInt() orelse return EvalError.TypeError;

    if (b == 0) return EvalError.DivisionByZero;

    // Truncate toward zero (like C/C++)
    const q = @divTrunc(a, b);
    return Value.fromInt(q);
}

/// Integer remainder (truncates toward zero).
///
/// Args: [Int, Int]
/// Returns: Int
pub fn remInt(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = args[0].asInt() orelse return EvalError.TypeError;
    const b = args[1].asInt() orelse return EvalError.TypeError;

    if (b == 0) return EvalError.DivisionByZero;

    // Remainder from truncation toward zero
    const r = @rem(a, b);
    return Value.fromInt(r);
}

// ── Floating-Point Arithmetic ────────────────────────────────────────────

/// Add two doubles.
///
/// Args: [Double, Double]
/// Returns: Double
pub fn addDouble(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = switch (args[0]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };
    const b = switch (args[1]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };

    return .{ .Double = a + b };
}

/// Subtract two doubles.
///
/// Args: [Double, Double]
/// Returns: Double
pub fn subDouble(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = switch (args[0]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };
    const b = switch (args[1]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };

    return .{ .Double = a - b };
}

/// Multiply two doubles.
///
/// Args: [Double, Double]
/// Returns: Double
pub fn mulDouble(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = switch (args[0]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };
    const b = switch (args[1]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };

    return .{ .Double = a * b };
}

/// Divide two doubles.
///
/// Args: [Double, Double]
/// Returns: Double
pub fn divDouble(args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    const a = switch (args[0]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };
    const b = switch (args[1]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };

    // Division by zero produces infinity, not an error, for doubles
    return .{ .Double = a / b };
}

/// Negate a double.
///
/// Args: [Double]
/// Returns: Double
pub fn negDouble(args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    const a = switch (args[0]) {
        .Double => |d| d,
        .Int => |i| @as(f64, @floatFromInt(i)),
        else => return EvalError.TypeError,
    };

    return .{ .Double = -a };
}

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

test "addInt: basic" {
    const args = [_]Value{ Value.fromInt(3), Value.fromInt(4) };
    const result = try addInt(&args);
    try testing.expectEqual(@as(i64, 7), result.Int);
}

test "subInt: basic" {
    const args = [_]Value{ Value.fromInt(10), Value.fromInt(3) };
    const result = try subInt(&args);
    try testing.expectEqual(@as(i64, 7), result.Int);
}

test "mulInt: basic" {
    const args = [_]Value{ Value.fromInt(6), Value.fromInt(7) };
    const result = try mulInt(&args);
    try testing.expectEqual(@as(i64, 42), result.Int);
}

test "negInt: basic" {
    const args = [_]Value{Value.fromInt(42)};
    const result = try negInt(&args);
    try testing.expectEqual(@as(i64, -42), result.Int);
}

test "absInt: positive" {
    const args = [_]Value{Value.fromInt(42)};
    const result = try absInt(&args);
    try testing.expectEqual(@as(i64, 42), result.Int);
}

test "absInt: negative" {
    const args = [_]Value{Value.fromInt(-42)};
    const result = try absInt(&args);
    try testing.expectEqual(@as(i64, 42), result.Int);
}

test "quotInt: basic" {
    const args = [_]Value{ Value.fromInt(10), Value.fromInt(3) };
    const result = try quotInt(&args);
    try testing.expectEqual(@as(i64, 3), result.Int);
}

test "quotInt: negative dividend" {
    const args = [_]Value{ Value.fromInt(-10), Value.fromInt(3) };
    const result = try quotInt(&args);
    try testing.expectEqual(@as(i64, -3), result.Int);
}

test "quotInt: division by zero" {
    const args = [_]Value{ Value.fromInt(10), Value.fromInt(0) };
    const result = quotInt(&args);
    try testing.expectError(EvalError.DivisionByZero, result);
}

test "remInt: basic" {
    const args = [_]Value{ Value.fromInt(10), Value.fromInt(3) };
    const result = try remInt(&args);
    try testing.expectEqual(@as(i64, 1), result.Int);
}

test "addDouble: basic" {
    const args = [_]Value{ .{ .Double = 3.5 }, .{ .Double = 4.5 } };
    const result = try addDouble(&args);
    try testing.expectApproxEqAbs(@as(f64, 8.0), result.Double, 0.0001);
}

test "divDouble: by zero returns infinity" {
    const args = [_]Value{ .{ .Double = 1.0 }, .{ .Double = 0.0 } };
    const result = try divDouble(&args);
    try testing.expect(std.math.isInf(result.Double));
}

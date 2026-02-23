//! GRIN evaluator with PrimOp dispatch.
//!
//! This module implements the core evaluation logic for GRIN IR, including:
//! - PrimOp dispatch to RTS functions
//! - Basic evaluation of simple expressions
//! - Heap management integration
//!
//! Reference: docs/decisions/0001-primops-and-rts-architecture.md

const std = @import("std");
const Allocator = std.mem.Allocator;

const primop = @import("../grin/primop.zig");
const PrimOp = primop.PrimOp;

const value = @import("value.zig");
const Value = value.Value;
const EvalError = value.EvalError;
const Heap = value.Heap;

const io_mod = @import("io.zig");
const arith_mod = @import("arith.zig");

// ── Evaluator Context ────────────────────────────────────────────────────

/// Context for evaluation, holding heap and IO state.
pub const EvalContext = struct {
    /// The heap for allocating values.
    heap: *Heap,

    /// The allocator for temporary allocations.
    allocator: Allocator,

    /// The IO interface for performing IO operations.
    io: std.Io,

    /// Initialize an evaluation context.
    pub fn init(allocator: Allocator, heap: *Heap, io: std.Io) EvalContext {
        return .{
            .heap = heap,
            .allocator = allocator,
            .io = io,
        };
    }
};

// ── PrimOp Dispatch ──────────────────────────────────────────────────────

/// Evaluate a PrimOp with the given arguments.
///
/// This is the core dispatch function that routes PrimOps to their
/// RTS implementations. It handles:
/// - IO operations (write_stdout, read_stdin, etc.)
/// - Arithmetic operations (add_Int, mul_Int, etc.)
/// - Comparison operations (eq_Int, lt_Int, etc.)
/// - Control operations (error, unreachable)
///
/// Args:
///   ctx: The evaluation context (heap, allocator, IO)
///   op: The PrimOp to evaluate
///   args: The arguments to the PrimOp
///
/// Returns:
///   The result of evaluating the PrimOp.
pub fn evalPrimOp(ctx: EvalContext, op: PrimOp, args: []const Value) EvalError!Value {
    const discriminant: u16 = @intFromEnum(op);

    // Dispatch based on discriminant ranges (matches primop.zig categories)
    if (discriminant < 50) {
        // IO Primitives (0-49)
        return evalIOPrim(ctx, op, args);
    } else if (discriminant < 150) {
        // Integer Arithmetic (100-149)
        return evalIntArithPrim(op, args);
    } else if (discriminant < 200) {
        // Floating-Point Arithmetic (150-199)
        return evalFloatArithPrim(op, args);
    } else if (discriminant < 250) {
        // Comparison (200-249)
        return evalComparisonPrim(op, args);
    } else if (discriminant < 350) {
        // Heap Operations (300-349)
        return evalHeapPrim(ctx, op, args);
    } else if (discriminant < 450) {
        // Control Flow (400-449)
        return evalControlPrim(op, args);
    } else if (discriminant < 550) {
        // FFI Bridge (500-549)
        return evalFFIPrim(ctx, op, args);
    } else {
        // Conversions (600-649) and unknown
        return evalConversionPrim(op, args);
    }
}

// ── Category-Specific Dispatch ───────────────────────────────────────────

/// Evaluate IO PrimOps.
fn evalIOPrim(ctx: EvalContext, op: PrimOp, args: []const Value) EvalError!Value {
    return switch (op) {
        .write_stdout => io_mod.writeStdout(ctx.io, args),
        .write_stderr => io_mod.writeStderr(ctx.io, args),
        .read_stdin => io_mod.readStdin(ctx.io, ctx.allocator, args),
        else => EvalError.NotImplemented,
    };
}

/// Evaluate integer arithmetic PrimOps.
fn evalIntArithPrim(op: PrimOp, args: []const Value) EvalError!Value {
    return switch (op) {
        .add_Int => arith_mod.addInt(args),
        .sub_Int => arith_mod.subInt(args),
        .mul_Int => arith_mod.mulInt(args),
        .neg_Int => arith_mod.negInt(args),
        .abs_Int => arith_mod.absInt(args),
        .quot_Int => arith_mod.quotInt(args),
        .rem_Int => arith_mod.remInt(args),
        else => EvalError.NotImplemented,
    };
}

/// Evaluate floating-point arithmetic PrimOps.
fn evalFloatArithPrim(op: PrimOp, args: []const Value) EvalError!Value {
    return switch (op) {
        .add_Double => arith_mod.addDouble(args),
        .sub_Double => arith_mod.subDouble(args),
        .mul_Double => arith_mod.mulDouble(args),
        .div_Double => arith_mod.divDouble(args),
        .neg_Double => arith_mod.negDouble(args),
        else => EvalError.NotImplemented,
    };
}

/// Evaluate comparison PrimOps.
fn evalComparisonPrim(op: PrimOp, args: []const Value) EvalError!Value {
    if (args.len != 2) return EvalError.ArityMismatch;

    return switch (op) {
        .eq_Int => blk: {
            const a = args[0].asInt() orelse return EvalError.TypeError;
            const b = args[1].asInt() orelse return EvalError.TypeError;
            break :blk Value.fromBool(a == b);
        },
        .lt_Int => blk: {
            const a = args[0].asInt() orelse return EvalError.TypeError;
            const b = args[1].asInt() orelse return EvalError.TypeError;
            break :blk Value.fromBool(a < b);
        },
        .le_Int => blk: {
            const a = args[0].asInt() orelse return EvalError.TypeError;
            const b = args[1].asInt() orelse return EvalError.TypeError;
            break :blk Value.fromBool(a <= b);
        },
        .gt_Int => blk: {
            const a = args[0].asInt() orelse return EvalError.TypeError;
            const b = args[1].asInt() orelse return EvalError.TypeError;
            break :blk Value.fromBool(a > b);
        },
        .ge_Int => blk: {
            const a = args[0].asInt() orelse return EvalError.TypeError;
            const b = args[1].asInt() orelse return EvalError.TypeError;
            break :blk Value.fromBool(a >= b);
        },
        .eq_Char => blk: {
            const a = switch (args[0]) {
                .Char => |c| c,
                else => return EvalError.TypeError,
            };
            const b = switch (args[1]) {
                .Char => |c| c,
                else => return EvalError.TypeError,
            };
            break :blk Value.fromBool(a == b);
        },
        .eq_Double => blk: {
            const a = switch (args[0]) {
                .Double => |d| d,
                else => return EvalError.TypeError,
            };
            const b = switch (args[1]) {
                .Double => |d| d,
                else => return EvalError.TypeError,
            };
            break :blk Value.fromBool(a == b);
        },
        .lt_Double => blk: {
            const a = switch (args[0]) {
                .Double => |d| d,
                else => return EvalError.TypeError,
            };
            const b = switch (args[1]) {
                .Double => |d| d,
                else => return EvalError.TypeError,
            };
            break :blk Value.fromBool(a < b);
        },
        else => EvalError.NotImplemented,
    };
}

/// Evaluate heap operation PrimOps.
fn evalHeapPrim(ctx: EvalContext, op: PrimOp, args: []const Value) EvalError!Value {
    _ = ctx;
    _ = args;

    return switch (op) {
        // Placeholder implementations - full support requires GRIN heap ops
        .newMutVar => EvalError.NotImplemented,
        .readMutVar => EvalError.NotImplemented,
        .writeMutVar => EvalError.NotImplemented,
        else => EvalError.NotImplemented,
    };
}

/// Evaluate control flow PrimOps.
fn evalControlPrim(op: PrimOp, args: []const Value) EvalError!Value {
    return switch (op) {
        .@"error" => blk: {
            if (args.len != 1) return EvalError.ArityMismatch;
            const msg = args[0].asString() orelse return EvalError.TypeError;
            std.log.err("Runtime error: {s}", .{msg});
            break :blk EvalError.RuntimeError;
        },
        .unreachable_ => {
            std.log.err("Reached unreachable PrimOp", .{});
            return EvalError.RuntimeError;
        },
        else => EvalError.NotImplemented,
    };
}

/// Evaluate FFI PrimOps.
fn evalFFIPrim(ctx: EvalContext, op: PrimOp, args: []const Value) EvalError!Value {
    _ = ctx;
    _ = args;

    return switch (op) {
        // FFI calls require proper marshalling infrastructure
        .ccall => EvalError.NotImplemented,
        else => EvalError.NotImplemented,
    };
}

/// Evaluate conversion PrimOps.
fn evalConversionPrim(op: PrimOp, args: []const Value) EvalError!Value {
    if (args.len != 1) return EvalError.ArityMismatch;

    return switch (op) {
        .intToDouble => blk: {
            const i = args[0].asInt() orelse return EvalError.TypeError;
            break :blk .{ .Double = @floatFromInt(i) };
        },
        .doubleToInt => blk: {
            const d = switch (args[0]) {
                .Double => |d| d,
                else => return EvalError.TypeError,
            };
            break :blk Value.fromInt(@intFromFloat(d));
        },
        .charToInt => blk: {
            const c = switch (args[0]) {
                .Char => |c| c,
                else => return EvalError.TypeError,
            };
            break :blk Value.fromInt(@as(i64, @intCast(c)));
        },
        .intToChar => blk: {
            const i = args[0].asInt() orelse return EvalError.TypeError;
            if (i < 0 or i > std.math.maxInt(u21)) return EvalError.TypeError;
            break :blk .{ .Char = @intCast(i) };
        },
        else => EvalError.NotImplemented,
    };
}

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

test "evalPrimOp: add_Int" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(3), Value.fromInt(4) };
    const result = try evalPrimOp(ctx, .add_Int, &args);
    try testing.expectEqual(@as(i64, 7), result.Int);
}

test "evalPrimOp: sub_Int" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(10), Value.fromInt(3) };
    const result = try evalPrimOp(ctx, .sub_Int, &args);
    try testing.expectEqual(@as(i64, 7), result.Int);
}

test "evalPrimOp: mul_Int" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(6), Value.fromInt(7) };
    const result = try evalPrimOp(ctx, .mul_Int, &args);
    try testing.expectEqual(@as(i64, 42), result.Int);
}

test "evalPrimOp: neg_Int" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{Value.fromInt(42)};
    const result = try evalPrimOp(ctx, .neg_Int, &args);
    try testing.expectEqual(@as(i64, -42), result.Int);
}

test "evalPrimOp: eq_Int true" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(5), Value.fromInt(5) };
    const result = try evalPrimOp(ctx, .eq_Int, &args);
    try testing.expect(result.Bool);
}

test "evalPrimOp: eq_Int false" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(5), Value.fromInt(3) };
    const result = try evalPrimOp(ctx, .eq_Int, &args);
    try testing.expect(!result.Bool);
}

test "evalPrimOp: lt_Int" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(3), Value.fromInt(5) };
    const result = try evalPrimOp(ctx, .lt_Int, &args);
    try testing.expect(result.Bool);
}

test "evalPrimOp: quot_Int" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(10), Value.fromInt(3) };
    const result = try evalPrimOp(ctx, .quot_Int, &args);
    try testing.expectEqual(@as(i64, 3), result.Int);
}

test "evalPrimOp: rem_Int" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(10), Value.fromInt(3) };
    const result = try evalPrimOp(ctx, .rem_Int, &args);
    try testing.expectEqual(@as(i64, 1), result.Int);
}

test "evalPrimOp: division by zero" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ Value.fromInt(10), Value.fromInt(0) };
    const result = evalPrimOp(ctx, .quot_Int, &args);
    try testing.expectError(EvalError.DivisionByZero, result);
}

test "evalPrimOp: intToDouble" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{Value.fromInt(42)};
    const result = try evalPrimOp(ctx, .intToDouble, &args);
    try testing.expectApproxEqAbs(@as(f64, 42.0), result.Double, 0.0001);
}

test "evalPrimOp: doubleToInt" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{.{ .Double = 42.9 }};
    const result = try evalPrimOp(ctx, .doubleToInt, &args);
    try testing.expectEqual(@as(i64, 42), result.Int);
}

test "evalPrimOp: charToInt" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{.{ .Char = 65 }};
    const result = try evalPrimOp(ctx, .charToInt, &args);
    try testing.expectEqual(@as(i64, 65), result.Int);
}

test "evalPrimOp: intToChar" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{Value.fromInt(65)};
    const result = try evalPrimOp(ctx, .intToChar, &args);
    try testing.expectEqual(@as(u21, 65), result.Char);
}

test "evalPrimOp: add_Double" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ .{ .Double = 3.5 }, .{ .Double = 4.5 } };
    const result = try evalPrimOp(ctx, .add_Double, &args);
    try testing.expectApproxEqAbs(@as(f64, 8.0), result.Double, 0.0001);
}

test "evalPrimOp: arity mismatch" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{Value.fromInt(1)};
    const result = evalPrimOp(ctx, .add_Int, &args);
    try testing.expectError(EvalError.ArityMismatch, result);
}

test "evalPrimOp: type error" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();
    const ctx = EvalContext.init(testing.allocator, &heap, testing.io);

    const args = [_]Value{ .{ .String = "not an int" }, Value.fromInt(1) };
    const result = evalPrimOp(ctx, .add_Int, &args);
    try testing.expectError(EvalError.TypeError, result);
}

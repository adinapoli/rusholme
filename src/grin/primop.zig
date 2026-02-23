//! Primitive operations (PrimOps) for the GRIN runtime system.
//!
//! PrimOps are the fundamental operations that the runtime system must implement.
//! They form the contract between the compiler and the RTS. All high-level
//! Prelude functions (like `putStrLn`, `map`, `foldr`) are ultimately implemented
//! in terms of these PrimOps.
//!
//! ## Design Philosophy
//!
//! - **Minimal surface area**: ~15-30 PrimOps instead of hundreds of built-in functions
//! - **Clear semantics**: Each PrimOp has well-defined type and behavior
//! - **RTS implementable**: All PrimOps can be implemented in Zig
//! - **FFI bridge**: The `ccall` PrimOp allows calling arbitrary C functions
//!
//! ## Categories
//!
//! - **IO**: Input/output operations (write, read)
//! - **Arithmetic**: Integer and floating-point operations
//! - **Comparison**: Equality and ordering
//! - **Heap**: Mutable variables and references
//! - **Control**: Error handling and divergence
//! - **FFI**: Foreign function interface
//!
//! Reference: docs/decisions/0001-primops-and-rts-architecture.md

const std = @import("std");
const naming = @import("../naming/unique.zig");

pub const Name = naming.Name;

// ── PrimOp Definition ───────────────────────────────────────────────────

/// A primitive operation known to the compiler and implemented by the RTS.
///
/// PrimOp names use the `#` suffix convention from GHC to distinguish them
/// from regular Haskell functions. In the IR, they appear as `PrimOp_<name>`.
///
/// The discriminant values are stable and can be used for serialization.
pub const PrimOp = enum(u16) {
    // ═══════════════════════════════════════════════════════════════════════
    // IO Primitives (0-49)
    // ═══════════════════════════════════════════════════════════════════════

    /// Write a string to stdout.
    /// Type: String -> IO ()
    write_stdout = 0,

    /// Write a string to stderr.
    /// Type: String -> IO ()
    write_stderr = 1,

    /// Read a line from stdin.
    /// Type: IO String
    read_stdin = 2,

    // ═══════════════════════════════════════════════════════════════════════
    // Integer Arithmetic (100-149)
    // ═══════════════════════════════════════════════════════════════════════

    /// Add two integers.
    /// Type: Int# -> Int# -> Int#
    add_Int = 100,

    /// Subtract two integers.
    /// Type: Int# -> Int# -> Int#
    sub_Int = 101,

    /// Multiply two integers.
    /// Type: Int# -> Int# -> Int#
    mul_Int = 102,

    /// Negate an integer.
    /// Type: Int# -> Int#
    neg_Int = 103,

    /// Absolute value of an integer.
    /// Type: Int# -> Int#
    abs_Int = 104,

    /// Quotient of two integers (truncates toward zero).
    /// Type: Int# -> Int# -> Int#
    quot_Int = 105,

    /// Remainder of integer division (truncates toward zero).
    /// Type: Int# -> Int# -> Int#
    rem_Int = 106,

    // ═══════════════════════════════════════════════════════════════════════
    // Floating-Point Arithmetic (150-199)
    // ═══════════════════════════════════════════════════════════════════════

    /// Add two doubles.
    /// Type: Double# -> Double# -> Double#
    add_Double = 150,

    /// Subtract two doubles.
    /// Type: Double# -> Double# -> Double#
    sub_Double = 151,

    /// Multiply two doubles.
    /// Type: Double# -> Double# -> Double#
    mul_Double = 152,

    /// Divide two doubles.
    /// Type: Double# -> Double# -> Double#
    div_Double = 153,

    /// Negate a double.
    /// Type: Double# -> Double#
    neg_Double = 154,

    // ═══════════════════════════════════════════════════════════════════════
    // Comparison (200-249)
    // ═══════════════════════════════════════════════════════════════════════

    /// Integer equality.
    /// Type: Int# -> Int# -> Bool
    eq_Int = 200,

    /// Integer less-than.
    /// Type: Int# -> Int# -> Bool
    lt_Int = 201,

    /// Integer less-than-or-equal.
    /// Type: Int# -> Int# -> Bool
    le_Int = 202,

    /// Integer greater-than.
    /// Type: Int# -> Int# -> Bool
    gt_Int = 203,

    /// Integer greater-than-or-equal.
    /// Type: Int# -> Int# -> Bool
    ge_Int = 204,

    /// Character equality.
    /// Type: Char# -> Char# -> Bool
    eq_Char = 205,

    /// Double equality.
    /// Type: Double# -> Double# -> Bool
    eq_Double = 206,

    /// Double less-than.
    /// Type: Double# -> Double# -> Bool
    lt_Double = 207,

    // ═══════════════════════════════════════════════════════════════════════
    // Heap Operations (300-349)
    // ═══════════════════════════════════════════════════════════════════════

    /// Create a new mutable variable.
    /// Type: a -> State# s -> (# State# s, MutVar# s a #)
    newMutVar = 300,

    /// Read a mutable variable.
    /// Type: MutVar# s a -> State# s -> (# State# s, a #)
    readMutVar = 301,

    /// Write a mutable variable.
    /// Type: MutVar# s a -> a -> State# s -> State# s
    writeMutVar = 302,

    // ═══════════════════════════════════════════════════════════════════════
    // Control Flow (400-449)
    // ═══════════════════════════════════════════════════════════════════════

    /// Throw an error with a message.
    /// Type: String -> a  (diverges)
    @"error" = 400,

    /// Unreachable code marker.
    /// Type: a  (compiler bug if reached)
    unreachable_ = 401,

    // ═══════════════════════════════════════════════════════════════════════
    // FFI Bridge (500-549)
    // ═══════════════════════════════════════════════════════════════════════

    /// Generic C function call.
    /// Type: (varies based on function signature)
    /// This is used internally by `foreign import ccall` declarations.
    ccall = 500,

    // ═══════════════════════════════════════════════════════════════════════
    // Conversions (600-649)
    // ═══════════════════════════════════════════════════════════════════════

    /// Convert Int# to Double#.
    /// Type: Int# -> Double#
    intToDouble = 600,

    /// Convert Double# to Int# (truncates).
    /// Type: Double# -> Int#
    doubleToInt = 601,

    /// Convert Char# to Int#.
    /// Type: Char# -> Int#
    charToInt = 602,

    /// Convert Int# to Char#.
    /// Type: Int# -> Char#
    intToChar = 603,

    _,

    // ── Helpers ───────────────────────────────────────────────────────────

    /// Returns the string name of this PrimOp (without the `#` suffix).
    pub fn name(self: PrimOp) []const u8 {
        return switch (self) {
            .write_stdout => "write_stdout",
            .write_stderr => "write_stderr",
            .read_stdin => "read_stdin",
            .add_Int => "add_Int",
            .sub_Int => "sub_Int",
            .mul_Int => "mul_Int",
            .neg_Int => "neg_Int",
            .abs_Int => "abs_Int",
            .quot_Int => "quot_Int",
            .rem_Int => "rem_Int",
            .add_Double => "add_Double",
            .sub_Double => "sub_Double",
            .mul_Double => "mul_Double",
            .div_Double => "div_Double",
            .neg_Double => "neg_Double",
            .eq_Int => "eq_Int",
            .lt_Int => "lt_Int",
            .le_Int => "le_Int",
            .gt_Int => "gt_Int",
            .ge_Int => "ge_Int",
            .eq_Char => "eq_Char",
            .eq_Double => "eq_Double",
            .lt_Double => "lt_Double",
            .newMutVar => "newMutVar",
            .readMutVar => "readMutVar",
            .writeMutVar => "writeMutVar",
            .@"error" => "error",
            .unreachable_ => "unreachable",
            .ccall => "ccall",
            .intToDouble => "intToDouble",
            .doubleToInt => "doubleToInt",
            .charToInt => "charToInt",
            .intToChar => "intToChar",
            _ => "unknown_primop",
        };
    }

    /// Returns the full PrimOp name with `#` suffix (GHC convention).
    pub fn fullName(self: PrimOp) []const u8 {
        return self.name(); // For now, return base name; can add # suffix if needed
    }

    /// Returns the category this PrimOp belongs to.
    pub fn category(self: PrimOp) PrimOpCategory {
        const discriminant: u16 = @intFromEnum(self);
        return if (discriminant < 50)
            .io
        else if (discriminant < 150)
            .int_arith
        else if (discriminant < 200)
            .float_arith
        else if (discriminant < 250)
            .comparison
        else if (discriminant < 350)
            .heap
        else if (discriminant < 450)
            .control
        else if (discriminant < 550)
            .ffi
        else
            .conversion;
    }

    /// Try to parse a PrimOp from its string name.
    pub fn fromString(str: []const u8) ?PrimOp {
        return std.meta.stringToEnum(PrimOp, str);
    }
};

/// Categories of PrimOps for documentation and organization.
pub const PrimOpCategory = enum {
    io,
    int_arith,
    float_arith,
    comparison,
    heap,
    control,
    ffi,
    conversion,
};

// ── PrimOp Registry ──────────────────────────────────────────────────────

/// A registry of all known PrimOps with their stable Name values.
///
/// This is used by the renamer to resolve PrimOp references and by the
/// typechecker to look up PrimOp type signatures.
pub const PrimOpRegistry = struct {
    /// The stable unique ID range for PrimOps is 500-599.
    /// This is separate from the Prelude function range (0-999).
    pub const unique_base: u64 = 500;

    /// Get the stable Name for a PrimOp.
    pub fn getName(op: PrimOp) Name {
        return .{
            .base = op.name(),
            .unique = .{ .value = unique_base + @intFromEnum(op) },
        };
    }
};

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

test "PrimOp: discriminant values" {
    try testing.expectEqual(@as(u16, 0), @intFromEnum(PrimOp.write_stdout));
    try testing.expectEqual(@as(u16, 100), @intFromEnum(PrimOp.add_Int));
    try testing.expectEqual(@as(u16, 200), @intFromEnum(PrimOp.eq_Int));
    try testing.expectEqual(@as(u16, 400), @intFromEnum(PrimOp.@"error"));
}

test "PrimOp: name lookup" {
    try testing.expectEqualStrings("write_stdout", PrimOp.write_stdout.name());
    try testing.expectEqualStrings("add_Int", PrimOp.add_Int.name());
    try testing.expectEqualStrings("error", PrimOp.@"error".name());
}

test "PrimOp: category classification" {
    try testing.expectEqual(PrimOpCategory.io, PrimOp.write_stdout.category());
    try testing.expectEqual(PrimOpCategory.int_arith, PrimOp.add_Int.category());
    try testing.expectEqual(PrimOpCategory.comparison, PrimOp.eq_Int.category());
    try testing.expectEqual(PrimOpCategory.control, PrimOp.@"error".category());
    try testing.expectEqual(PrimOpCategory.ffi, PrimOp.ccall.category());
}

test "PrimOp: fromString" {
    try testing.expectEqual(PrimOp.write_stdout, PrimOp.fromString("write_stdout"));
    try testing.expectEqual(PrimOp.add_Int, PrimOp.fromString("add_Int"));
    try testing.expectEqual(PrimOp.@"error", PrimOp.fromString("error"));
    try testing.expectEqual(@as(?PrimOp, null), PrimOp.fromString("nonexistent"));
}

test "PrimOpRegistry: stable names" {
    const name1 = PrimOpRegistry.getName(.write_stdout);
    try testing.expectEqualStrings("write_stdout", name1.base);
    // write_stdout has discriminant 0, so unique = 500 + 0 = 500
    try testing.expectEqual(@as(u64, 500), name1.unique.value);

    const name2 = PrimOpRegistry.getName(.add_Int);
    try testing.expectEqualStrings("add_Int", name2.base);
    // add_Int has discriminant 100, so unique = 500 + 100 = 600
    try testing.expectEqual(@as(u64, 600), name2.unique.value);
}

test "PrimOp: all ops have name mappings" {
    // Verify that all defined PrimOps have a name() implementation
    const ops = [_]PrimOp{
        .write_stdout, .write_stderr, .read_stdin,
        .add_Int, .sub_Int, .mul_Int, .neg_Int, .abs_Int, .quot_Int, .rem_Int,
        .add_Double, .sub_Double, .mul_Double, .div_Double, .neg_Double,
        .eq_Int, .lt_Int, .le_Int, .gt_Int, .ge_Int, .eq_Char, .eq_Double, .lt_Double,
        .newMutVar, .readMutVar, .writeMutVar,
        .@"error", .unreachable_,
        .ccall,
        .intToDouble, .doubleToInt, .charToInt, .intToChar,
    };

    for (ops) |op| {
        const n = op.name();
        try testing.expect(n.len > 0);
        try testing.expect(!std.mem.eql(u8, n, "unknown_primop"));
    }
}

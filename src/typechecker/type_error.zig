//! Structured type error payloads for diagnostics.
//!
//! This module defines the `TypeError` union, which carries structured
//! information about type errors (rather than pre-rendered strings).
//!
//! Renderers can use this information to provide rich, formatted output
//! (e.g., color-highlighting conflicting types, type diffs, etc.).
//!
//! The `message` field in `Diagnostic` is still populated for backward
//! compatibility with plain-text sinks, but the `payload` field allows
//! rich renderers to access the raw type information.

const std = @import("std");
const htype_mod = @import("htype.zig");
const naming_mod = @import("../naming/unique.zig");

pub const HType = htype_mod.HType;
pub const MetaVar = htype_mod.MetaVar;
pub const Name = naming_mod.Name;

/// Structured type error payload.
///
/// Each variant represents a specific kind of type error, carrying the
/// relevant data needed for rich rendering.
pub const TypeError = union(enum) {
    /// Type mismatch: lhs ~ rhs failed unification.
    ///
    /// The solver emits this when two types cannot be unified. Renderers
    /// can display the two types side-by-side, apply different colors to
    /// distinguish them, or compute a type diff.
    mismatch: struct {
        lhs: HType,
        rhs: HType,
        /// Expected type (for better error messages, e.g., when lhs is the
        /// expected type from an annotation)
        expected: ?HType = null,
        /// Actual type being checked
        actual: ?HType = null,
    },

    /// Occurs check violation: a metavariable appears in the type it's being
    /// unified with, which would create an infinite type.
    infinite_type: struct {
        /// The metavariable that appears in its own definition
        meta: MetaVar,
        /// The type the metavar is being unified against
        ty: HType,
    },

    /// Constructor applied to wrong number of arguments.
    ///
    /// Emitted when a type constructor is applied to a number of arguments
    /// that doesn't match its arity.
    arity_mismatch: struct {
        /// The name of the constructor
        name: Name,
        /// Expected number of type arguments
        expected: usize,
        /// Actual number of arguments received
        got: usize,
    },

    /// Function application with non-function type.
    application_error: struct {
        /// The expression being applied
        fn_ty: HType,
        /// The argument type
        arg_ty: HType,
    },

    /// Pattern match failure (type of pattern doesn't match scrutinee).
    pattern_mismatch: struct {
        /// Type of the pattern
        pat_ty: HType,
        /// Type of the scrutinee
        scrutinee_ty: HType,
    },
};

/// Generate a human-readable message for a TypeError.
///
/// This is used to populate the `message` field in `Diagnostic` as a
/// fallback, while the payload carries the rich structured data.
pub fn format(alloc: std.mem.Allocator, te: TypeError) std.mem.Allocator.Error![]const u8 {
    return switch (te) {
        .mismatch => |m| blk: {
            const lhs_str = try m.lhs.pretty(alloc);
            const rhs_str = try m.rhs.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "cannot unify `{s}` with `{s}`",
                .{ lhs_str, rhs_str },
            );
        },
        .infinite_type => |it| blk: {
            const ty_str = try it.ty.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "infinite type: ?{d} ~ `{s}` (occurs check failed)",
                .{ it.meta.id, ty_str },
            );
        },
        .arity_mismatch => |am| blk: {
            break :blk std.fmt.allocPrint(
                alloc,
                "type constructor `{s}` applied to {d} argument(s) but expects {d}",
                .{ am.name.base, am.got, am.expected },
            );
        },
        .application_error => |ae| blk: {
            const fn_str = try ae.fn_ty.pretty(alloc);
            const arg_str = try ae.arg_ty.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "cannot apply function of type `{s}` to argument of type `{s}`",
                .{ fn_str, arg_str },
            );
        },
        .pattern_mismatch => |pm| blk: {
            const pat_str = try pm.pat_ty.pretty(alloc);
            const scrutinee_str = try pm.scrutinee_ty.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "pattern of type `{s}` does not match scrutinee of type `{s}`",
                .{ pat_str, scrutinee_str },
            );
        },
    };
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

fn testName(base: []const u8, id: u64) Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

fn con0(base: []const u8, id: u64) HType {
    return HType{ .Con = .{ .name = testName(base, id), .args = &.{} } };
}

test "TypeError.format: mismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const te = TypeError{ .mismatch = .{
        .lhs = con0("Int", 0),
        .rhs = con0("Bool", 1),
    } };

    const msg = try format(alloc, te);
    try testing.expect(std.mem.indexOf(u8, msg, "cannot unify") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "Int") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "Bool") != null);
}

test "TypeError.format: infinite_type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const mv = MetaVar{ .id = 42, .ref = null };
    const te = TypeError{ .infinite_type = .{
        .meta = mv,
        .ty = con0("Int", 0),
    } };

    const msg = try format(alloc, te);
    try testing.expect(std.mem.indexOf(u8, msg, "?42") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "Int") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "occurs check") != null);
}

test "TypeError.format: arity_mismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const te = TypeError{ .arity_mismatch = .{
        .name = testName("Maybe", 0),
        .expected = 1,
        .got = 2,
    } };

    const msg = try format(alloc, te);
    try testing.expect(std.mem.indexOf(u8, msg, "Maybe") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "expects 1") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "applied to 2") != null);
}

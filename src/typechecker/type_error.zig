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

    /// No instance found for a class constraint (e.g. `Eq (a -> b)`).
    missing_instance: struct {
        class_name: Name,
        ty: HType,
    },

    /// Multiple matching instances for a class constraint.
    overlapping_instances: struct {
        class_name: Name,
        ty: HType,
    },

    /// Ambiguous type: a class constraint could not be resolved because
    /// the type variable was never determined (e.g. `show (read s)`).
    ambiguous_type: struct {
        class_name: Name,
        ty: HType,
    },

    /// Reference to a type class that does not exist.
    no_such_class: struct {
        name: Name,
    },

    /// Instance declaration is missing a required method implementation.
    missing_method: struct {
        class_name: Name,
        method_name: Name,
        instance_ty: HType,
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
        .missing_instance => |mi| blk: {
            const ty_str = try mi.ty.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "no instance for `{s} {s}`",
                .{ mi.class_name.base, ty_str },
            );
        },
        .overlapping_instances => |oi| blk: {
            const ty_str = try oi.ty.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "overlapping instances for `{s} {s}`",
                .{ oi.class_name.base, ty_str },
            );
        },
        .ambiguous_type => |at| blk: {
            const ty_str = try at.ty.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "ambiguous type variable in constraint `{s} {s}`",
                .{ at.class_name.base, ty_str },
            );
        },
        .no_such_class => |nc| blk: {
            break :blk std.fmt.allocPrint(
                alloc,
                "not a type class: `{s}`",
                .{nc.name.base},
            );
        },
        .missing_method => |mm| blk: {
            const ty_str = try mm.instance_ty.pretty(alloc);
            break :blk std.fmt.allocPrint(
                alloc,
                "instance `{s} {s}` is missing method `{s}`",
                .{ mm.class_name.base, ty_str, mm.method_name.base },
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

test "TypeError.format: missing_instance" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const te = TypeError{ .missing_instance = .{
        .class_name = testName("Show", 302),
        .ty = con0("Int -> Int", 0),
    } };

    const msg = try format(alloc, te);
    try testing.expect(std.mem.indexOf(u8, msg, "no instance") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "Show") != null);
}

test "TypeError.format: ambiguous_type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const te = TypeError{ .ambiguous_type = .{
        .class_name = testName("Num", 304),
        .ty = HType{ .Meta = .{ .id = 7, .ref = null } },
    } };

    const msg = try format(alloc, te);
    try testing.expect(std.mem.indexOf(u8, msg, "ambiguous") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "Num") != null);
}

test "TypeError.format: no_such_class" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const te = TypeError{ .no_such_class = .{
        .name = testName("Foo", 9999),
    } };

    const msg = try format(alloc, te);
    try testing.expect(std.mem.indexOf(u8, msg, "not a type class") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "Foo") != null);
}

test "TypeError.format: missing_method" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const te = TypeError{ .missing_method = .{
        .class_name = testName("Eq", 300),
        .method_name = testName("==", 50),
        .instance_ty = con0("Bool", 104),
    } };

    const msg = try format(alloc, te);
    try testing.expect(std.mem.indexOf(u8, msg, "missing method") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "Eq") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "==") != null);
}

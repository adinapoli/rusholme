//! Classify a data/newtype declaration into a `DataShape` for the deriving
//! pass.  The shape drives which classes a type may legally derive and which
//! synthesis strategy applies.

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const span_mod = @import("../diagnostics/span.zig");
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;

pub const DataShape = enum {
    /// All constructors are nullary (e.g. `data Day = Mon | Tue | Wed`).
    /// Legal: Eq, Ord, Show, Bounded, Enum.
    Enumeration,
    /// Exactly one constructor with at least one field
    /// (e.g. `data P = P Int Int` or any `newtype`).
    /// Legal: Eq, Ord, Show, Bounded.
    SingleProduct,
    /// Multiple constructors, at least one with fields.
    /// Legal: Eq, Ord, Show.
    SumOfProducts,
    /// Zero constructors (`data Void`).
    /// Legal: Eq, Ord; Show with empty case.
    Empty,
};

/// A uniform view over data and newtype declarations: a name, type variables,
/// and a list of constructors.  Newtypes appear here as a single-constructor
/// data with one field.
pub const NormalizedDecl = struct {
    name: []const u8,
    tyvars: []const []const u8,
    constructors: []const ast.ConDecl,
    span: SourceSpan,

    pub fn fromData(d: ast.DataDecl) NormalizedDecl {
        return .{
            .name = d.name,
            .tyvars = d.tyvars,
            .constructors = d.constructors,
            .span = d.span,
        };
    }

    pub fn fromNewtype(
        arena: std.mem.Allocator,
        d: ast.NewtypeDecl,
    ) std.mem.Allocator.Error!NormalizedDecl {
        const cons = try arena.alloc(ast.ConDecl, 1);
        cons[0] = d.constructor;
        return .{
            .name = d.name,
            .tyvars = d.tyvars,
            .constructors = cons,
            .span = d.span,
        };
    }
};

pub fn classify(decl: NormalizedDecl) DataShape {
    if (decl.constructors.len == 0) return .Empty;

    var all_nullary = true;
    for (decl.constructors) |c| {
        if (c.fields.len != 0) {
            all_nullary = false;
            break;
        }
    }
    if (all_nullary) return .Enumeration;

    if (decl.constructors.len == 1) return .SingleProduct;
    return .SumOfProducts;
}

fn testSpan() SourceSpan {
    const p = SourcePos.init(1, 1, 1);
    return SourceSpan.init(p, p);
}

test "classify: enumeration" {
    const cons = [_]ast.ConDecl{
        .{ .name = "A", .fields = &.{}, .span = testSpan() },
        .{ .name = "B", .fields = &.{}, .span = testSpan() },
    };
    const decl = NormalizedDecl{
        .name = "T",
        .tyvars = &.{},
        .constructors = &cons,
        .span = testSpan(),
    };
    try std.testing.expectEqual(DataShape.Enumeration, classify(decl));
}

test "classify: single product" {
    const fields = [_]ast.FieldDecl{
        .{ .Plain = .{ .Var = "a" } },
    };
    const cons = [_]ast.ConDecl{
        .{ .name = "P", .fields = &fields, .span = testSpan() },
    };
    const decl = NormalizedDecl{
        .name = "P",
        .tyvars = &.{"a"},
        .constructors = &cons,
        .span = testSpan(),
    };
    try std.testing.expectEqual(DataShape.SingleProduct, classify(decl));
}

test "classify: sum of products" {
    const fields = [_]ast.FieldDecl{
        .{ .Plain = .{ .Var = "a" } },
    };
    const cons = [_]ast.ConDecl{
        .{ .name = "Just", .fields = &fields, .span = testSpan() },
        .{ .name = "Nothing", .fields = &.{}, .span = testSpan() },
    };
    const decl = NormalizedDecl{
        .name = "Maybe",
        .tyvars = &.{"a"},
        .constructors = &cons,
        .span = testSpan(),
    };
    try std.testing.expectEqual(DataShape.SumOfProducts, classify(decl));
}

test "classify: empty" {
    const decl = NormalizedDecl{
        .name = "Void",
        .tyvars = &.{},
        .constructors = &.{},
        .span = testSpan(),
    };
    try std.testing.expectEqual(DataShape.Empty, classify(decl));
}

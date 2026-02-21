//! Core IR types (System F_C intermediate representation).
//!
//! This module defines the Core intermediate representation, modelled on
//! GHC's System F_C. Core is a small, typed language that the desugarer
//! produces from the Haskell AST. All optimisation is deferred to the
//! GRIN stage — there are no Core-to-Core passes.
//!
//! Reference: GHC's `compiler/GHC/Core.hs`

const std = @import("std");
const naming = @import("../naming/unique.zig");
const span_mod = @import("../diagnostics/span.zig");

pub const Name = naming.Name;
pub const Unique = naming.Unique;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;

// ── Literals ───────────────────────────────────────────────────────────

/// Core-level literal values.
///
/// These are simpler than the AST's source-level literals — no source
/// spans (the span lives on the enclosing Expr node).
pub const Literal = union(enum) {
    Int: i64,
    Float: f64,
    Char: u21,
    String: []const u8,
};

// ── Types ──────────────────────────────────────────────────────────────

/// Core's post-elaboration type representation.
///
/// Simpler than source-level types: all type synonyms have been expanded,
/// type class constraints have been translated to dictionary arguments,
/// and all types are explicit.
pub const CoreType = union(enum) {
    /// Type variable (e.g. `a` in `forall a. a -> a`).
    TyVar: Name,

    /// Type constructor application (e.g. `Maybe Int`, `Int`).
    /// A nullary constructor like `Int` has an empty `args` slice.
    TyCon: struct { name: Name, args: []const CoreType },

    /// Function type (a -> b).
    FunTy: struct { arg: *const CoreType, res: *const CoreType },

    /// Polymorphic type (forall a. ...).
    ForAllTy: struct { binder: Name, body: *const CoreType },
};

// ── Identifiers ────────────────────────────────────────────────────────

/// A Core variable/binder: a unique name paired with its type and
/// source location.
///
/// Used both for variable references (in `Expr.Var`) and for binders
/// (in `Expr.Lam`, `Bind`, `Alt`, etc.).
pub const Id = struct {
    name: Name,
    ty: CoreType,
    span: SourceSpan,
};

// ── Case alternatives ──────────────────────────────────────────────────

/// What a case alternative matches against.
pub const AltCon = union(enum) {
    /// Constructor pattern (e.g. `Just`, `Left`, `:`).
    DataAlt: Name,

    /// Literal pattern (e.g. `3`, `'a'`).
    LitAlt: Literal,

    /// Wildcard / default pattern.
    Default: void,
};

/// A single case alternative: pattern, binders for fields, and body.
pub const Alt = struct {
    con: AltCon,
    binders: []const Id,
    body: *const Expr,
};

// ── Bindings ───────────────────────────────────────────────────────────

/// A binding pair used in both NonRec and Rec bindings.
pub const BindPair = struct {
    binder: Id,
    rhs: *const Expr,
};

/// A let-binding: either a single non-recursive binding or a group of
/// mutually recursive bindings.
pub const Bind = union(enum) {
    NonRec: BindPair,
    Rec: []const BindPair,
};

// ── Coercions ──────────────────────────────────────────────────────────

/// Stub coercion type. Full System F_C coercions are deferred; for now
/// all coercions are Refl (identity).
pub const Coercion = enum {
    Refl,
};

// ── Expressions ────────────────────────────────────────────────────────

/// Core expression — the heart of the IR.
///
/// Modelled on GHC's `Expr CoreBndr` with 8 constructors. `Cast` and
/// `Tick` are deferred (not needed for M1).
pub const Expr = union(enum) {
    /// Variable reference.
    Var: Id,

    /// Literal value.
    Lit: struct { val: Literal, span: SourceSpan },

    /// Function application.
    App: struct { fn_expr: *const Expr, arg: *const Expr, span: SourceSpan },

    /// Lambda abstraction.
    Lam: struct { binder: Id, body: *const Expr, span: SourceSpan },

    /// Let binding (recursive or non-recursive).
    Let: struct { bind: Bind, body: *const Expr, span: SourceSpan },

    /// Case expression.
    ///
    /// The `binder` binds the scrutinee's value so alternatives can refer
    /// to it. The `ty` field caches the result type (needed when the
    /// alternatives list is empty, i.e. the scrutinee is known to diverge).
    Case: struct {
        scrutinee: *const Expr,
        binder: Id,
        ty: CoreType,
        alts: []const Alt,
        span: SourceSpan,
    },

    /// A type appearing as a function argument (explicit type application).
    Type: CoreType,

    /// A coercion appearing as a function argument (stubbed as Refl).
    Coercion: Coercion,
};

/// A Core-level data declaration.
pub const CoreDataDecl = struct {
    name: Name,
    tyvars: []const Name,
    /// Data constructors, represented as typed Ids.
    constructors: []const Id,
    span: SourceSpan,
};

/// A Core program consists of data declarations and top-level bindings.
pub const CoreProgram = struct {
    data_decls: []const CoreDataDecl,
    binds: []const Bind,
};

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

fn testSpan() SourceSpan {
    return SourceSpan.init(
        SourcePos.init(1, 1, 1),
        SourcePos.init(1, 1, 10),
    );
}

fn testName(base: []const u8, unique: u64) Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn intType() CoreType {
    return .{ .TyCon = .{ .name = testName("Int", 0), .args = &.{} } };
}

fn testId(base: []const u8, unique: u64) Id {
    return .{
        .name = testName(base, unique),
        .ty = intType(),
        .span = testSpan(),
    };
}

test "Literal: all variants" {
    const lit_int = Literal{ .Int = 42 };
    try testing.expectEqual(@as(i64, 42), lit_int.Int);

    const lit_float = Literal{ .Float = 3.14 };
    try testing.expectEqual(@as(f64, 3.14), lit_float.Float);

    const lit_char = Literal{ .Char = 'A' };
    try testing.expectEqual(@as(u21, 'A'), lit_char.Char);

    const lit_str = Literal{ .String = "hello" };
    try testing.expectEqualStrings("hello", lit_str.String);
}

test "CoreType: TyVar" {
    const tv = CoreType{ .TyVar = testName("a", 1) };
    try testing.expectEqualStrings("a", tv.TyVar.base);
}

test "CoreType: TyCon with args" {
    const maybe_int = CoreType{ .TyCon = .{
        .name = testName("Maybe", 2),
        .args = &.{intType()},
    } };
    try testing.expectEqualStrings("Maybe", maybe_int.TyCon.name.base);
    try testing.expectEqual(@as(usize, 1), maybe_int.TyCon.args.len);
}

test "CoreType: FunTy" {
    const arg_ty = CoreType{ .TyVar = testName("a", 1) };
    const res_ty = CoreType{ .TyVar = testName("b", 2) };
    const fun = CoreType{ .FunTy = .{ .arg = &arg_ty, .res = &res_ty } };
    try testing.expectEqualStrings("a", fun.FunTy.arg.TyVar.base);
    try testing.expectEqualStrings("b", fun.FunTy.res.TyVar.base);
}

test "CoreType: ForAllTy" {
    const body = CoreType{ .TyVar = testName("a", 1) };
    const forall = CoreType{ .ForAllTy = .{
        .binder = testName("a", 1),
        .body = &body,
    } };
    try testing.expectEqualStrings("a", forall.ForAllTy.binder.base);
}

test "Id: construction" {
    const id = testId("x", 5);
    try testing.expectEqualStrings("x", id.name.base);
    try testing.expectEqual(@as(u64, 5), id.name.unique.value);
}

test "AltCon: all variants" {
    const data = AltCon{ .DataAlt = testName("Just", 10) };
    try testing.expectEqualStrings("Just", data.DataAlt.base);

    const lit = AltCon{ .LitAlt = .{ .Int = 0 } };
    try testing.expectEqual(@as(i64, 0), lit.LitAlt.Int);

    const def = AltCon{ .Default = {} };
    _ = def;
}

test "Bind: NonRec" {
    const rhs = Expr{ .Lit = .{ .val = .{ .Int = 42 }, .span = testSpan() } };
    const bind = Bind{ .NonRec = .{
        .binder = testId("x", 1),
        .rhs = &rhs,
    } };
    try testing.expectEqualStrings("x", bind.NonRec.binder.name.base);
}

test "Bind: Rec" {
    const body_a = Expr{ .Var = testId("b", 2) };
    const body_b = Expr{ .Var = testId("a", 1) };
    const pairs = [_]BindPair{
        .{ .binder = testId("a", 1), .rhs = &body_a },
        .{ .binder = testId("b", 2), .rhs = &body_b },
    };
    const bind = Bind{ .Rec = &pairs };
    try testing.expectEqual(@as(usize, 2), bind.Rec.len);
}

test "Expr.Var" {
    const e = Expr{ .Var = testId("x", 1) };
    try testing.expectEqualStrings("x", e.Var.name.base);
}

test "Expr.Lit" {
    const e = Expr{ .Lit = .{ .val = .{ .Int = 99 }, .span = testSpan() } };
    try testing.expectEqual(@as(i64, 99), e.Lit.val.Int);
}

test "Expr.App" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const fn_expr = try alloc.create(Expr);
    fn_expr.* = .{ .Var = testId("f", 1) };

    const arg_expr = try alloc.create(Expr);
    arg_expr.* = .{ .Lit = .{ .val = .{ .Int = 5 }, .span = testSpan() } };

    const app = Expr{ .App = .{
        .fn_expr = fn_expr,
        .arg = arg_expr,
        .span = testSpan(),
    } };
    try testing.expectEqualStrings("f", app.App.fn_expr.Var.name.base);
    try testing.expectEqual(@as(i64, 5), app.App.arg.Lit.val.Int);
}

test "Expr.Lam" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(Expr);
    body.* = .{ .Var = testId("x", 1) };

    const lam = Expr{ .Lam = .{
        .binder = testId("x", 1),
        .body = body,
        .span = testSpan(),
    } };
    try testing.expectEqualStrings("x", lam.Lam.binder.name.base);
    try testing.expectEqualStrings("x", lam.Lam.body.Var.name.base);
}

test "Expr.Let: NonRec" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const rhs = try alloc.create(Expr);
    rhs.* = .{ .Lit = .{ .val = .{ .Int = 1 }, .span = testSpan() } };

    const body = try alloc.create(Expr);
    body.* = .{ .Var = testId("x", 1) };

    const let_expr = Expr{ .Let = .{
        .bind = .{ .NonRec = .{ .binder = testId("x", 1), .rhs = rhs } },
        .body = body,
        .span = testSpan(),
    } };
    try testing.expectEqualStrings("x", let_expr.Let.bind.NonRec.binder.name.base);
}

test "Expr.Case: with alternatives" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const scrutinee = try alloc.create(Expr);
    scrutinee.* = .{ .Var = testId("x", 1) };

    const alt_body = try alloc.create(Expr);
    alt_body.* = .{ .Lit = .{ .val = .{ .Int = 0 }, .span = testSpan() } };

    const alts = try alloc.alloc(Alt, 1);
    alts[0] = .{
        .con = .{ .Default = {} },
        .binders = &.{},
        .body = alt_body,
    };

    const case_expr = Expr{ .Case = .{
        .scrutinee = scrutinee,
        .binder = testId("wild", 99),
        .ty = intType(),
        .alts = alts,
        .span = testSpan(),
    } };
    try testing.expectEqual(@as(usize, 1), case_expr.Case.alts.len);
    try testing.expectEqualStrings("wild", case_expr.Case.binder.name.base);
}

test "Expr.Type" {
    const e = Expr{ .Type = intType() };
    try testing.expectEqualStrings("Int", e.Type.TyCon.name.base);
}

test "Expr.Coercion" {
    const e = Expr{ .Coercion = .Refl };
    try testing.expectEqual(Coercion.Refl, e.Coercion);
}

test "Nested: \\x -> case x of { _ -> x }" {
    // Represents the Core expression: \x -> case x of wild { DEFAULT -> x }
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const x_id = testId("x", 1);

    // The body of the default alternative: just x
    const alt_body = try alloc.create(Expr);
    alt_body.* = .{ .Var = x_id };

    const alts = try alloc.alloc(Alt, 1);
    alts[0] = .{
        .con = .{ .Default = {} },
        .binders = &.{},
        .body = alt_body,
    };

    // Scrutinee: x
    const scrutinee = try alloc.create(Expr);
    scrutinee.* = .{ .Var = x_id };

    // case x of wild { DEFAULT -> x }
    const case_body = try alloc.create(Expr);
    case_body.* = .{ .Case = .{
        .scrutinee = scrutinee,
        .binder = testId("wild", 99),
        .ty = intType(),
        .alts = alts,
        .span = testSpan(),
    } };

    // \x -> case x of wild { DEFAULT -> x }
    const lam = Expr{ .Lam = .{
        .binder = x_id,
        .body = case_body,
        .span = testSpan(),
    } };

    // Verify structure
    try testing.expectEqualStrings("x", lam.Lam.binder.name.base);
    const inner_case = lam.Lam.body.Case;
    try testing.expectEqualStrings("x", inner_case.scrutinee.Var.name.base);
    try testing.expectEqualStrings("wild", inner_case.binder.name.base);
    try testing.expectEqual(@as(usize, 1), inner_case.alts.len);
    try testing.expectEqualStrings("x", inner_case.alts[0].body.Var.name.base);
}

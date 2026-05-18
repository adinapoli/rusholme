//! Synthesise a `Bounded` instance.
//!
//! Legal shapes:
//!   - Enumeration: `minBound = <first con>`, `maxBound = <last con>`.
//!   - SingleProduct: each field's bound, requires `Bounded` per field type.
//!
//! Other shapes (sum-of-products, empty) emit a `deriving_shape_mismatch`
//! diagnostic and return `error.NotDerivable`.

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const span_mod = @import("../diagnostics/span.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");

const builder = @import("builder.zig");
const shape_mod = @import("shape.zig");

const SourceSpan = span_mod.SourceSpan;
const Allocator = std.mem.Allocator;
const NormalizedDecl = shape_mod.NormalizedDecl;

pub const Error = error{ OutOfMemory, NotDerivable };

pub const Synthesised = struct {
    helpers: []const ast.Decl,
    instance: ast.InstanceDecl,
};

pub fn synth(
    arena: Allocator,
    decl: NormalizedDecl,
    span: SourceSpan,
    diags: *diag_mod.DiagnosticCollector,
) Error!Synthesised {
    const shape = shape_mod.classify(decl);
    switch (shape) {
        .Enumeration => {
            const first = decl.constructors[0];
            const last = decl.constructors[decl.constructors.len - 1];
            const min_body = builder.mkVar(first.name, span);
            const max_body = builder.mkVar(last.name, span);
            const min_m = try builder.mkMatch(arena, &.{}, min_body, span);
            const max_m = try builder.mkMatch(arena, &.{}, max_body, span);
            const min_fb = try builder.mkFunBind(arena, "minBound", &.{min_m}, span);
            const max_fb = try builder.mkFunBind(arena, "maxBound", &.{max_m}, span);
            return .{ .helpers = &.{}, .instance = try finalize(arena, decl, &.{ min_fb, max_fb }, span, false) };
        },
        .SingleProduct => {
            const con = decl.constructors[0];
            const arity = con.fields.len;
            const min_args = try arena.alloc(ast.Expr, arity);
            const max_args = try arena.alloc(ast.Expr, arity);
            for (0..arity) |i| {
                min_args[i] = builder.mkVar("minBound", span);
                max_args[i] = builder.mkVar("maxBound", span);
            }
            const min_body = try builder.mkApp(arena, builder.mkVar(con.name, span), min_args);
            const max_body = try builder.mkApp(arena, builder.mkVar(con.name, span), max_args);
            const min_m = try builder.mkMatch(arena, &.{}, min_body, span);
            const max_m = try builder.mkMatch(arena, &.{}, max_body, span);
            const min_fb = try builder.mkFunBind(arena, "minBound", &.{min_m}, span);
            const max_fb = try builder.mkFunBind(arena, "maxBound", &.{max_m}, span);
            return .{ .helpers = &.{}, .instance = try finalize(arena, decl, &.{ min_fb, max_fb }, span, true) };
        },
        .Empty => {
            try emitDiag(arena, diags, .deriving_empty_bounded, span,
                "Cannot derive `Bounded` for an empty data type",
            );
            return error.NotDerivable;
        },
        .SumOfProducts => {
            try emitDiag(arena, diags, .deriving_shape_mismatch, span,
                "Cannot derive `Bounded`: type must be an enumeration or single-constructor product",
            );
            return error.NotDerivable;
        },
    }
}

fn finalize(
    arena: Allocator,
    decl: NormalizedDecl,
    bindings: []const ast.FunBinding,
    span: SourceSpan,
    with_field_context: bool,
) Allocator.Error!ast.InstanceDecl {
    var ctx: ?ast.Context = null;
    if (with_field_context) {
        var seen: std.StringArrayHashMapUnmanaged(void) = .empty;
        try builder.collectTypeVars(arena, decl.constructors, &seen);
        var pairs: std.ArrayListUnmanaged(builder.ClassVarPair) = .empty;
        for (seen.keys()) |tv| {
            try pairs.append(arena, .{ .class_name = "Bounded", .tyvar = tv });
        }
        ctx = try builder.mkContext(arena, pairs.items);
    }
    const applied = try builder.mkAppliedTypeCon(arena, decl.name, decl.tyvars, span);
    const head = try builder.mkInstanceHead(arena, "Bounded", applied, span);
    return builder.mkInstance(arena, ctx, head, bindings, span);
}

fn emitDiag(
    alloc: Allocator,
    diags: *diag_mod.DiagnosticCollector,
    code: diag_mod.DiagnosticCode,
    span: SourceSpan,
    msg: []const u8,
) Allocator.Error!void {
    try diags.emit(alloc, .{
        .severity = .@"error",
        .code = code,
        .span = span,
        .message = msg,
    });
}

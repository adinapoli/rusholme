//! Synthesise a `Show` instance.
//!
//! Uses `show = \x -> case x of ...` so that the method body is a single
//! binding to a lambda — this avoids the desugarer/typechecker issue with
//! multi-equation instance methods AND the dict-resolution bug that
//! affects top-level helpers mutually recursive with the instance.

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const span_mod = @import("../diagnostics/span.zig");

const builder = @import("builder.zig");
const shape_mod = @import("shape.zig");

const SourceSpan = span_mod.SourceSpan;
const Allocator = std.mem.Allocator;
const NormalizedDecl = shape_mod.NormalizedDecl;

pub const Synthesised = struct {
    helpers: []const ast.Decl,
    instance: ast.InstanceDecl,
};

pub fn synth(
    arena: Allocator,
    decl: NormalizedDecl,
    span: SourceSpan,
) Allocator.Error!Synthesised {
    var alts: std.ArrayListUnmanaged(ast.Alt) = .empty;

    for (decl.constructors) |c| {
        const arity = c.fields.len;
        if (arity == 0) {
            const pat = try builder.mkConPat(arena, c.name, &.{}, span);
            try alts.append(arena, builder.mkAlt(
                pat,
                builder.mkStrLit(c.name, span),
                span,
            ));
            continue;
        }

        const pats = try arena.alloc(ast.Pattern, arity);
        var parts: std.ArrayListUnmanaged(ast.Expr) = .empty;
        // Emit a single combined string prefix `"ConName "` (with trailing
        // space) then alternating `show xN` and `" "` separators — matches
        // how a user would write the body by hand.
        const prefix = try std.fmt.allocPrint(arena, "{s} ", .{c.name});
        try parts.append(arena, builder.mkStrLit(prefix, span));
        for (0..arity) |i| {
            const xn = try std.fmt.allocPrint(arena, "x{d}", .{i});
            pats[i] = builder.mkVarPat(xn, span);
            if (i > 0) try parts.append(arena, builder.mkStrLit(" ", span));
            const show_call = try builder.mkApp(
                arena,
                builder.mkVar("show", span),
                &.{builder.mkVar(xn, span)},
            );
            try parts.append(arena, show_call);
        }
        const con_pat = try builder.mkConPat(arena, c.name, pats, span);
        const body = try builder.mkAppendChain(arena, parts.items, span);
        try alts.append(arena, builder.mkAlt(con_pat, body, span));
    }

    // `show x = case x of ...` — match the same shape Prelude's hand-written
    // Show instances use.  `show = \x -> case x of ...` (single-binding to
    // a Lambda) is treated differently by the typechecker and resolves
    // inner `show` references through the outer instance's dictionary.
    const body: ast.Expr = if (decl.constructors.len == 0)
        try builder.mkApp(
            arena,
            builder.mkVar("error", span),
            &.{builder.mkStrLit("Show.show: empty type", span)},
        )
    else
        try builder.mkCase(
            arena,
            builder.mkVar("x", span),
            alts.items,
        );

    const method_match = try builder.mkMatch(
        arena,
        &.{builder.mkVarPat("x", span)},
        body,
        span,
    );
    const fb = try builder.mkFunBind(arena, "show", &.{method_match}, span);

    var seen: std.StringArrayHashMapUnmanaged(void) = .empty;
    try builder.collectTypeVars(arena, decl.constructors, &seen);
    var pairs: std.ArrayListUnmanaged(builder.ClassVarPair) = .empty;
    for (seen.keys()) |tv| {
        try pairs.append(arena, .{ .class_name = "Show", .tyvar = tv });
    }
    const ctx = try builder.mkContext(arena, pairs.items);

    const applied = try builder.mkAppliedTypeCon(arena, decl.name, decl.tyvars, span);
    const head = try builder.mkInstanceHead(arena, "Show", applied, span);
    const instance = try builder.mkInstance(arena, ctx, head, &.{fb}, span);

    return .{ .helpers = &.{}, .instance = instance };
}

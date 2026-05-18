//! Synthesise an `Eq` instance.
//!
//! Emits a single instance with method bodies in the canonical shape
//!
//!     instance Eq Color where
//!       (==) x y = case x of
//!         Red   -> case y of Red   -> True; _ -> False
//!         Green -> case y of Green -> True; _ -> False
//!         Blue  -> case y of Blue  -> True; _ -> False
//!       (/=) x y = not (x == y)
//!
//! The desugarer hoists each method's lambda chain to a top-level
//! binding (`_inst$Eq$<TypeName>$<method>`), so the dictionary slot
//! holds a Var reference to a properly-arited function rather than a
//! 1-argument outer lambda — without this hoist the LLVM call-lowering
//! drops the second argument when the dict method is called with two.

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
    var outer_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;

    for (decl.constructors) |c_outer| {
        const arity = c_outer.fields.len;

        const outer_pats = try arena.alloc(ast.Pattern, arity);
        for (0..arity) |i| {
            const n = try std.fmt.allocPrint(arena, "x{d}", .{i});
            outer_pats[i] = builder.mkVarPat(n, span);
        }
        const outer_con = try builder.mkConPat(arena, c_outer.name, outer_pats, span);

        // Inner case on y: matching the same constructor returns the
        // conjunction of field equalities; anything else is False.
        const inner_pats = try arena.alloc(ast.Pattern, arity);
        var field_eqs: std.ArrayListUnmanaged(ast.Expr) = .empty;
        for (0..arity) |i| {
            const xn = try std.fmt.allocPrint(arena, "x{d}", .{i});
            const yn = try std.fmt.allocPrint(arena, "y{d}", .{i});
            inner_pats[i] = builder.mkVarPat(yn, span);
            const eq_e = try builder.mkInfix(
                arena,
                builder.mkVar(xn, span),
                "==",
                builder.mkVar(yn, span),
                span,
            );
            try field_eqs.append(arena, eq_e);
        }
        const inner_con = try builder.mkConPat(arena, c_outer.name, inner_pats, span);
        const matched_body = try builder.mkAndChain(arena, field_eqs.items, span);

        var inner_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
        try inner_alts.append(arena, builder.mkAlt(inner_con, matched_body, span));
        if (decl.constructors.len > 1) {
            try inner_alts.append(arena, builder.mkAlt(
                builder.mkWildPat(span),
                builder.mkVar("False", span),
                span,
            ));
        }
        const inner_case = try builder.mkCase(
            arena,
            builder.mkVar("y", span),
            inner_alts.items,
        );

        try outer_alts.append(arena, builder.mkAlt(outer_con, inner_case, span));
    }

    const eq_body: ast.Expr = if (decl.constructors.len == 0)
        try builder.mkApp(
            arena,
            builder.mkVar("error", span),
            &.{builder.mkStrLit("Eq.==: empty type", span)},
        )
    else
        try builder.mkCase(
            arena,
            builder.mkVar("x", span),
            outer_alts.items,
        );

    const eq_method_match = try builder.mkMatch(
        arena,
        &.{ builder.mkVarPat("x", span), builder.mkVarPat("y", span) },
        eq_body,
        span,
    );
    const eq_fb = try builder.mkFunBind(arena, "==", &.{eq_method_match}, span);

    // `(/=) x y = not (x == y)`.
    const ne_body_eq = try builder.mkInfix(
        arena,
        builder.mkVar("x", span),
        "==",
        builder.mkVar("y", span),
        span,
    );
    const ne_body = try builder.mkApp(
        arena,
        builder.mkVar("not", span),
        &.{ne_body_eq},
    );
    const ne_match = try builder.mkMatch(
        arena,
        &.{ builder.mkVarPat("x", span), builder.mkVarPat("y", span) },
        ne_body,
        span,
    );
    const ne_fb = try builder.mkFunBind(arena, "/=", &.{ne_match}, span);

    var seen: std.StringArrayHashMapUnmanaged(void) = .empty;
    try builder.collectTypeVars(arena, decl.constructors, &seen);
    var pairs: std.ArrayListUnmanaged(builder.ClassVarPair) = .empty;
    for (seen.keys()) |tv| {
        try pairs.append(arena, .{ .class_name = "Eq", .tyvar = tv });
    }
    const ctx = try builder.mkContext(arena, pairs.items);

    const applied = try builder.mkAppliedTypeCon(arena, decl.name, decl.tyvars, span);
    const head = try builder.mkInstanceHead(arena, "Eq", applied, span);
    const instance = try builder.mkInstance(arena, ctx, head, &.{ eq_fb, ne_fb }, span);

    return .{ .helpers = &.{}, .instance = instance };
}

//! Synthesise an `Ord` instance.  Uses `compare :: a -> a -> Ordering` as
//! the primary method.  The body is a nested case expression that handles
//! every constructor pairing:
//!
//!   compare a b = case a of
//!     C1 x1 .. -> case b of
//!         C1 y1 .. -> <lex-compare fields>
//!         _        -> LT  -- later constructor on the right
//!     C2 x1 .. -> case b of
//!         C1 _ .. -> GT   -- earlier constructor on the right
//!         C2 y1 .. -> <lex-compare fields>
//!         _        -> LT
//!     ...
//!
//! Constructor order = order of declaration.

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
    // Build the outer `case a of` alts.
    var outer_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;

    for (decl.constructors, 0..) |c_outer, outer_idx| {
        const outer_arity = c_outer.fields.len;
        const outer_pats = try arena.alloc(ast.Pattern, outer_arity);
        for (0..outer_arity) |i| {
            const n = try std.fmt.allocPrint(arena, "x{d}", .{i});
            outer_pats[i] = builder.mkVarPat(n, span);
        }
        const outer_con = try builder.mkConPat(arena, c_outer.name, outer_pats, span);

        // Build the inner `case b of` alts.
        var inner_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;

        for (decl.constructors, 0..) |c_inner, inner_idx| {
            if (inner_idx == outer_idx) {
                // Equal-constructor case: lex compare fields.
                const inner_arity = c_inner.fields.len;
                const inner_pats = try arena.alloc(ast.Pattern, inner_arity);
                for (0..inner_arity) |j| {
                    const n = try std.fmt.allocPrint(arena, "y{d}", .{j});
                    inner_pats[j] = builder.mkVarPat(n, span);
                }
                const inner_con = try builder.mkConPat(
                    arena,
                    c_inner.name,
                    inner_pats,
                    span,
                );
                const body = try lexCompare(arena, inner_arity, span);
                try inner_alts.append(arena, builder.mkAlt(inner_con, body, span));
            } else if (inner_idx < outer_idx) {
                // Right is an earlier constructor → left > right.
                const inner_arity = c_inner.fields.len;
                const wild_pats = try arena.alloc(ast.Pattern, inner_arity);
                for (0..inner_arity) |j| wild_pats[j] = builder.mkWildPat(span);
                const inner_con = try builder.mkConPat(
                    arena,
                    c_inner.name,
                    wild_pats,
                    span,
                );
                try inner_alts.append(arena, builder.mkAlt(
                    inner_con,
                    builder.mkVar("GT", span),
                    span,
                ));
            } else {
                // inner_idx > outer_idx: right is later → left < right.
                const inner_arity = c_inner.fields.len;
                const wild_pats = try arena.alloc(ast.Pattern, inner_arity);
                for (0..inner_arity) |j| wild_pats[j] = builder.mkWildPat(span);
                const inner_con = try builder.mkConPat(
                    arena,
                    c_inner.name,
                    wild_pats,
                    span,
                );
                try inner_alts.append(arena, builder.mkAlt(
                    inner_con,
                    builder.mkVar("LT", span),
                    span,
                ));
            }
        }

        const inner_case = try builder.mkCase(
            arena,
            builder.mkVar("b", span),
            inner_alts.items,
        );
        try outer_alts.append(arena, builder.mkAlt(outer_con, inner_case, span));
    }

    // Empty data type: `compare _ _ = error "Ord.compare: empty type"`.
    if (decl.constructors.len == 0) {
        const err_call = try builder.mkApp(
            arena,
            builder.mkVar("error", span),
            &.{builder.mkStrLit("Ord.compare: empty type", span)},
        );
        const m = try builder.mkMatch(
            arena,
            &.{ builder.mkWildPat(span), builder.mkWildPat(span) },
            err_call,
            span,
        );
        const fb = try builder.mkFunBind(arena, "compare", &.{m}, span);
        return .{ .helpers = &.{}, .instance = try finalize(arena, decl, &.{fb}, span) };
    }

    const outer_case = try builder.mkCase(
        arena,
        builder.mkVar("a", span),
        outer_alts.items,
    );
    const m = try builder.mkMatch(
        arena,
        &.{
            builder.mkVarPat("a", span),
            builder.mkVarPat("b", span),
        },
        outer_case,
        span,
    );
    const fb = try builder.mkFunBind(arena, "compare", &.{m}, span);
    return .{ .helpers = &.{}, .instance = try finalize(arena, decl, &.{fb}, span) };
}

/// Build `case compare x0 y0 of { EQ -> case compare x1 y1 of { ... }; o -> o }`
/// down through `arity` field positions.  Returns `EQ` for arity 0.
fn lexCompare(
    arena: Allocator,
    arity: usize,
    span: SourceSpan,
) Allocator.Error!ast.Expr {
    if (arity == 0) return builder.mkVar("EQ", span);
    return lexCompareFrom(arena, 0, arity, span);
}

fn lexCompareFrom(
    arena: Allocator,
    i: usize,
    arity: usize,
    span: SourceSpan,
) Allocator.Error!ast.Expr {
    const x = try std.fmt.allocPrint(arena, "x{d}", .{i});
    const y = try std.fmt.allocPrint(arena, "y{d}", .{i});
    const cmp = try builder.mkApp(
        arena,
        builder.mkVar("compare", span),
        &.{ builder.mkVar(x, span), builder.mkVar(y, span) },
    );
    if (i + 1 == arity) return cmp;
    // Otherwise wrap in `case cmp of { EQ -> rest; o -> o }`.
    const rest = try lexCompareFrom(arena, i + 1, arity, span);
    const eq_alt = builder.mkAlt(
        try builder.mkConPat(arena, "EQ", &.{}, span),
        rest,
        span,
    );
    const o_alt = builder.mkAlt(
        builder.mkVarPat("o", span),
        builder.mkVar("o", span),
        span,
    );
    return builder.mkCase(arena, cmp, &.{ eq_alt, o_alt });
}

fn finalize(
    arena: Allocator,
    decl: NormalizedDecl,
    bindings: []const ast.FunBinding,
    span: SourceSpan,
) Allocator.Error!ast.InstanceDecl {
    var seen: std.StringArrayHashMapUnmanaged(void) = .empty;
    try builder.collectTypeVars(arena, decl.constructors, &seen);
    var pairs: std.ArrayListUnmanaged(builder.ClassVarPair) = .empty;
    for (seen.keys()) |tv| {
        try pairs.append(arena, .{ .class_name = "Ord", .tyvar = tv });
    }
    const ctx = try builder.mkContext(arena, pairs.items);
    const applied = try builder.mkAppliedTypeCon(arena, decl.name, decl.tyvars, span);
    const head = try builder.mkInstanceHead(arena, "Ord", applied, span);
    return builder.mkInstance(arena, ctx, head, bindings, span);
}

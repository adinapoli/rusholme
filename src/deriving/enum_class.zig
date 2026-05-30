//! Synthesise an `Enum` instance.  Only legal for enumeration types (all
//! constructors nullary).
//!
//! Generates only the four *primitive* Enum methods: `fromEnum`, `toEnum`,
//! `succ` and `pred`.  The four ranged enumerations — `enumFrom`,
//! `enumFromTo`, `enumFromThen`, `enumFromThenTo` — are inherited from the
//! `Enum` class defaults, which are expressed in terms of `succ`, `fromEnum`
//! and `toEnum` (issue #713).  Relying on the defaults removes the previous
//! O(n²)/O(n³) explicit case-matching code-size blow-up for `enumFromThen`
//! and `enumFromThenTo` (the workaround that issue #714 tracked, now obsolete).
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
    if (shape != .Enumeration) {
        try diags.emit(arena, .{
            .severity = .@"error",
            .code = .deriving_shape_mismatch,
            .span = span,
            .message = "Cannot derive `Enum`: type must be an enumeration (all constructors nullary)",
        });
        return error.NotDerivable;
    }

    // fromEnum
    var from_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |c, idx| {
        const pat = try builder.mkConPat(arena, c.name, &.{}, span);
        try from_alts.append(arena, builder.mkAlt(
            pat,
            builder.mkIntLit(@intCast(idx), span),
            span,
        ));
    }
    const from_body = try builder.mkCase(arena, builder.mkVar("x", span), from_alts.items);
    const from_match = try builder.mkMatch(
        arena,
        &.{builder.mkVarPat("x", span)},
        from_body,
        span,
    );
    const from_fb = try builder.mkFunBind(arena, "fromEnum", &.{from_match}, span);

    // toEnum
    var to_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |c, idx| {
        const lit_pat: ast.Pattern = .{ .Lit = .{ .Int = .{
            .value = @intCast(idx),
            .span = span,
        } } };
        try to_alts.append(arena, builder.mkAlt(
            lit_pat,
            builder.mkVar(c.name, span),
            span,
        ));
    }
    const to_err = try builder.mkApp(
        arena,
        builder.mkVar("error", span),
        &.{builder.mkStrLit("Enum.toEnum: out of range", span)},
    );
    try to_alts.append(arena, builder.mkAlt(builder.mkWildPat(span), to_err, span));
    const to_body = try builder.mkCase(arena, builder.mkVar("n", span), to_alts.items);
    const to_match = try builder.mkMatch(
        arena,
        &.{builder.mkVarPat("n", span)},
        to_body,
        span,
    );
    const to_fb = try builder.mkFunBind(arena, "toEnum", &.{to_match}, span);

    // succ
    var succ_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |c, idx| {
        const pat = try builder.mkConPat(arena, c.name, &.{}, span);
        const body = if (idx + 1 < decl.constructors.len)
            builder.mkVar(decl.constructors[idx + 1].name, span)
        else
            try builder.mkApp(
                arena,
                builder.mkVar("error", span),
                &.{builder.mkStrLit("Enum.succ: bad argument", span)},
            );
        try succ_alts.append(arena, builder.mkAlt(pat, body, span));
    }
    const succ_body = try builder.mkCase(arena, builder.mkVar("x", span), succ_alts.items);
    const succ_match = try builder.mkMatch(
        arena,
        &.{builder.mkVarPat("x", span)},
        succ_body,
        span,
    );
    const succ_fb = try builder.mkFunBind(arena, "succ", &.{succ_match}, span);

    // pred
    var pred_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |c, idx| {
        const pat = try builder.mkConPat(arena, c.name, &.{}, span);
        const body = if (idx == 0)
            try builder.mkApp(
                arena,
                builder.mkVar("error", span),
                &.{builder.mkStrLit("Enum.pred: bad argument", span)},
            )
        else
            builder.mkVar(decl.constructors[idx - 1].name, span);
        try pred_alts.append(arena, builder.mkAlt(pat, body, span));
    }
    const pred_body = try builder.mkCase(arena, builder.mkVar("x", span), pred_alts.items);
    const pred_match = try builder.mkMatch(
        arena,
        &.{builder.mkVarPat("x", span)},
        pred_body,
        span,
    );
    const pred_fb = try builder.mkFunBind(arena, "pred", &.{pred_match}, span);

    const applied = try builder.mkAppliedTypeCon(arena, decl.name, decl.tyvars, span);
    const head = try builder.mkInstanceHead(arena, "Enum", applied, span);
    const instance = try builder.mkInstance(
        arena,
        null,
        head,
        // Only the primitive methods; the four ranged enumerations are
        // inherited from the Enum class defaults (issue #713).
        &.{ from_fb, to_fb, succ_fb, pred_fb },
        span,
    );
    return .{ .helpers = &.{}, .instance = instance };
}

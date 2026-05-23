//! Synthesise an `Enum` instance.  Only legal for enumeration types (all
//! constructors nullary).
//!
//! Generates all 8 Enum methods: `fromEnum`, `toEnum`, `succ`, `pred`,
//! `enumFrom`, `enumFromTo`, `enumFromThen`, `enumFromThenTo`.
//!
//! The four arithmetic-sequence methods use explicit case-matching
//! over all constructor combinations rather than recursive self-calls.
//! This avoids GRIN thunk-naming collisions (see issue #714) and keeps
//! the generated code self-contained within the instance.  The trade-off
//! is O(n²) and O(n³) code size for `enumFromThen` and `enumFromThenTo`
//! respectively, which is acceptable for enumeration types (few constructors).
//!
//! A more compact recursive approach (e.g. `enumFrom x = x : enumFrom (succ x)`)
//! is deferred to issue #714 due to the thunk-naming collision it triggers.
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

    // enumFrom — explicit case enumeration (no recursive self-calls).
    // For each constructor Ck: enumFrom Ck = [Ck, C{k+1}, ..., C{n-1}]
    var ef_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |c, idx| {
        const pat = try builder.mkConPat(arena, c.name, &.{}, span);
        // Build [Ck, C{k+1}, ..., C{n-1}] right-to-left
        var list_expr: ast.Expr = .{ .List = &.{} };
        var k: usize = decl.constructors.len;
        while (k > idx) {
            k -= 1;
            const elem = builder.mkVar(decl.constructors[k].name, span);
            list_expr = try builder.mkInfix(arena, elem, ":", list_expr, span);
        }
        try ef_alts.append(arena, builder.mkAlt(pat, list_expr, span));
    }
    const ef_body = try builder.mkCase(arena, builder.mkVar("x", span), ef_alts.items);
    const ef_match = try builder.mkMatch(
        arena,
        &.{builder.mkVarPat("x", span)},
        ef_body,
        span,
    );
    const ef_fb = try builder.mkFunBind(arena, "enumFrom", &.{ef_match}, span);

    // enumFromTo — explicit case enumeration for both arguments.
    // enumFromTo Ck Cj = [Ck, ..., Cj] if j >= k, else []
    var eft_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |c_outer, outer_idx| {
        const outer_pat = try builder.mkConPat(arena, c_outer.name, &.{}, span);
        var inner_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
        for (decl.constructors, 0..) |c_inner, inner_idx| {
            const inner_pat = try builder.mkConPat(arena, c_inner.name, &.{}, span);
            if (inner_idx < outer_idx) {
                // y < x: empty list
                try inner_alts.append(arena, builder.mkAlt(inner_pat, .{ .List = &.{} }, span));
            } else {
                // y >= x: [C{outer_idx}, ..., C{inner_idx}]
                var list_expr: ast.Expr = .{ .List = &.{} };
                var k: usize = inner_idx + 1;
                while (k > outer_idx) {
                    k -= 1;
                    const elem = builder.mkVar(decl.constructors[k].name, span);
                    list_expr = try builder.mkInfix(arena, elem, ":", list_expr, span);
                }
                try inner_alts.append(arena, builder.mkAlt(inner_pat, list_expr, span));
            }
        }
        const inner_case = try builder.mkCase(arena, builder.mkVar("y", span), inner_alts.items);
        try eft_alts.append(arena, builder.mkAlt(outer_pat, inner_case, span));
    }
    const eft_body = try builder.mkCase(arena, builder.mkVar("x", span), eft_alts.items);
    const eft_match = try builder.mkMatch(
        arena,
        &.{ builder.mkVarPat("x", span), builder.mkVarPat("y", span) },
        eft_body,
        span,
    );
    const eft_fb = try builder.mkFunBind(arena, "enumFromTo", &.{eft_match}, span);

    // enumFromThen — explicit case enumeration for both arguments.
    // For each pair (Ck, Cj), produce the arithmetic sequence
    //   [Ck, C{k+step}, ...] limited to the constructor range.
    // Lists are built right-to-left to ensure correct element order.
    // tracked in: https://github.com/adinapoli/rusholme/issues/708
    var eftn_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |c, idx| {
        const outer_pat = try builder.mkConPat(arena, c.name, &.{}, span);
        var inner_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
        for (decl.constructors, 0..) |c2, idx2| {
            const inner_pat = try builder.mkConPat(arena, c2.name, &.{}, span);
            const step: isize = @as(isize, @intCast(idx2)) - @as(isize, @intCast(idx));
            var list_expr: ast.Expr = .{ .List = &.{} };
            if (step > 0) {
                // Ascending: [Ck, C{k+step}, C{k+2*step}, ...] up to last in range
                // Build right-to-left: iterate from last element back to first
                var pos: usize = decl.constructors.len - 1;
                while (pos > idx) : (pos -= 1) {
                    // Only include elements on the step grid
                    if ((pos - idx) % @as(usize, @intCast(step)) == 0) {
                        const elem = builder.mkVar(decl.constructors[pos].name, span);
                        list_expr = try builder.mkInfix(arena, elem, ":", list_expr, span);
                    }
                }
                // Always include the first element
                const first = builder.mkVar(decl.constructors[idx].name, span);
                list_expr = try builder.mkInfix(arena, first, ":", list_expr, span);
            } else if (step < 0) {
                // Descending: [Ck, C{k+step}, C{k+2*step}, ...] down to first in range
                // Build right-to-left: iterate from first element forward to k
                var pos: usize = 0;
                while (pos < idx) : (pos += 1) {
                    const abs_step = @as(usize, @intCast(-step));
                    if ((idx - pos) % abs_step == 0) {
                        const elem = builder.mkVar(decl.constructors[pos].name, span);
                        list_expr = try builder.mkInfix(arena, elem, ":", list_expr, span);
                    }
                }
                // Always include the first element
                const first = builder.mkVar(decl.constructors[idx].name, span);
                list_expr = try builder.mkInfix(arena, first, ":", list_expr, span);
            } else {
                // step == 0: infinite repeat, just return [Ck]
                const elem = builder.mkVar(c.name, span);
                list_expr = try builder.mkInfix(arena, elem, ":", .{ .List = &.{} }, span);
            }
            try inner_alts.append(arena, builder.mkAlt(inner_pat, list_expr, span));
        }
        const inner_case = try builder.mkCase(arena, builder.mkVar("y", span), inner_alts.items);
        try eftn_alts.append(arena, builder.mkAlt(outer_pat, inner_case, span));
    }
    const eftn_body = try builder.mkCase(arena, builder.mkVar("x", span), eftn_alts.items);
    const eftn_match = try builder.mkMatch(
        arena,
        &.{ builder.mkVarPat("x", span), builder.mkVarPat("y", span) },
        eftn_body,
        span,
    );
    const eftn_fb = try builder.mkFunBind(arena, "enumFromThen", &.{eftn_match}, span);

    // enumFromThenTo — explicit case enumeration for all three arguments.
    // Produces the arithmetic sequence [Ck, C{k+step}, ...] up to Cm.
    // Lists are built right-to-left to ensure correct element order.
    var eftt_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
    for (decl.constructors, 0..) |cx, x_idx| {
        const outer_pat = try builder.mkConPat(arena, cx.name, &.{}, span);
        var mid_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
        for (decl.constructors, 0..) |cy, y_idx| {
            const mid_pat = try builder.mkConPat(arena, cy.name, &.{}, span);
            var inner_alts: std.ArrayListUnmanaged(ast.Alt) = .empty;
            for (decl.constructors, 0..) |cz, z_idx| {
                const inner_pat = try builder.mkConPat(arena, cz.name, &.{}, span);
                const step: isize = @as(isize, @intCast(y_idx)) - @as(isize, @intCast(x_idx));
                var list_expr: ast.Expr = .{ .List = &.{} };
                if (step > 0) {
                    // Ascending: build [Ck, C{k+step}, ...] right-to-left up to Cm
                    var pos: usize = z_idx + 1;
                    while (pos > x_idx) : (pos -= 1) {
                        if ((pos - 1 - x_idx) % @as(usize, @intCast(step)) == 0) {
                            const elem = builder.mkVar(decl.constructors[pos - 1].name, span);
                            list_expr = try builder.mkInfix(arena, elem, ":", list_expr, span);
                        }
                    }
                    // Always include the first element Ck
                    const first = builder.mkVar(decl.constructors[x_idx].name, span);
                    list_expr = try builder.mkInfix(arena, first, ":", list_expr, span);
                } else if (step < 0) {
                    // Descending: build [Ck, C{k+step}, ...] right-to-left down to Cm
                    const abs_step = @as(usize, @intCast(-step));
                    var pos: usize = 0;
                    while (pos < x_idx) : (pos += 1) {
                        if ((x_idx - pos) % abs_step == 0) {
                            const elem = builder.mkVar(decl.constructors[pos].name, span);
                            list_expr = try builder.mkInfix(arena, elem, ":", list_expr, span);
                        }
                    }
                    // Always include the first element Ck
                    const first = builder.mkVar(decl.constructors[x_idx].name, span);
                    list_expr = try builder.mkInfix(arena, first, ":", list_expr, span);
                } else {
                    // step == 0: [x] (infinite repeat, cap at single element)
                    const elem = builder.mkVar(cx.name, span);
                    list_expr = try builder.mkInfix(arena, elem, ":", .{ .List = &.{} }, span);
                }
                try inner_alts.append(arena, builder.mkAlt(inner_pat, list_expr, span));
            }
            const inner_case = try builder.mkCase(arena, builder.mkVar("z", span), inner_alts.items);
            try mid_alts.append(arena, builder.mkAlt(mid_pat, inner_case, span));
        }
        const mid_case = try builder.mkCase(arena, builder.mkVar("y", span), mid_alts.items);
        try eftt_alts.append(arena, builder.mkAlt(outer_pat, mid_case, span));
    }
    const eftt_body = try builder.mkCase(arena, builder.mkVar("x", span), eftt_alts.items);
    const eftt_match = try builder.mkMatch(
        arena,
        &.{ builder.mkVarPat("x", span), builder.mkVarPat("y", span), builder.mkVarPat("z", span) },
        eftt_body,
        span,
    );
    const eftt_fb = try builder.mkFunBind(arena, "enumFromThenTo", &.{eftt_match}, span);

    const applied = try builder.mkAppliedTypeCon(arena, decl.name, decl.tyvars, span);
    const head = try builder.mkInstanceHead(arena, "Enum", applied, span);
    const instance = try builder.mkInstance(
        arena,
        null,
        head,
        &.{ from_fb, to_fb, succ_fb, pred_fb, ef_fb, eft_fb, eftn_fb, eftt_fb },
        span,
    );
    return .{ .helpers = &.{}, .instance = instance };
}

//! AST construction helpers for the deriving pass.
//!
//! All synthesised nodes carry the same `SourceSpan` (typically the data
//! decl's deriving-clause span) so diagnostics point at the user's
//! `deriving (...)` clause rather than at phantom internal locations.

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const span_mod = @import("../diagnostics/span.zig");

pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;
pub const Allocator = std.mem.Allocator;

/// Monotonic counter giving every synthesised *expression* occurrence of a
/// variable or operator a distinct column.
///
/// The desugarer's dictionary-evidence map is keyed by
/// `(var_unique, span_start_line, span_start_col, class_unique)`.  All nodes a
/// deriving builder emits share one source span — the `deriving (...)` clause.
/// Without distinct spans the many class-method call sites in a single derived
/// instance collapse onto one key, so e.g. the field comparison `x == y`
/// (needing `Eq Int`) and `(/=)`'s own `x == y` (needing `Eq <T>`) overwrite
/// each other; the field comparison is then handed the instance's *own*
/// dictionary and dispatches on the wrong constructor, crashing at runtime with
/// "Non-exhaustive patterns in case".  Giving each occurrence a unique column
/// keeps the evidence keys distinct.  See #851.
var occ_seq: u32 = 0;

/// Reset the occurrence-span counter. Called at the start of each deriving
/// pass so span assignment is deterministic per compile / REPL input.
pub fn resetOccurrenceSpans() void {
    occ_seq = 0;
}

/// Derive a distinct span from `span`, preserving file + line (so diagnostics
/// still point at the user's `deriving` clause) but assigning a fresh column.
fn freshOccSpan(span: SourceSpan) SourceSpan {
    occ_seq += 1;
    const line = if (span.start.line > 0) span.start.line else 1;
    const start = SourcePos.init(span.start.file_id, line, occ_seq);
    const end = SourcePos.init(span.start.file_id, line, occ_seq + 1);
    return SourceSpan.init(start, end);
}

pub fn alloc(arena: Allocator, comptime T: type, value: T) Allocator.Error!*const T {
    const ptr = try arena.create(T);
    ptr.* = value;
    return ptr;
}

pub fn mkQName(name: []const u8, span: SourceSpan) ast.QName {
    return .{ .module_name = null, .name = name, .span = span };
}

pub fn mkVar(name: []const u8, span: SourceSpan) ast.Expr {
    // A variable *occurrence* may carry a class-method constraint, so it needs
    // a unique span for evidence keying (see `occ_seq`).
    return .{ .Var = mkQName(name, freshOccSpan(span)) };
}

pub fn mkVarPat(name: []const u8, span: SourceSpan) ast.Pattern {
    return .{ .Var = .{ .name = name, .span = span } };
}

pub fn mkWildPat(span: SourceSpan) ast.Pattern {
    return .{ .Wild = span };
}

pub fn mkConPat(
    arena: Allocator,
    name: []const u8,
    args: []const ast.Pattern,
    span: SourceSpan,
) Allocator.Error!ast.Pattern {
    const owned = try arena.alloc(ast.Pattern, args.len);
    @memcpy(owned, args);
    return .{ .Con = .{
        .name = mkQName(name, span),
        .args = owned,
        .span = span,
    } };
}

/// Wrap a constructor pattern in parens for use as a function argument
/// pattern (`f (Con x) = ...`).  Required to mirror the AST shape the
/// parser produces, which downstream phases rely on.
pub fn mkConPatParen(
    arena: Allocator,
    name: []const u8,
    args: []const ast.Pattern,
    span: SourceSpan,
) Allocator.Error!ast.Pattern {
    const inner = try mkConPat(arena, name, args, span);
    if (args.len == 0) return inner; // bare nullary cons need no parens
    const boxed = try arena.create(ast.Pattern);
    boxed.* = inner;
    return .{ .Paren = .{ .pat = boxed, .span = span } };
}

pub fn mkApp(
    arena: Allocator,
    func: ast.Expr,
    args: []const ast.Expr,
) Allocator.Error!ast.Expr {
    if (args.len == 0) return func;
    var current = func;
    for (args) |a| {
        const fn_box = try alloc(arena, ast.Expr, current);
        const arg_box = try alloc(arena, ast.Expr, a);
        current = .{ .App = .{ .fn_expr = fn_box, .arg_expr = arg_box } };
    }
    return current;
}

pub fn mkInfix(
    arena: Allocator,
    left: ast.Expr,
    op: []const u8,
    right: ast.Expr,
    span: SourceSpan,
) Allocator.Error!ast.Expr {
    return .{ .InfixApp = .{
        .left = try alloc(arena, ast.Expr, left),
        // The operator occurrence carries the class-method constraint, so it
        // needs a unique span for evidence keying (see `occ_seq`).
        .op = mkQName(op, freshOccSpan(span)),
        .right = try alloc(arena, ast.Expr, right),
    } };
}

pub fn mkStrLit(s: []const u8, span: SourceSpan) ast.Expr {
    return .{ .Lit = .{ .String = .{ .value = s, .span = span } } };
}

pub fn mkIntLit(n: i64, span: SourceSpan) ast.Expr {
    return .{ .Lit = .{ .Int = .{ .value = n, .span = span } } };
}

pub fn mkCase(
    arena: Allocator,
    scrutinee: ast.Expr,
    alts: []const ast.Alt,
) Allocator.Error!ast.Expr {
    const owned_alts = try arena.alloc(ast.Alt, alts.len);
    @memcpy(owned_alts, alts);
    return .{ .Case = .{
        .scrutinee = try alloc(arena, ast.Expr, scrutinee),
        .alts = owned_alts,
    } };
}

pub fn mkUngRhs(expr: ast.Expr) ast.Rhs {
    return .{ .UnGuarded = expr };
}

pub fn mkMatch(
    arena: Allocator,
    patterns: []const ast.Pattern,
    body: ast.Expr,
    span: SourceSpan,
) Allocator.Error!ast.Match {
    const owned = try arena.alloc(ast.Pattern, patterns.len);
    @memcpy(owned, patterns);
    return .{
        .patterns = owned,
        .rhs = mkUngRhs(body),
        .where_clause = null,
        .span = span,
    };
}

pub fn mkAlt(pat: ast.Pattern, body: ast.Expr, span: SourceSpan) ast.Alt {
    return .{
        .pattern = pat,
        .rhs = mkUngRhs(body),
        .where_clause = null,
        .span = span,
    };
}

pub fn mkFunBind(
    arena: Allocator,
    name: []const u8,
    equations: []const ast.Match,
    span: SourceSpan,
) Allocator.Error!ast.FunBinding {
    const owned = try arena.alloc(ast.Match, equations.len);
    @memcpy(owned, equations);
    return .{ .name = name, .equations = owned, .span = span };
}

/// Build an instance head type: `App([Con("ClassName"), <type>])`.
pub fn mkInstanceHead(
    arena: Allocator,
    class_name: []const u8,
    instance_type: ast.Type,
    span: SourceSpan,
) Allocator.Error!ast.Type {
    const parts = try arena.alloc(*const ast.Type, 2);
    parts[0] = try alloc(arena, ast.Type, .{ .Con = mkQName(class_name, span) });
    parts[1] = try alloc(arena, ast.Type, instance_type);
    return .{ .App = parts };
}

/// Build the `T a b ...` type-application expression for a parametric data
/// type's instance head argument.  For nullary type constructors this is
/// just `Con(T)`.
pub fn mkAppliedTypeCon(
    arena: Allocator,
    type_name: []const u8,
    tyvars: []const []const u8,
    span: SourceSpan,
) Allocator.Error!ast.Type {
    const head: ast.Type = .{ .Con = mkQName(type_name, span) };
    if (tyvars.len == 0) return head;
    const parts = try arena.alloc(*const ast.Type, 1 + tyvars.len);
    parts[0] = try alloc(arena, ast.Type, head);
    for (tyvars, 0..) |tv, i| {
        parts[1 + i] = try alloc(arena, ast.Type, .{ .Var = tv });
    }
    return .{ .App = parts };
}

pub const ClassVarPair = struct { class_name: []const u8, tyvar: []const u8 };

/// Build an instance context of the form `(C1 v1, C2 v2, ...) =>` from
/// pairs of (class_name, type_variable).
pub fn mkContext(
    arena: Allocator,
    class_var_pairs: []const ClassVarPair,
) Allocator.Error!?ast.Context {
    if (class_var_pairs.len == 0) return null;
    const constraints = try arena.alloc(ast.Assertion, class_var_pairs.len);
    for (class_var_pairs, 0..) |pair, i| {
        const types = try arena.alloc(ast.Type, 1);
        types[0] = .{ .Var = pair.tyvar };
        constraints[i] = .{ .class_name = pair.class_name, .types = types };
    }
    return .{ .constraints = constraints };
}

pub fn mkInstance(
    arena: Allocator,
    context: ?ast.Context,
    head: ast.Type,
    bindings: []const ast.FunBinding,
    span: SourceSpan,
) Allocator.Error!ast.InstanceDecl {
    const owned = try arena.alloc(ast.FunBinding, bindings.len);
    @memcpy(owned, bindings);
    return .{
        .context = context,
        .constructor_type = head,
        .bindings = owned,
        .span = span,
    };
}

/// Fold a sequence of expressions with infix `&&`, producing `True` for an
/// empty input. Used by the synthesised `Eq` body.
pub fn mkAndChain(
    arena: Allocator,
    exprs: []const ast.Expr,
    span: SourceSpan,
) Allocator.Error!ast.Expr {
    if (exprs.len == 0) return mkVar("True", span);
    if (exprs.len == 1) return exprs[0];
    var acc = exprs[exprs.len - 1];
    var i: usize = exprs.len - 1;
    while (i > 0) : (i -= 1) {
        acc = try mkInfix(arena, exprs[i - 1], "&&", acc, span);
    }
    return acc;
}

/// Fold a sequence of expressions with infix `++`. Empty input returns `""`.
pub fn mkAppendChain(
    arena: Allocator,
    exprs: []const ast.Expr,
    span: SourceSpan,
) Allocator.Error!ast.Expr {
    if (exprs.len == 0) return mkStrLit("", span);
    if (exprs.len == 1) return exprs[0];
    var acc = exprs[exprs.len - 1];
    var i: usize = exprs.len - 1;
    while (i > 0) : (i -= 1) {
        acc = try mkInfix(arena, exprs[i - 1], "++", acc, span);
    }
    return acc;
}

/// Collect every distinct type-variable name appearing in a list of field
/// types, in deterministic order of first appearance. Used to infer instance
/// contexts for parametric data types.
pub fn collectTypeVars(
    arena: Allocator,
    constructors: []const ast.ConDecl,
    seen: *std.StringArrayHashMapUnmanaged(void),
) Allocator.Error!void {
    for (constructors) |c| {
        for (c.fields) |f| {
            const t = switch (f) {
                .Plain => |t| t,
                .Record => |r| r.type,
            };
            try collectTypeVarsIn(arena, t, seen);
        }
    }
}

fn collectTypeVarsIn(
    arena: Allocator,
    t: ast.Type,
    seen: *std.StringArrayHashMapUnmanaged(void),
) Allocator.Error!void {
    switch (t) {
        .Var => |v| try seen.put(arena, v, {}),
        .Con => {},
        .App => |parts| for (parts) |p| try collectTypeVarsIn(arena, p.*, seen),
        .Fun => |parts| for (parts) |p| try collectTypeVarsIn(arena, p.*, seen),
        .Tuple => |parts| for (parts) |p| try collectTypeVarsIn(arena, p.*, seen),
        .List => |p| try collectTypeVarsIn(arena, p.*, seen),
        .Forall => |fa| try collectTypeVarsIn(arena, fa.type.*, seen),
        .Paren => |p| try collectTypeVarsIn(arena, p.*, seen),
        .IParam => |ip| try collectTypeVarsIn(arena, ip.type.*, seen),
    }
}

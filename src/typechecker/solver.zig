//! Constraint solver for the bidirectional typechecker.
//!
//! The typechecker emits *Wanted* equality constraints rather than calling
//! the unifier inline.  This separation keeps each stage independently
//! testable and mirrors GHC's constraint pipeline (simplified for M1).
//!
//! ## Pipeline position
//!
//! ```
//! Bidirectional TC  →  [Constraint]  →  Solver  →  solved MetaVar.ref fields
//!                                           ↓
//!                                    DiagnosticCollector (type errors)
//! ```
//!
//! After `solve` returns, all `MetaVar.ref` fields reachable from the
//! program's `HType` nodes are filled in (or a diagnostic has been emitted
//! for each failure).  The elaborator can then call `HType.toCore()` on
//! every node.
//!
//! ## Error handling
//!
//! The solver does **not** fail fast.  It continues after a unification
//! failure so that a single compilation surfaces as many type errors as
//! possible.  Each failure is turned into a structured `Diagnostic` carrying
//! the `SourceSpan` of the constraint that triggered it.
//!
//! ## M1 scope
//!
//! Only equality constraints (`Constraint.Eq`) are needed for M1.  The
//! design is intentionally open for extension:
//!
//! - M2: add `Constraint.Class` for type class constraints; the solver would
//!   look up instances in `TyEnv` and emit dictionary arguments.
//! - Future: stratified solving (OutsideIn-style), constraint simplification.
//!
//! ## References
//!
//! - Vytiniotis, Peyton Jones et al., "OutsideIn(X)", JFP 2011.
//! - Dunfield & Krishnaswami, "Complete and Easy Bidirectional Typechecking
//!   for Higher-Rank Polymorphism", ICFP 2013.

const std = @import("std");
const htype_mod = @import("htype.zig");
const unify_mod = @import("unify.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");
const span_mod = @import("../diagnostics/span.zig");

pub const HType = htype_mod.HType;
pub const MetaVar = htype_mod.MetaVar;
pub const MetaVarSupply = htype_mod.MetaVarSupply;
pub const UnifyError = unify_mod.UnifyError;
pub const Diagnostic = diag_mod.Diagnostic;
pub const DiagnosticCollector = diag_mod.DiagnosticCollector;
pub const DiagnosticCode = diag_mod.DiagnosticCode;
pub const Severity = diag_mod.Severity;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;

// ── Constraint ─────────────────────────────────────────────────────────

/// An equality constraint emitted by the typechecker: `lhs ~ rhs`.
///
/// `span` records the source location of the expression that caused this
/// constraint to be generated.  The solver uses it to produce diagnostics
/// pointing at the right place in the source.
///
/// Both `lhs` and `rhs` are stored by value here; the solver takes pointers
/// to the copies it holds in the constraint slice so that metavar bindings
/// written by the unifier are visible through those pointers.  Callers must
/// ensure that any `HType` nodes referenced transitively (via `Fun.arg`,
/// `Con.args`, etc.) are allocated on an arena that outlives the solve call.
pub const Constraint = struct {
    lhs: HType,
    rhs: HType,
    /// Source location of the expression that generated this constraint.
    span: SourceSpan,
};

// ── Solver ─────────────────────────────────────────────────────────────

/// Solve a slice of equality constraints by driving Robinson unification.
///
/// For each constraint `lhs ~ rhs`, calls `unify(&lhs, &rhs)`.  On failure,
/// emits a structured `Diagnostic` into `diags` and continues to the next
/// constraint (no fail-fast — collect all errors).
///
/// `alloc` is the typechecker's arena; it is passed through to `unify` for
/// metavar binding allocation.  It is also used to format diagnostic
/// messages.
///
/// Returns `error.OutOfMemory` only if arena allocation fails (a fatal
/// condition distinct from type errors, which are soft failures recorded in
/// `diags`).
pub fn solve(
    constraints: []Constraint,
    alloc: std.mem.Allocator,
    diags: *DiagnosticCollector,
) std.mem.Allocator.Error!void {
    for (constraints) |*c| {
        unify_mod.unify(alloc, &c.lhs, &c.rhs) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.TypeMismatch,
            error.RigidMismatch,
            => {
                const msg = try formatMismatch(alloc, c.lhs, c.rhs);
                try diags.emit(alloc, .{
                    .severity = .@"error",
                    .code = .type_error,
                    .span = c.span,
                    .message = msg,
                });
            },
            error.InfiniteType => {
                const msg = try formatInfiniteType(alloc, c.lhs, c.rhs);
                try diags.emit(alloc, .{
                    .severity = .@"error",
                    .code = .type_error,
                    .span = c.span,
                    .message = msg,
                });
            },
            error.ArityMismatch => {
                const msg = try std.fmt.allocPrint(
                    alloc,
                    "type constructor arity mismatch",
                    .{},
                );
                try diags.emit(alloc, .{
                    .severity = .@"error",
                    .code = .type_error,
                    .span = c.span,
                    .message = msg,
                });
            },
        };
    }
}

// ── Diagnostic message formatting ──────────────────────────────────────

/// Format a human-readable type mismatch message.
///
/// For M1 this is a simple "cannot unify X with Y" string.  A richer
/// pretty-printer (showing the full type tree) can replace this later.
fn formatMismatch(alloc: std.mem.Allocator, lhs: HType, rhs: HType) std.mem.Allocator.Error![]const u8 {
    const lhs_str = try formatHType(alloc, lhs);
    const rhs_str = try formatHType(alloc, rhs);
    return std.fmt.allocPrint(alloc, "cannot unify `{s}` with `{s}`", .{ lhs_str, rhs_str });
}

/// Format an infinite type error message.
fn formatInfiniteType(alloc: std.mem.Allocator, lhs: HType, rhs: HType) std.mem.Allocator.Error![]const u8 {
    const lhs_str = try formatHType(alloc, lhs);
    const rhs_str = try formatHType(alloc, rhs);
    return std.fmt.allocPrint(
        alloc,
        "infinite type: `{s}` ~ `{s}` (occurs check failed)",
        .{ lhs_str, rhs_str },
    );
}

/// Minimal HType formatter for diagnostic messages.
///
/// This is intentionally simple — a proper pretty-printer will be added as
/// part of issue #35 (Core IR pretty-printer) or a dedicated HType printer.
/// For now, names are rendered as their base string and metavars as `?N`.
///
/// Known shortcoming: tracked in follow-up issue #163.
fn formatHType(alloc: std.mem.Allocator, ty: HType) std.mem.Allocator.Error![]const u8 {
    const chased = ty.chase();
    return switch (chased) {
        .Meta => |mv| std.fmt.allocPrint(alloc, "?{d}", .{mv.id}),
        .Rigid => |name| std.fmt.allocPrint(alloc, "{s}", .{name.base}),
        .Con => |c| blk: {
            if (c.args.len == 0) {
                break :blk std.fmt.allocPrint(alloc, "{s}", .{c.name.base});
            }
            // Special-case list: `[] a` → `[a]`
            if (std.mem.eql(u8, c.name.base, "[]") and c.args.len == 1) {
                const arg_str = try formatHType(alloc, c.args[0]);
                break :blk std.fmt.allocPrint(alloc, "[{s}]", .{arg_str});
            }
            // General: `F a b`
            var buf: std.ArrayListUnmanaged(u8) = .empty;
            try buf.appendSlice(alloc, c.name.base);
            for (c.args) |arg| {
                try buf.append(alloc, ' ');
                const arg_str = try formatHType(alloc, arg);
                try buf.appendSlice(alloc, arg_str);
            }
            break :blk try buf.toOwnedSlice(alloc);
        },
        .Fun => |f| blk: {
            const arg_str = try formatHType(alloc, f.arg.*);
            const res_str = try formatHType(alloc, f.res.*);
            break :blk std.fmt.allocPrint(alloc, "{s} -> {s}", .{ arg_str, res_str });
        },
        .ForAll => |fa| blk: {
            const body_str = try formatHType(alloc, fa.body.*);
            break :blk std.fmt.allocPrint(alloc, "forall {s}. {s}", .{ fa.binder.base, body_str });
        },
    };
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

fn testSpan() SourceSpan {
    return SourceSpan.init(
        SourcePos.init(1, 1, 1),
        SourcePos.init(1, 1, 10),
    );
}

fn testName(base: []const u8, id: u64) htype_mod.Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

fn con0(base: []const u8, id: u64) HType {
    return HType{ .Con = .{ .name = testName(base, id), .args = &.{} } };
}

/// Arena-allocate a nullary Con so its address can be taken for Fun.arg/res.
fn dupCon0(alloc: std.mem.Allocator, base: []const u8, id: u64) !*HType {
    const p = try alloc.create(HType);
    p.* = con0(base, id);
    return p;
}

// ── solve: success cases ───────────────────────────────────────────────

test "solve: empty constraint set produces no diagnostics" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena.allocator());

    const constraints: []Constraint = &.{};
    try solve(constraints, arena.allocator(), &diags);
    try testing.expect(!diags.hasErrors());
}

test "solve: single Int ~ Int constraint succeeds" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena.allocator());

    var constraints = [_]Constraint{.{
        .lhs = con0("Int", 0),
        .rhs = con0("Int", 0),
        .span = testSpan(),
    }};
    try solve(&constraints, arena.allocator(), &diags);
    try testing.expect(!diags.hasErrors());
}

test "solve: ?0 ~ Int solves metavar" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    var constraints = [_]Constraint{.{
        .lhs = HType{ .Meta = mv },
        .rhs = con0("Int", 0),
        .span = testSpan(),
    }};
    try solve(&constraints, alloc, &diags);
    try testing.expect(!diags.hasErrors());

    // The metavar in the constraint should now be solved to Int.
    const chased = constraints[0].lhs.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

test "solve: multiple independent constraints all solved" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    const mv0 = supply.fresh();
    const mv1 = supply.fresh();
    var constraints = [_]Constraint{
        .{ .lhs = HType{ .Meta = mv0 }, .rhs = con0("Int", 0), .span = testSpan() },
        .{ .lhs = HType{ .Meta = mv1 }, .rhs = con0("Bool", 1), .span = testSpan() },
    };
    try solve(&constraints, alloc, &diags);
    try testing.expect(!diags.hasErrors());

    try testing.expectEqualStrings("Int", constraints[0].lhs.chase().Con.name.base);
    try testing.expectEqualStrings("Bool", constraints[1].lhs.chase().Con.name.base);
}

// ── solve: failure cases ───────────────────────────────────────────────

test "solve: Int ~ Bool emits TypeMismatch diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var constraints = [_]Constraint{.{
        .lhs = con0("Int", 0),
        .rhs = con0("Bool", 1),
        .span = testSpan(),
    }};
    try solve(&constraints, alloc, &diags);
    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
    try testing.expectEqual(DiagnosticCode.type_error, diags.diagnostics.items[0].code);
}

test "solve: ?0 ~ [?0] emits InfiniteType diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    const meta_ty = HType{ .Meta = mv };
    const args = [_]HType{meta_ty};
    var constraints = [_]Constraint{.{
        .lhs = meta_ty,
        .rhs = HType{ .Con = .{ .name = testName("[]", 99), .args = &args } },
        .span = testSpan(),
    }};
    try solve(&constraints, alloc, &diags);
    try testing.expect(diags.hasErrors());
    // Message should mention "occurs check"
    try testing.expect(std.mem.indexOf(u8, diags.diagnostics.items[0].message, "occurs check") != null);
}

test "solve: conflicting constraints both reported" {
    // ?0 ~ Int, then ?0 ~ Bool — the second should fail after ?0 is solved to Int.
    //
    // For the mutation on constraint[0] to be visible when solving constraint[1],
    // both `lhs` fields must share the same MetaVar storage.  We achieve this by
    // allocating the MetaVar's HType on the arena and building each constraint's
    // `lhs` as a `Fun` that references the shared heap cell.  A simpler way is
    // to allocate the shared HType and use `HType{ .Fun = .{ .arg = shared, ... } }`
    // so both constraints hold a pointer to the *same* MetaVar node.
    //
    // Concretely: build `lhs = ?0 -> ()` for both constraints, where the `arg`
    // pointer is the same heap cell.  After the first solve, `shared.Meta.ref`
    // points to `Int`, and the second solve unifies `Int -> () ~ Bool -> ()`,
    // which fails with TypeMismatch.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    // Allocate the shared metavar cell on the arena so both constraints
    // reference the same underlying HType node.
    const shared = try alloc.create(HType);
    shared.* = HType{ .Meta = supply.fresh() };
    var unit_ty = con0("()", 99);

    var constraints = [_]Constraint{
        .{ .lhs = HType{ .Fun = .{ .arg = shared, .res = &unit_ty } }, .rhs = HType{ .Fun = .{ .arg = try dupCon0(alloc, "Int", 0), .res = &unit_ty } }, .span = testSpan() },
        .{ .lhs = HType{ .Fun = .{ .arg = shared, .res = &unit_ty } }, .rhs = HType{ .Fun = .{ .arg = try dupCon0(alloc, "Bool", 1), .res = &unit_ty } }, .span = testSpan() },
    };
    try solve(&constraints, alloc, &diags);
    try testing.expect(diags.hasErrors());
    // The second constraint fails (Int vs Bool after ?0 = Int).
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
}

test "solve: diagnostic carries correct source span" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const span = SourceSpan.init(
        SourcePos.init(1, 42, 5),
        SourcePos.init(1, 42, 12),
    );
    var constraints = [_]Constraint{.{
        .lhs = con0("Int", 0),
        .rhs = con0("Bool", 1),
        .span = span,
    }};
    try solve(&constraints, alloc, &diags);
    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(u32, 42), diags.diagnostics.items[0].span.start.line);
    try testing.expectEqual(@as(u32, 5), diags.diagnostics.items[0].span.start.column);
}

// ── formatHType ────────────────────────────────────────────────────────

test "formatHType: nullary Con" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const s = try formatHType(arena.allocator(), con0("Int", 0));
    try testing.expectEqualStrings("Int", s);
}

test "formatHType: unsolved Meta" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const ty = HType{ .Meta = MetaVar{ .id = 7, .ref = null } };
    const s = try formatHType(arena.allocator(), ty);
    try testing.expectEqualStrings("?7", s);
}

test "formatHType: Fun type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var int_ty = con0("Int", 0);
    var bool_ty = con0("Bool", 1);
    const ty = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };
    const s = try formatHType(alloc, ty);
    try testing.expectEqualStrings("Int -> Bool", s);
}

test "formatHType: list type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const char_ty = con0("Char", 0);
    const args = [_]HType{char_ty};
    const ty = HType{ .Con = .{ .name = testName("[]", 1), .args = &args } };
    const s = try formatHType(alloc, ty);
    try testing.expectEqualStrings("[Char]", s);
}

test "formatHType: solved Meta renders as solution" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var int_ty = con0("Int", 0);
    const ty = HType{ .Meta = MetaVar{ .id = 0, .ref = &int_ty } };
    const s = try formatHType(alloc, ty);
    try testing.expectEqualStrings("Int", s);
}

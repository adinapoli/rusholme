//! Pattern-match exhaustiveness and redundancy checking (#378).
//!
//! Implements the usefulness algorithm 𝒰rec from Maranget, "Compiling
//! Pattern Matching to Good Decision Trees" (ML'08), §7:
//!
//!   - a match group is exhaustive iff the all-wildcards vector is NOT
//!     useful with respect to its pattern matrix; when it is useful,
//!     a witness (an uncovered value vector) is built along the way;
//!   - equation i is redundant iff its pattern row is not useful with
//!     respect to rows 0..i-1.
//!
//! ## Conservative scope (v1)
//!
//! No false positives by construction; some warnings are skipped:
//!
//!   - Guarded equations may fall through, so they are excluded from the
//!     coverage matrix. A group is only reported non-exhaustive from its
//!     unguarded rows; if guarded rows exist, exhaustiveness reporting is
//!     skipped entirely (a total guard set would be a false positive).
//!     Redundancy is checked for unguarded rows only.
//!   - Record patterns with sub-patterns make the whole group skip
//!     (field-order metadata is not yet plumbed through the renamer).
//!   - Head constructors missing from the signature environment (e.g.
//!     constructors of a type declared in another module) make their
//!     column's signature "open": completeness is never claimed for it.
//!     Cross-module constructor signatures are a tracked follow-up.
//!
//! Reference: http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const renamer_mod = @import("../renamer/renamer.zig");
const known = @import("../naming/known.zig");

const RPat = renamer_mod.RPat;

// ── Signature environment ───────────────────────────────────────────────

/// Maps data constructors to their arity and owning type, and each type
/// to its complete constructor set. Built per module from the renamed
/// data declarations plus the wired-in list/tuple/unit constructors.
pub const SigEnv = struct {
    /// Constructor unique → {arity, type_key}.
    cons: std.AutoHashMapUnmanaged(u64, ConInfo) = .{},
    /// Type key → the type's full constructor set.
    types: std.AutoHashMapUnmanaged(u64, []const ConRef) = .{},

    pub const ConInfo = struct {
        arity: u32,
        /// Identifies the owning type. Any stable value works as long as
        /// all constructors of one type share it; we use the unique of
        /// the type's first constructor.
        type_key: u64,
    };

    pub const ConRef = struct {
        unique: u64,
        base: []const u8,
        arity: u32,
    };

    pub fn deinit(self: *SigEnv, alloc: std.mem.Allocator) void {
        var it = self.types.valueIterator();
        while (it.next()) |refs| alloc.free(refs.*);
        self.types.deinit(alloc);
        self.cons.deinit(alloc);
    }

    /// Register a complete type signature. `refs` is copied.
    pub fn addType(self: *SigEnv, alloc: std.mem.Allocator, refs: []const ConRef) !void {
        if (refs.len == 0) return;
        const owned = try alloc.dupe(ConRef, refs);
        errdefer alloc.free(owned);
        const type_key = owned[0].unique;
        try self.types.put(alloc, type_key, owned);
        for (owned) |r| {
            try self.cons.put(alloc, r.unique, .{ .arity = r.arity, .type_key = type_key });
        }
    }

    /// Seed the wired-in constructors: list, unit, and tuples. Bool,
    /// Maybe, Either etc. come from the Prelude's own `data` declarations.
    pub fn addBuiltins(self: *SigEnv, alloc: std.mem.Allocator) !void {
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Nil.unique.value, .base = "[]", .arity = 0 },
            .{ .unique = known.Con.Cons.unique.value, .base = "(:)", .arity = 2 },
        });
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Unit.unique.value, .base = "()", .arity = 0 },
        });
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Tuple2.unique.value, .base = "(,)", .arity = 2 },
        });
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Tuple3.unique.value, .base = "(,,)", .arity = 3 },
        });
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Tuple4.unique.value, .base = "(,,,)", .arity = 4 },
        });
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Tuple5.unique.value, .base = "(,,,,)", .arity = 5 },
        });
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Tuple6.unique.value, .base = "(,,,,,)", .arity = 6 },
        });
        try self.addType(alloc, &.{
            .{ .unique = known.Con.Tuple7.unique.value, .base = "(,,,,,,)", .arity = 7 },
        });
    }
};

// ── Normalized patterns ─────────────────────────────────────────────────

/// The checker's pattern language: wildcards, constructor patterns, and
/// opaque literals. Var/As/Paren/Negate/List/Tuple/InfixCon are folded
/// into these during normalization.
pub const Pat = union(enum) {
    wild,
    con: Con,
    lit: ast.Literal,

    pub const Con = struct {
        unique: u64,
        base: []const u8,
        args: []const Pat,
    };
};

/// Returned when a pattern uses a feature the checker does not model
/// (currently: record patterns with sub-patterns).
pub const NormalizeError = error{Unsupported} || std.mem.Allocator.Error;

/// Lower an RPat into the checker's pattern language.
pub fn normalize(alloc: std.mem.Allocator, rpat: RPat) NormalizeError!Pat {
    return switch (rpat) {
        .Var => .wild,
        .Wild => .wild,
        .Lit => |l| .{ .lit = l },
        .Paren => |p| normalize(alloc, p.*),
        .AsPat => |a| normalize(alloc, a.pat.*),
        .Negate => |p| blk: {
            const inner = try normalize(alloc, p.*);
            if (inner == .lit and inner.lit == .Int) {
                var negated = inner.lit;
                negated.Int.value = -negated.Int.value;
                break :blk .{ .lit = negated };
            }
            if (inner == .lit and inner.lit == .Float) {
                var negated = inner.lit;
                negated.Float.value = -negated.Float.value;
                break :blk .{ .lit = negated };
            }
            break :blk error.Unsupported;
        },
        .Con => |c| blk: {
            const args = try alloc.alloc(Pat, c.args.len);
            for (c.args, 0..) |a, i| args[i] = try normalize(alloc, a);
            break :blk .{ .con = .{ .unique = c.name.unique.value, .base = c.name.base, .args = args } };
        },
        .InfixCon => |ic| blk: {
            const args = try alloc.alloc(Pat, 2);
            args[0] = try normalize(alloc, ic.left.*);
            args[1] = try normalize(alloc, ic.right.*);
            break :blk .{ .con = .{ .unique = ic.con.unique.value, .base = ic.con.base, .args = args } };
        },
        .Tuple => |ps| blk: {
            const con_name = known.Con.tuple(ps.len) orelse return error.Unsupported;
            const args = try alloc.alloc(Pat, ps.len);
            for (ps, 0..) |p, i| args[i] = try normalize(alloc, p);
            break :blk .{ .con = .{ .unique = con_name.unique.value, .base = con_name.base, .args = args } };
        },
        .List => |ps| blk: {
            // [p1, p2] ≡ p1 : (p2 : [])
            var acc = Pat{ .con = .{
                .unique = known.Con.Nil.unique.value,
                .base = "[]",
                .args = &.{},
            } };
            var i: usize = ps.len;
            while (i > 0) {
                i -= 1;
                const args = try alloc.alloc(Pat, 2);
                args[0] = try normalize(alloc, ps[i]);
                args[1] = acc;
                acc = .{ .con = .{
                    .unique = known.Con.Cons.unique.value,
                    .base = "(:)",
                    .args = args,
                } };
            }
            break :blk acc;
        },
        .RecPat => |rp| blk: {
            // A record pattern with no sub-patterns matches like `Con _ … _`
            // would, but we lack field-order metadata to model constrained
            // fields. Punned/explicit fields therefore bail out.
            if (rp.fields.len != 0) break :blk error.Unsupported;
            const info = .{ .unique = rp.con.unique.value, .base = rp.con.base };
            // Arity unknown here; the matrix ops look it up via SigEnv when
            // specialising, so store no args and let specialise pad. To keep
            // the representation uniform we treat it as unsupported when the
            // arity cannot be resolved — handled in checkMatch.
            _ = info;
            break :blk error.Unsupported;
        },
    };
}

// ── Matrix operations (Maranget §1, §7) ─────────────────────────────────

const Matrix = std.ArrayListUnmanaged([]const Pat);

fn litEql(a: ast.Literal, b: ast.Literal) bool {
    return switch (a) {
        .Int => |x| b == .Int and b.Int.value == x.value,
        .Float => |x| b == .Float and b.Float.value == x.value,
        .Char => |x| b == .Char and b.Char.value == x.value,
        .String => |x| b == .String and std.mem.eql(u8, b.String.value, x.value),
        .Rational => |x| b == .Rational and
            b.Rational.numerator == x.numerator and
            b.Rational.denominator == x.denominator,
    };
}

/// S(c, P): keep rows whose head matches constructor `unique`, expanding
/// the head into its sub-patterns (wildcard heads expand to `arity` wilds).
fn specializeCon(
    alloc: std.mem.Allocator,
    rows: []const []const Pat,
    unique: u64,
    arity: u32,
) ![]const []const Pat {
    var out = Matrix.empty;
    defer out.deinit(alloc);
    for (rows) |row| {
        switch (row[0]) {
            .wild => {
                const new_row = try alloc.alloc(Pat, arity + row.len - 1);
                @memset(new_row[0..arity], .wild);
                @memcpy(new_row[arity..], row[1..]);
                try out.append(alloc, new_row);
            },
            .con => |c| if (c.unique == unique) {
                const new_row = try alloc.alloc(Pat, arity + row.len - 1);
                @memcpy(new_row[0..arity], c.args);
                @memcpy(new_row[arity..], row[1..]);
                try out.append(alloc, new_row);
            },
            .lit => {},
        }
    }
    return out.toOwnedSlice(alloc);
}

/// S(l, P) for a literal head.
fn specializeLit(
    alloc: std.mem.Allocator,
    rows: []const []const Pat,
    lit: ast.Literal,
) ![]const []const Pat {
    var out = Matrix.empty;
    defer out.deinit(alloc);
    for (rows) |row| {
        switch (row[0]) {
            .wild => try out.append(alloc, row[1..]),
            .lit => |l| if (litEql(l, lit)) try out.append(alloc, row[1..]),
            .con => {},
        }
    }
    return out.toOwnedSlice(alloc);
}

/// D(P): keep rows with wildcard heads, dropping the head column.
fn defaultMatrix(alloc: std.mem.Allocator, rows: []const []const Pat) ![]const []const Pat {
    var out = Matrix.empty;
    defer out.deinit(alloc);
    for (rows) |row| {
        if (row[0] == .wild) try out.append(alloc, row[1..]);
    }
    return out.toOwnedSlice(alloc);
}

/// The set of constructors heading the first column, and whether it is a
/// complete signature for its type.
const HeadSig = struct {
    /// Uniques of the constructors that appear as heads.
    seen: std.AutoArrayHashMapUnmanaged(u64, void),
    /// The full constructor set of the column's type, when every head is
    /// known to the SigEnv and the heads cover the whole set.
    complete: ?[]const SigEnv.ConRef,
    /// Any head constructor known to the SigEnv (for witness suggestions
    /// when the signature is incomplete).
    any_known_type: ?[]const SigEnv.ConRef,
    has_lit_heads: bool,

    fn deinit(self: *HeadSig, alloc: std.mem.Allocator) void {
        self.seen.deinit(alloc);
    }
};

fn headSignature(alloc: std.mem.Allocator, sig: *const SigEnv, rows: []const []const Pat) !HeadSig {
    var seen = std.AutoArrayHashMapUnmanaged(u64, void){};
    errdefer seen.deinit(alloc);
    var has_lit = false;
    var type_refs: ?[]const SigEnv.ConRef = null;
    var all_known = true;

    for (rows) |row| {
        switch (row[0]) {
            .con => |c| {
                try seen.put(alloc, c.unique, {});
                if (sig.cons.get(c.unique)) |info| {
                    if (type_refs == null) type_refs = sig.types.get(info.type_key);
                } else {
                    all_known = false;
                }
            },
            .lit => has_lit = true,
            .wild => {},
        }
    }

    const complete: ?[]const SigEnv.ConRef = blk: {
        if (has_lit or !all_known) break :blk null;
        const refs = type_refs orelse break :blk null;
        if (seen.count() == refs.len) break :blk refs;
        break :blk null;
    };

    return .{
        .seen = seen,
        .complete = complete,
        .any_known_type = type_refs,
        .has_lit_heads = has_lit,
    };
}

// ── Usefulness (Maranget §7) ────────────────────────────────────────────

/// 𝒰(P, q⃗): is there a value vector matched by q⃗ but by no row of P?
pub fn useful(
    alloc: std.mem.Allocator,
    sig: *const SigEnv,
    rows: []const []const Pat,
    q: []const Pat,
) std.mem.Allocator.Error!bool {
    if (q.len == 0) return rows.len == 0;

    switch (q[0]) {
        .con => |c| {
            const arity: u32 = @intCast(c.args.len);
            const spec = try specializeCon(alloc, rows, c.unique, arity);
            const new_q = try alloc.alloc(Pat, arity + q.len - 1);
            @memcpy(new_q[0..arity], c.args);
            @memcpy(new_q[arity..], q[1..]);
            return useful(alloc, sig, spec, new_q);
        },
        .lit => |l| {
            const spec = try specializeLit(alloc, rows, l);
            return useful(alloc, sig, spec, q[1..]);
        },
        .wild => {
            var hs = try headSignature(alloc, sig, rows);
            defer hs.deinit(alloc);

            if (hs.complete) |refs| {
                for (refs) |r| {
                    const spec = try specializeCon(alloc, rows, r.unique, r.arity);
                    const new_q = try alloc.alloc(Pat, r.arity + q.len - 1);
                    @memset(new_q[0..r.arity], .wild);
                    @memcpy(new_q[r.arity..], q[1..]);
                    if (try useful(alloc, sig, spec, new_q)) return true;
                }
                return false;
            }

            const def = try defaultMatrix(alloc, rows);
            return useful(alloc, sig, def, q[1..]);
        },
    }
}

/// Find an uncovered value vector of width `n`, or null if `rows` is
/// exhaustive. The witness uses `wild` where any value works.
pub fn findWitness(
    alloc: std.mem.Allocator,
    sig: *const SigEnv,
    rows: []const []const Pat,
    n: usize,
) std.mem.Allocator.Error!?[]const Pat {
    if (n == 0) {
        if (rows.len == 0) return &[_]Pat{};
        return null;
    }

    var hs = try headSignature(alloc, sig, rows);
    defer hs.deinit(alloc);

    if (hs.complete) |refs| {
        for (refs) |r| {
            const spec = try specializeCon(alloc, rows, r.unique, r.arity);
            const sub = try findWitness(alloc, sig, spec, r.arity + n - 1) orelse continue;
            const args = try alloc.dupe(Pat, sub[0..r.arity]);
            const out = try alloc.alloc(Pat, n);
            out[0] = .{ .con = .{ .unique = r.unique, .base = r.base, .args = args } };
            @memcpy(out[1..], sub[r.arity..]);
            return out;
        }
        return null;
    }

    const def = try defaultMatrix(alloc, rows);
    const sub = try findWitness(alloc, sig, def, n - 1) orelse return null;

    const out = try alloc.alloc(Pat, n);
    // Suggest a constructor missing from the head set when the column's
    // type is known; otherwise a wildcard stands for "any value not
    // matched above" (e.g. an uncovered integer literal).
    out[0] = .wild;
    if (hs.any_known_type) |refs| {
        for (refs) |r| {
            if (!hs.seen.contains(r.unique)) {
                const args = try alloc.alloc(Pat, r.arity);
                @memset(args, .wild);
                out[0] = .{ .con = .{ .unique = r.unique, .base = r.base, .args = args } };
                break;
            }
        }
    }
    @memcpy(out[1..], sub);
    return out;
}

// ── Public entry point ──────────────────────────────────────────────────

pub const CheckResult = struct {
    /// An uncovered value vector, or null when the unguarded rows are
    /// exhaustive. Only reported when no row was guarded (see module doc).
    missing: ?[]const Pat,
    /// Indices (into the original equation list) of redundant rows.
    redundant: []const usize,
};

/// Check one match group (function equations or case alternatives).
///
/// `equations[i]` is equation i's pattern row; `guarded[i]` marks rows
/// whose RHS has guards. Returns null when the group uses unsupported
/// patterns (record sub-patterns) — no warnings should be emitted then.
///
/// All allocations come from `alloc`; pass an arena.
pub fn checkMatch(
    alloc: std.mem.Allocator,
    sig: *const SigEnv,
    equations: []const []const RPat,
    guarded: []const bool,
) std.mem.Allocator.Error!?CheckResult {
    std.debug.assert(equations.len == guarded.len);
    if (equations.len == 0) return null;
    const width = equations[0].len;

    // Normalize all rows; any unsupported pattern skips the whole group.
    var rows = try alloc.alloc([]const Pat, equations.len);
    for (equations, 0..) |eq, i| {
        const row = try alloc.alloc(Pat, width);
        for (eq, 0..) |p, j| {
            row[j] = normalize(alloc, p) catch |err| switch (err) {
                error.Unsupported => return null,
                error.OutOfMemory => return error.OutOfMemory,
            };
        }
        rows[i] = row;
    }

    var any_guarded = false;
    for (guarded) |g| {
        if (g) any_guarded = true;
    }

    // ── Redundancy: row i vs the unguarded rows before it ──────────────
    var redundant = std.ArrayListUnmanaged(usize).empty;
    defer redundant.deinit(alloc);
    {
        var prefix = std.ArrayListUnmanaged([]const Pat).empty;
        defer prefix.deinit(alloc);
        for (rows, 0..) |row, i| {
            if (!try useful(alloc, sig, prefix.items, row)) {
                try redundant.append(alloc, i);
            }
            // Guarded rows may fall through — they contribute no coverage.
            if (!guarded[i]) try prefix.append(alloc, row);
        }
    }

    // ── Exhaustiveness: skip when guards could cover the remainder ─────
    var missing: ?[]const Pat = null;
    if (!any_guarded) {
        var unguarded = std.ArrayListUnmanaged([]const Pat).empty;
        defer unguarded.deinit(alloc);
        for (rows, 0..) |row, i| {
            if (!guarded[i]) try unguarded.append(alloc, row);
        }
        missing = try findWitness(alloc, sig, unguarded.items, width);
    }

    return .{
        .missing = missing,
        .redundant = try redundant.toOwnedSlice(alloc),
    };
}

/// Render a witness pattern vector for a warning message, e.g. "Just _ []".
pub fn formatWitness(alloc: std.mem.Allocator, witness: []const Pat) ![]u8 {
    var buf = std.ArrayListUnmanaged(u8).empty;
    defer buf.deinit(alloc);
    for (witness, 0..) |p, i| {
        if (i > 0) try buf.append(alloc, ' ');
        try formatPat(alloc, &buf, p, false);
    }
    return buf.toOwnedSlice(alloc);
}

fn formatPat(
    alloc: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    p: Pat,
    nested: bool,
) !void {
    switch (p) {
        .wild => try buf.append(alloc, '_'),
        .lit => |l| switch (l) {
            .Int => |v| try buf.print(alloc, "{d}", .{v.value}),
            .Float => |v| try buf.print(alloc, "{d}", .{v.value}),
            .Char => |v| try buf.print(alloc, "'{u}'", .{v.value}),
            .String => |s| try buf.print(alloc, "\"{s}\"", .{s.value}),
            .Rational => |r| try buf.print(alloc, "{d}/{d}", .{ r.numerator, r.denominator }),
        },
        .con => |c| {
            const needs_parens = nested and c.args.len > 0;
            if (needs_parens) try buf.append(alloc, '(');
            try buf.appendSlice(alloc, c.base);
            for (c.args) |a| {
                try buf.append(alloc, ' ');
                try formatPat(alloc, buf, a, true);
            }
            if (needs_parens) try buf.append(alloc, ')');
        },
    }
}

// ── Tests ───────────────────────────────────────────────────────────────

const testing = std.testing;

const span_mod = @import("../diagnostics/span.zig");

fn testSpan() span_mod.SourceSpan {
    return span_mod.SourceSpan.init(span_mod.SourcePos.init(1, 1, 1), span_mod.SourcePos.init(1, 1, 2));
}

/// Build a tiny Bool-like signature: data B = F | T (uniques 9001/9002).
fn boolSig(alloc: std.mem.Allocator) !SigEnv {
    var sig = SigEnv{};
    try sig.addType(alloc, &.{
        .{ .unique = 9001, .base = "F", .arity = 0 },
        .{ .unique = 9002, .base = "T", .arity = 0 },
    });
    return sig;
}

/// data M = N | J x (uniques 9011/9012) — a Maybe lookalike.
fn maybeSig(alloc: std.mem.Allocator) !SigEnv {
    var sig = SigEnv{};
    try sig.addType(alloc, &.{
        .{ .unique = 9011, .base = "N", .arity = 0 },
        .{ .unique = 9012, .base = "J", .arity = 1 },
    });
    return sig;
}

fn conPat(unique: u64, base: []const u8, args: []const Pat) Pat {
    return .{ .con = .{ .unique = unique, .base = base, .args = args } };
}

test "useful: missing T branch is detected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = try boolSig(alloc);
    defer sig.deinit(alloc);

    // P = [ [F] ]; q = [_] — useful (T uncovered).
    const rows = [_][]const Pat{&[_]Pat{conPat(9001, "F", &.{})}};
    try testing.expect(try useful(alloc, &sig, &rows, &[_]Pat{.wild}));
}

test "useful: complete signature makes wildcard row redundant check work" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = try boolSig(alloc);
    defer sig.deinit(alloc);

    // P = [ [F], [T] ]; q = [_] — NOT useful (both covered).
    const rows = [_][]const Pat{
        &[_]Pat{conPat(9001, "F", &.{})},
        &[_]Pat{conPat(9002, "T", &.{})},
    };
    try testing.expect(!try useful(alloc, &sig, &rows, &[_]Pat{.wild}));
}

test "findWitness: reports J _ when only N is matched" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = try maybeSig(alloc);
    defer sig.deinit(alloc);

    const rows = [_][]const Pat{&[_]Pat{conPat(9011, "N", &.{})}};
    const w = (try findWitness(alloc, &sig, &rows, 1)).?;
    const txt = try formatWitness(alloc, w);
    try testing.expectEqualStrings("J _", txt);
}

test "findWitness: exhaustive nested match returns null" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = try maybeSig(alloc);
    defer sig.deinit(alloc);

    // case m of { N -> …; J _ -> … }
    const j_args = [_]Pat{.wild};
    const rows = [_][]const Pat{
        &[_]Pat{conPat(9011, "N", &.{})},
        &[_]Pat{conPat(9012, "J", &j_args)},
    };
    try testing.expect(try findWitness(alloc, &sig, &rows, 1) == null);
}

test "findWitness: nested constructor witness J (J _) style" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = try maybeSig(alloc);
    defer sig.deinit(alloc);

    // case m of { N -> …; J N -> … }   — missing: J (J _)
    const j_n = [_]Pat{conPat(9011, "N", &.{})};
    const rows = [_][]const Pat{
        &[_]Pat{conPat(9011, "N", &.{})},
        &[_]Pat{conPat(9012, "J", &j_n)},
    };
    const w = (try findWitness(alloc, &sig, &rows, 1)).?;
    const txt = try formatWitness(alloc, w);
    try testing.expectEqualStrings("J (J _)", txt);
}

test "findWitness: integer literals are never complete" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = SigEnv{};
    defer sig.deinit(alloc);

    // f 0 = …; f 1 = … — non-exhaustive, witness "_" (any other Int).
    const rows = [_][]const Pat{
        &[_]Pat{.{ .lit = .{ .Int = .{ .value = 0, .span = testSpan() } } }},
        &[_]Pat{.{ .lit = .{ .Int = .{ .value = 1, .span = testSpan() } } }},
    };
    const w = (try findWitness(alloc, &sig, &rows, 1)).?;
    const txt = try formatWitness(alloc, w);
    try testing.expectEqualStrings("_", txt);
}

test "findWitness: wildcard row makes any match exhaustive" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = SigEnv{};
    defer sig.deinit(alloc);

    const rows = [_][]const Pat{
        &[_]Pat{.{ .lit = .{ .Int = .{ .value = 0, .span = testSpan() } } }},
        &[_]Pat{.wild},
    };
    try testing.expect(try findWitness(alloc, &sig, &rows, 1) == null);
}

test "checkMatch: redundant duplicate equation flagged" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = SigEnv{};
    try sig.addBuiltins(alloc);
    defer sig.deinit(alloc);

    // f _ = …; f 1 = … — second equation unreachable.
    const eq0 = [_]RPat{.{ .Wild = testSpan() }};
    const eq1 = [_]RPat{.{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } }};
    const eqs = [_][]const RPat{ &eq0, &eq1 };
    const guards = [_]bool{ false, false };

    const result = (try checkMatch(alloc, &sig, &eqs, &guards)).?;
    try testing.expect(result.missing == null);
    try testing.expectEqualSlices(usize, &.{1}, result.redundant);
}

test "checkMatch: list patterns via builtins — missing [] case" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = SigEnv{};
    try sig.addBuiltins(alloc);
    defer sig.deinit(alloc);

    // f (x:xs) = … — missing [].
    const x = RPat{ .Var = .{ .name = .{ .base = "x", .unique = .{ .value = 7001 } }, .span = testSpan() } };
    const xs = RPat{ .Var = .{ .name = .{ .base = "xs", .unique = .{ .value = 7002 } }, .span = testSpan() } };
    const cons_pat = RPat{ .InfixCon = .{
        .left = &x,
        .con = known.Con.Cons,
        .con_span = testSpan(),
        .right = &xs,
    } };
    const eq0 = [_]RPat{cons_pat};
    const eqs = [_][]const RPat{&eq0};
    const guards = [_]bool{false};

    const result = (try checkMatch(alloc, &sig, &eqs, &guards)).?;
    try testing.expect(result.missing != null);
    const txt = try formatWitness(alloc, result.missing.?);
    try testing.expectEqualStrings("[]", txt);
    try testing.expectEqual(@as(usize, 0), result.redundant.len);
}

test "checkMatch: guarded rows suppress exhaustiveness, keep redundancy" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = SigEnv{};
    try sig.addBuiltins(alloc);
    defer sig.deinit(alloc);

    // f x | g x = …; f _ = … — no exhaustiveness claim, no redundancy.
    const x = RPat{ .Var = .{ .name = .{ .base = "x", .unique = .{ .value = 7003 } }, .span = testSpan() } };
    const eq0 = [_]RPat{x};
    const eq1 = [_]RPat{.{ .Wild = testSpan() }};
    const eqs = [_][]const RPat{ &eq0, &eq1 };
    const guards = [_]bool{ true, false };

    const result = (try checkMatch(alloc, &sig, &eqs, &guards)).?;
    try testing.expect(result.missing == null);
    // Row 1 is NOT redundant: row 0 is guarded and contributes no coverage.
    try testing.expectEqual(@as(usize, 0), result.redundant.len);
}

test "checkMatch: unknown constructors keep the signature open" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var sig = SigEnv{};
    try sig.addBuiltins(alloc);
    defer sig.deinit(alloc);

    // f (Foo) = … with Foo from another module: cannot claim completeness,
    // so the match is reported non-exhaustive with a wildcard witness.
    const foo = RPat{ .Con = .{
        .name = .{ .base = "Foo", .unique = .{ .value = 8800 } },
        .con_span = testSpan(),
        .args = &.{},
    } };
    const eq0 = [_]RPat{foo};
    const eqs = [_][]const RPat{&eq0};
    const guards = [_]bool{false};

    const result = (try checkMatch(alloc, &sig, &eqs, &guards)).?;
    try testing.expect(result.missing != null);
    const txt = try formatWitness(alloc, result.missing.?);
    try testing.expectEqualStrings("_", txt);
}

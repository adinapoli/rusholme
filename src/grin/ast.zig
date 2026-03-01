//! GRIN IR types (Modern GRIN dialect, Hruska et al. 2020).
//!
//! GRIN (Graph Reduction Intermediate Notation) is an imperative-monadic
//! intermediate representation where memory operations (store/fetch/update)
//! and laziness are explicit. It replaces both STG and Cmm in Rusholme's
//! pipeline.
//!
//! Reference: Podlovics, Hruska & Pénzes, "A Modern Look at GRIN", 2020.
//! Reference implementation: https://github.com/grin-compiler/grin

const std = @import("std");
const naming = @import("../naming/unique.zig");
const span_mod = @import("../diagnostics/span.zig");

pub const Name = naming.Name;
pub const Unique = naming.Unique;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;

// ── Tags ───────────────────────────────────────────────────────────────

/// Tag kind: distinguishes constructors, function closures, and partial
/// applications in the GRIN heap.
pub const TagType = union(enum) {
    /// Data constructor (e.g. `CJust`, `CCons`).
    Con: void,

    /// Function closure / thunk (e.g. `Fmap`, `Ffoldr`).
    Fun: void,

    /// Partial application, with the number of missing arguments.
    Partial: u32,
};

/// A GRIN tag: combines the tag kind with a name.
///
/// Examples: `CJust`, `FmyFunc`, `P2myFunc` (partial application missing 2 args).
pub const Tag = struct {
    tag_type: TagType,
    name: Name,

    pub fn eql(self: Tag, other: Tag) bool {
        const type_match = switch (self.tag_type) {
            .Con => other.tag_type == .Con,
            .Fun => other.tag_type == .Fun,
            .Partial => |n| switch (other.tag_type) {
                .Partial => |m| n == m,
                else => false,
            },
        };
        return type_match and self.name.eql(other.name);
    }

    /// Formats as `C:name`, `F:name`, or `P(n):name`.
    pub fn format(self: Tag, w: *std.Io.Writer) std.Io.Writer.Error!void {
        switch (self.tag_type) {
            .Con => try w.print("C:{f}", .{self.name}),
            .Fun => try w.print("F:{f}", .{self.name}),
            .Partial => |n| try w.print("P({d}):{f}", .{ n, self.name }),
        }
    }
};

// ── Field types for HPT-lite ───────────────────────────────────────────

/// Field types tracked by HPT-lite for LLVM codegen.
/// This is a simplified type system that will be extended when
/// implementing full Heap Points-to Analysis (M2.4).
///
/// See: https://github.com/adinapoli/rusholme/issues/449
/// Reference: Podlovics, Hruska & Pénzes, "Compiling Lazy Functional
/// Programs to LLVM IR", 2020, Section 4.2.
pub const FieldType = enum {
    /// Integer or character (64-bit).
    i64,
    /// Floating-point (64-bit).
    f64,
    /// Heap pointer (to another node).
    ptr,
};

// ── Literals ───────────────────────────────────────────────────────────

/// GRIN-level literal values.
pub const Literal = union(enum) {
    Int: i64,
    Float: f64,
    Bool: bool,
    Char: u21,
    String: []const u8,
};

// ── Values ─────────────────────────────────────────────────────────────

/// A GRIN value. Used as expressions, patterns (LPat), and simple values.
///
/// In the reference GRIN, `Val` serves triple duty: as values in
/// expressions, as left-hand patterns in bind, and as simple values
/// passed to applications. Type aliases distinguish these roles
/// semantically, but the underlying type is the same.
pub const Val = union(enum) {
    /// Fully applied constructor/function node: tag + fields.
    /// E.g. `CJust [x]`, `CCons [head, tail]`.
    ConstTagNode: struct { tag: Tag, fields: []const Val },

    /// Node where the tag is a variable (used in eval/apply).
    VarTagNode: struct { tag_var: Name, fields: []const Val },

    /// A bare tag value (no payload).
    ValTag: Tag,

    /// Unit value `()`.
    Unit: void,

    /// Literal value.
    Lit: Literal,

    /// Variable reference.
    Var: Name,
};

// ── Case patterns ──────────────────────────────────────────────────────

/// Pattern in a case alternative.
pub const CPat = union(enum) {
    /// Match a constructor node, binding field names.
    NodePat: struct { tag: Tag, fields: []const Name },

    /// Match a literal value.
    LitPat: Literal,

    /// Match a bare tag (no fields).
    TagPat: Tag,

    /// Default / wildcard pattern.
    DefaultPat: void,
};

// ── Expressions ────────────────────────────────────────────────────────

/// A case alternative: pattern + body.
pub const Alt = struct {
    pat: CPat,
    body: *const Expr,
};

/// GRIN expression — the heart of the IR.
///
/// GRIN is a monadic language. Sequencing is done via `Bind`:
///   `expr >>= \pat -> expr`
///
/// Simple expressions (SApp, SReturn, SStore, SFetch, SUpdate) produce
/// values. Compound expressions (EBind, ECase) compose them.
pub const Expr = union(enum) {
    /// Monadic bind / sequencing: evaluate `lhs`, bind result to `pat`,
    /// then evaluate `rhs`.
    /// Corresponds to: `do { pat <- lhs; rhs }`
    Bind: struct { lhs: *const Expr, pat: Val, rhs: *const Expr },

    /// Case expression: scrutinise a value and branch.
    Case: struct { scrutinee: Val, alts: []const Alt },

    /// Function / primitive application.
    App: struct { name: Name, args: []const Val },

    /// Return a value (no side effects).
    Return: Val,

    /// Allocate a node on the heap, return a pointer to it.
    Store: Val,

    /// Read a node from a heap pointer. Optional field index for
    /// optimised fetches (fetch the whole node when null).
    Fetch: struct { ptr: Name, index: ?u32 },

    /// Overwrite a heap node at the given pointer.
    Update: struct { ptr: Name, val: Val },

    /// Block expression (scoping).
    Block: *const Expr,
};

// ── Top-level definitions ──────────────────────────────────────────────

/// A top-level GRIN function definition.
pub const Def = struct {
    name: Name,
    params: []const Name,
    body: *const Expr,
};

/// A complete GRIN program.
pub const Program = struct {
    defs: []const Def,
};

// ── Simple types (for analysis) ────────────────────────────────────────

/// GRIN simple types, used in type analysis and heap-points-to results.
pub const SimpleType = enum {
    T_Int64,
    T_Float,
    T_Bool,
    T_Char,
    T_String,
    T_Unit,
    T_Dead,
};

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

fn testName(base: []const u8, unique: u64) Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn conTag(base: []const u8, unique: u64) Tag {
    return .{ .tag_type = .{ .Con = {} }, .name = testName(base, unique) };
}

fn funTag(base: []const u8, unique: u64) Tag {
    return .{ .tag_type = .{ .Fun = {} }, .name = testName(base, unique) };
}

test "Tag: constructor" {
    const tag = conTag("Just", 1);
    try testing.expectEqualStrings("Just", tag.name.base);
    try testing.expect(tag.tag_type == .Con);
}

test "Tag: function" {
    const tag = funTag("map", 2);
    try testing.expectEqualStrings("map", tag.name.base);
    try testing.expect(tag.tag_type == .Fun);
}

test "Tag: partial application" {
    const tag = Tag{ .tag_type = .{ .Partial = 2 }, .name = testName("map", 3) };
    try testing.expectEqual(@as(u32, 2), tag.tag_type.Partial);
}

test "Tag.eql: same tags" {
    const a = conTag("Just", 1);
    const b = conTag("Just", 1);
    try testing.expect(a.eql(b));
}

test "Tag.eql: different tag types" {
    const a = conTag("f", 1);
    const b = funTag("f", 1);
    try testing.expect(!a.eql(b));
}

test "Tag.format: constructor" {
    const tag = conTag("Just", 1);
    var buf: [64]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{tag});
    try testing.expectEqualStrings("C:Just_1", result);
}

test "Tag.format: partial application" {
    const tag = Tag{ .tag_type = .{ .Partial = 2 }, .name = testName("map", 3) };
    var buf: [64]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{tag});
    try testing.expectEqualStrings("P(2):map_3", result);
}

test "Literal: all variants" {
    const lit_int = Literal{ .Int = 42 };
    try testing.expectEqual(@as(i64, 42), lit_int.Int);

    const lit_float = Literal{ .Float = 3.14 };
    try testing.expectEqual(@as(f64, 3.14), lit_float.Float);

    const lit_bool = Literal{ .Bool = true };
    try testing.expect(lit_bool.Bool);

    const lit_char = Literal{ .Char = 'x' };
    try testing.expectEqual(@as(u21, 'x'), lit_char.Char);

    const lit_str = Literal{ .String = "hello" };
    try testing.expectEqualStrings("hello", lit_str.String);
}

test "Val: ConstTagNode" {
    const fields = [_]Val{
        .{ .Lit = .{ .Int = 42 } },
    };
    const val = Val{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &fields,
    } };
    try testing.expectEqual(@as(usize, 1), val.ConstTagNode.fields.len);
}

test "Val: VarTagNode" {
    const val = Val{ .VarTagNode = .{
        .tag_var = testName("t", 5),
        .fields = &.{},
    } };
    try testing.expectEqualStrings("t", val.VarTagNode.tag_var.base);
}

test "Val: Unit, Lit, Var" {
    const unit = Val{ .Unit = {} };
    _ = unit;

    const lit = Val{ .Lit = .{ .Int = 7 } };
    try testing.expectEqual(@as(i64, 7), lit.Lit.Int);

    const v = Val{ .Var = testName("x", 1) };
    try testing.expectEqualStrings("x", v.Var.base);
}

test "CPat: all variants" {
    const node_pat = CPat{ .NodePat = .{
        .tag = conTag("Cons", 1),
        .fields = &.{ testName("h", 2), testName("t", 3) },
    } };
    try testing.expectEqual(@as(usize, 2), node_pat.NodePat.fields.len);

    const lit_pat = CPat{ .LitPat = .{ .Int = 0 } };
    try testing.expectEqual(@as(i64, 0), lit_pat.LitPat.Int);

    const tag_pat = CPat{ .TagPat = conTag("Nil", 4) };
    try testing.expectEqualStrings("Nil", tag_pat.TagPat.name.base);

    const def_pat = CPat{ .DefaultPat = {} };
    _ = def_pat;
}

test "Expr.Return" {
    const e = Expr{ .Return = .{ .Lit = .{ .Int = 42 } } };
    try testing.expectEqual(@as(i64, 42), e.Return.Lit.Int);
}

test "Expr.App" {
    const args = [_]Val{.{ .Var = testName("x", 1) }};
    const e = Expr{ .App = .{
        .name = testName("f", 2),
        .args = &args,
    } };
    try testing.expectEqualStrings("f", e.App.name.base);
    try testing.expectEqual(@as(usize, 1), e.App.args.len);
}

test "Expr.Store" {
    const e = Expr{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 5 } }},
    } } };
    try testing.expectEqualStrings("Just", e.Store.ConstTagNode.tag.name.base);
}

test "Expr.Fetch" {
    const e = Expr{ .Fetch = .{ .ptr = testName("p", 1), .index = null } };
    try testing.expectEqualStrings("p", e.Fetch.ptr.base);
    try testing.expect(e.Fetch.index == null);
}

test "Expr.Fetch: with field index" {
    const e = Expr{ .Fetch = .{ .ptr = testName("p", 1), .index = 2 } };
    try testing.expectEqual(@as(u32, 2), e.Fetch.index.?);
}

test "Expr.Update" {
    const e = Expr{ .Update = .{
        .ptr = testName("p", 1),
        .val = .{ .ConstTagNode = .{
            .tag = conTag("Just", 2),
            .fields = &.{.{ .Lit = .{ .Int = 99 } }},
        } },
    } };
    try testing.expectEqualStrings("p", e.Update.ptr.base);
}

test "Expr.Case: with alternatives" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body1 = try alloc.create(Expr);
    body1.* = .{ .Return = .{ .Lit = .{ .Int = 1 } } };

    const body2 = try alloc.create(Expr);
    body2.* = .{ .Return = .{ .Lit = .{ .Int = 0 } } };

    const alts = try alloc.alloc(Alt, 2);
    alts[0] = .{
        .pat = .{ .NodePat = .{
            .tag = conTag("True", 1),
            .fields = &.{},
        } },
        .body = body1,
    };
    alts[1] = .{
        .pat = .{ .DefaultPat = {} },
        .body = body2,
    };

    const case = Expr{ .Case = .{
        .scrutinee = .{ .Var = testName("b", 5) },
        .alts = alts,
    } };
    try testing.expectEqual(@as(usize, 2), case.Case.alts.len);
}

test "Expr.Bind: sequencing" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // store (CJust [42])
    const lhs = try alloc.create(Expr);
    lhs.* = .{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 42 } }},
    } } };

    // fetch p
    const rhs = try alloc.create(Expr);
    rhs.* = .{ .Fetch = .{ .ptr = testName("p", 2), .index = null } };

    // store (CJust [42]) >>= \p -> fetch p
    const bind = Expr{ .Bind = .{
        .lhs = lhs,
        .pat = .{ .Var = testName("p", 2) },
        .rhs = rhs,
    } };
    try testing.expectEqualStrings("p", bind.Bind.pat.Var.base);
}

test "Def: function definition" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(Expr);
    body.* = .{ .Return = .{ .Var = testName("x", 2) } };

    const params = try alloc.alloc(Name, 1);
    params[0] = testName("x", 2);

    const def = Def{
        .name = testName("id", 1),
        .params = params,
        .body = body,
    };
    try testing.expectEqualStrings("id", def.name.base);
    try testing.expectEqual(@as(usize, 1), def.params.len);
}

test "Program: list of defs" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(Expr);
    body.* = .{ .Return = .{ .Unit = {} } };

    const defs = try alloc.alloc(Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const prog = Program{ .defs = defs };
    try testing.expectEqual(@as(usize, 1), prog.defs.len);
}

test "Nested: store >> bind >> case (eval pattern)" {
    // Represents:
    //   store (CJust [42]) >>= \p ->
    //     fetch p >>= \val ->
    //       case val of
    //         (CJust [x]) -> return x
    //         _ -> return 0
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Innermost: case val of ...
    const ret_x = try alloc.create(Expr);
    ret_x.* = .{ .Return = .{ .Var = testName("x", 10) } };

    const ret_zero = try alloc.create(Expr);
    ret_zero.* = .{ .Return = .{ .Lit = .{ .Int = 0 } } };

    const alts = try alloc.alloc(Alt, 2);
    alts[0] = .{
        .pat = .{ .NodePat = .{
            .tag = conTag("Just", 1),
            .fields = &.{testName("x", 10)},
        } },
        .body = ret_x,
    };
    alts[1] = .{
        .pat = .{ .DefaultPat = {} },
        .body = ret_zero,
    };

    const case_expr = try alloc.create(Expr);
    case_expr.* = .{ .Case = .{
        .scrutinee = .{ .Var = testName("val", 4) },
        .alts = alts,
    } };

    // fetch p >>= \val -> case ...
    const fetch_expr = try alloc.create(Expr);
    fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 3), .index = null } };

    const inner_bind = try alloc.create(Expr);
    inner_bind.* = .{ .Bind = .{
        .lhs = fetch_expr,
        .pat = .{ .Var = testName("val", 4) },
        .rhs = case_expr,
    } };

    // store (CJust [42]) >>= \p -> ...
    const store_expr = try alloc.create(Expr);
    store_expr.* = .{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 42 } }},
    } } };

    const outer_bind = Expr{ .Bind = .{
        .lhs = store_expr,
        .pat = .{ .Var = testName("p", 3) },
        .rhs = inner_bind,
    } };

    // Verify structure
    try testing.expectEqualStrings("p", outer_bind.Bind.pat.Var.base);
    const inner = outer_bind.Bind.rhs;
    try testing.expectEqualStrings("val", inner.Bind.pat.Var.base);
    const case_node = inner.Bind.rhs;
    try testing.expectEqual(@as(usize, 2), case_node.Case.alts.len);
    try testing.expectEqualStrings("x", case_node.Case.alts[0].body.Return.Var.base);
}

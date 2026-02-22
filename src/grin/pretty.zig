//! GRIN IR Pretty-Printer.
//!
//! Renders GRIN IR into a readable string representation using the
//! conventional syntax from the GRIN papers (Boquist 1999, Hruska et al.
//! 2020). Writes directly to any `std.io.Writer` to avoid allocations.
//!
//! Syntax conventions:
//!   - Monadic bind:      `lhs ; \pat -> rhs`  (semicolon-separated)
//!   - Store:             `store node`
//!   - Fetch:             `fetch ptr` or `fetch ptr[i]`
//!   - Update:            `update ptr val`
//!   - Return:            `pure val`
//!   - Application:       `name arg1 arg2`
//!   - Case:              `case val of { alt1 ; alt2 }`
//!   - Tags:              `CJust`, `Fmap`, `P(2)map`
//!   - Nodes:             `(CJust x y)` or `(Fmap x)`
//!
//! Reference: Hruska et al. 2020, Section 3; Boquist 1999, Chapter 4.

const std = @import("std");
const ir = @import("ast.zig");

/// A pretty-printer for GRIN IR that writes directly to any `std.io.Writer`.
pub fn GrinPrinter(comptime WriterType: type) type {
    return struct {
        writer: WriterType,
        indent_level: u32 = 0,

        const Self = @This();
        const INDENT_WIDTH = 2;

        pub fn init(writer: WriterType) Self {
            return .{ .writer = writer };
        }

        // ── Writing helpers ────────────────────────────────────────────

        fn write(self: *Self, bytes: []const u8) anyerror!void {
            try self.writer.writeAll(bytes);
        }

        fn writeByte(self: *Self, byte: u8) anyerror!void {
            try self.writer.writeByte(byte);
        }

        fn writeIndent(self: *Self) anyerror!void {
            const spaces = self.indent_level * INDENT_WIDTH;
            for (0..spaces) |_| {
                try self.writeByte(' ');
            }
        }

        fn newline(self: *Self) anyerror!void {
            try self.writeByte('\n');
        }

        fn indent(self: *Self) void {
            self.indent_level += 1;
        }

        fn dedent(self: *Self) void {
            self.indent_level -= 1;
        }

        // ── Names ──────────────────────────────────────────────────────

        pub fn printName(self: *Self, name: ir.Name) anyerror!void {
            if (name.unique.value == 0) {
                try self.write(name.base);
            } else {
                var buf: [128]u8 = undefined;
                const s = try std.fmt.bufPrint(&buf, "{s}_{d}", .{ name.base, name.unique.value });
                try self.write(s);
            }
        }

        // ── Tags ───────────────────────────────────────────────────────

        pub fn printTag(self: *Self, tag: ir.Tag) anyerror!void {
            switch (tag.tag_type) {
                .Con => try self.writeByte('C'),
                .Fun => try self.writeByte('F'),
                .Partial => |n| {
                    var buf: [32]u8 = undefined;
                    const s = try std.fmt.bufPrint(&buf, "P({d})", .{n});
                    try self.write(s);
                },
            }
            try self.printName(tag.name);
        }

        // ── Literals ───────────────────────────────────────────────────

        pub fn printLiteral(self: *Self, lit: ir.Literal) anyerror!void {
            var buf: [128]u8 = undefined;
            const s = switch (lit) {
                .Int => |i| try std.fmt.bufPrint(&buf, "{d}", .{i}),
                .Float => |f| try std.fmt.bufPrint(&buf, "{d}", .{f}),
                .Bool => |b| if (b) "True" else "False",
                .Char => |c| try std.fmt.bufPrint(&buf, "'{u}'", .{c}),
                .String => |st| try std.fmt.bufPrint(&buf, "\"{s}\"", .{st}),
            };
            try self.write(s);
        }

        // ── Values ─────────────────────────────────────────────────────

        pub fn printVal(self: *Self, val: ir.Val) anyerror!void {
            switch (val) {
                .ConstTagNode => |node| {
                    try self.writeByte('(');
                    try self.printTag(node.tag);
                    for (node.fields) |field| {
                        try self.writeByte(' ');
                        try self.printSimpleVal(field);
                    }
                    try self.writeByte(')');
                },
                .VarTagNode => |node| {
                    try self.writeByte('(');
                    try self.printName(node.tag_var);
                    for (node.fields) |field| {
                        try self.writeByte(' ');
                        try self.printSimpleVal(field);
                    }
                    try self.writeByte(')');
                },
                .ValTag => |tag| try self.printTag(tag),
                .Unit => try self.write("()"),
                .Lit => |lit| {
                    try self.writeByte('#');
                    try self.printLiteral(lit);
                },
                .Var => |name| try self.printName(name),
            }
        }

        /// Print a value in a context where it might need parentheses
        /// (e.g. as a field within a node). Nodes get parens, simple
        /// values don't.
        fn printSimpleVal(self: *Self, val: ir.Val) anyerror!void {
            switch (val) {
                .ConstTagNode, .VarTagNode => try self.printVal(val),
                else => try self.printVal(val),
            }
        }

        // ── Case patterns ──────────────────────────────────────────────

        pub fn printCPat(self: *Self, pat: ir.CPat) anyerror!void {
            switch (pat) {
                .NodePat => |node| {
                    try self.writeByte('(');
                    try self.printTag(node.tag);
                    for (node.fields) |field| {
                        try self.writeByte(' ');
                        try self.printName(field);
                    }
                    try self.writeByte(')');
                },
                .LitPat => |lit| {
                    try self.writeByte('#');
                    try self.printLiteral(lit);
                },
                .TagPat => |tag| try self.printTag(tag),
                .DefaultPat => try self.writeByte('_'),
            }
        }

        // ── Expressions ────────────────────────────────────────────────

        pub fn printExpr(self: *Self, expr: ir.Expr) anyerror!void {
            switch (expr) {
                .Bind => |bind| try self.printBind(bind),
                .Case => |case| try self.printCase(case),
                .App => |app| {
                    try self.printName(app.name);
                    for (app.args) |arg| {
                        try self.writeByte(' ');
                        try self.printVal(arg);
                    }
                },
                .Return => |val| {
                    try self.write("pure ");
                    try self.printVal(val);
                },
                .Store => |val| {
                    try self.write("store ");
                    try self.printVal(val);
                },
                .Fetch => |fetch| {
                    try self.write("fetch ");
                    try self.printName(fetch.ptr);
                    if (fetch.index) |idx| {
                        var buf: [16]u8 = undefined;
                        const s = try std.fmt.bufPrint(&buf, "[{d}]", .{idx});
                        try self.write(s);
                    }
                },
                .Update => |upd| {
                    try self.write("update ");
                    try self.printName(upd.ptr);
                    try self.writeByte(' ');
                    try self.printVal(upd.val);
                },
                .Block => |inner| try self.printExpr(inner.*),
            }
        }

        fn printBind(self: *Self, bind: anytype) anyerror!void {
            try self.printExpr(bind.lhs.*);
            try self.write(" ;");
            try self.newline();
            try self.writeIndent();
            try self.write("\\");
            try self.printVal(bind.pat);
            try self.write(" ->");
            try self.newline();
            self.indent();
            try self.writeIndent();
            try self.printExpr(bind.rhs.*);
            self.dedent();
        }

        fn printCase(self: *Self, case: anytype) anyerror!void {
            try self.write("case ");
            try self.printVal(case.scrutinee);
            try self.write(" of");
            self.indent();
            for (case.alts) |alt| {
                try self.newline();
                try self.writeIndent();
                try self.printAlt(alt);
            }
            self.dedent();
        }

        fn printAlt(self: *Self, alt: ir.Alt) anyerror!void {
            try self.printCPat(alt.pat);
            try self.write(" ->");
            try self.newline();
            self.indent();
            try self.writeIndent();
            try self.printExpr(alt.body.*);
            self.dedent();
        }

        // ── Top-level definitions ──────────────────────────────────────

        pub fn printDef(self: *Self, def: ir.Def) anyerror!void {
            try self.printName(def.name);
            for (def.params) |param| {
                try self.writeByte(' ');
                try self.printName(param);
            }
            try self.write(" =");
            try self.newline();
            self.indent();
            try self.writeIndent();
            try self.printExpr(def.body.*);
            self.dedent();
        }

        // ── Program ────────────────────────────────────────────────────

        pub fn printProgram(self: *Self, program: ir.Program) anyerror!void {
            for (program.defs, 0..) |def, i| {
                if (i > 0) {
                    try self.newline();
                    try self.newline();
                }
                try self.printDef(def);
            }
            try self.newline();
        }
    };
}

/// Helper to instantiate a printer for a given writer.
pub fn grinPrinter(writer: anytype) GrinPrinter(@TypeOf(writer)) {
    return GrinPrinter(@TypeOf(writer)).init(writer);
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

/// A simple buffer-backed writer for tests, matching the pattern used
/// in `core/pretty.zig`.
const TestWriter = struct {
    buf: []u8,
    pos: usize = 0,

    pub const Error = error{NoSpaceLeft};

    pub fn writeAll(self: *@This(), bytes: []const u8) !void {
        if (self.pos + bytes.len > self.buf.len) return error.NoSpaceLeft;
        @memcpy(self.buf[self.pos .. self.pos + bytes.len], bytes);
        self.pos += bytes.len;
    }

    pub fn writeByte(self: *@This(), byte: u8) !void {
        if (self.pos >= self.buf.len) return error.NoSpaceLeft;
        self.buf[self.pos] = byte;
        self.pos += 1;
    }

    pub fn write(self: *@This(), bytes: []const u8) !usize {
        if (self.pos + bytes.len > self.buf.len) return error.NoSpaceLeft;
        @memcpy(self.buf[self.pos .. self.pos + bytes.len], bytes);
        self.pos += bytes.len;
        return bytes.len;
    }

    pub fn getWritten(self: *@This()) []const u8 {
        return self.buf[0..self.pos];
    }

    pub fn reset(self: *@This()) void {
        self.pos = 0;
    }
};

fn testName(base: []const u8, unique: u64) ir.Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn conTag(base: []const u8, unique: u64) ir.Tag {
    return .{ .tag_type = .{ .Con = {} }, .name = testName(base, unique) };
}

fn funTag(base: []const u8, unique: u64) ir.Tag {
    return .{ .tag_type = .{ .Fun = {} }, .name = testName(base, unique) };
}

/// Renders a GRIN value to a string for testing.
fn renderVal(val: ir.Val) ![]const u8 {
    const S = struct {
        var buf: [4096]u8 = undefined;
        var tw: TestWriter = .{ .buf = &buf };
    };
    S.tw.reset();
    var printer = grinPrinter(&S.tw);
    try printer.printVal(val);
    return S.tw.getWritten();
}

/// Renders a GRIN expression to a string for testing.
fn renderExpr(expr: ir.Expr) ![]const u8 {
    const S = struct {
        var buf: [8192]u8 = undefined;
        var tw: TestWriter = .{ .buf = &buf };
    };
    S.tw.reset();
    var printer = grinPrinter(&S.tw);
    try printer.printExpr(expr);
    return S.tw.getWritten();
}

/// Renders a GRIN definition to a string for testing.
fn renderDef(def: ir.Def) ![]const u8 {
    const S = struct {
        var buf: [8192]u8 = undefined;
        var tw: TestWriter = .{ .buf = &buf };
    };
    S.tw.reset();
    var printer = grinPrinter(&S.tw);
    try printer.printDef(def);
    return S.tw.getWritten();
}

/// Renders a GRIN program to a string for testing.
fn renderProgram(program: ir.Program) ![]const u8 {
    const S = struct {
        var buf: [16384]u8 = undefined;
        var tw: TestWriter = .{ .buf = &buf };
    };
    S.tw.reset();
    var printer = grinPrinter(&S.tw);
    try printer.printProgram(program);
    return S.tw.getWritten();
}

// ── Tag tests ──────────────────────────────────────────────────────────

test "pretty: constructor tag" {
    var buf: [64]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);
    try printer.printTag(conTag("Just", 1));
    try testing.expectEqualStrings("CJust_1", tw.getWritten());
}

test "pretty: function tag" {
    var buf: [64]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);
    try printer.printTag(funTag("map", 2));
    try testing.expectEqualStrings("Fmap_2", tw.getWritten());
}

test "pretty: partial application tag" {
    var buf: [64]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);
    try printer.printTag(.{ .tag_type = .{ .Partial = 2 }, .name = testName("map", 3) });
    try testing.expectEqualStrings("P(2)map_3", tw.getWritten());
}

// ── Literal tests ──────────────────────────────────────────────────────

test "pretty: literals" {
    var buf: [128]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);

    try printer.printLiteral(.{ .Int = 42 });
    try testing.expectEqualStrings("42", tw.getWritten());

    tw.reset();
    try printer.printLiteral(.{ .Bool = true });
    try testing.expectEqualStrings("True", tw.getWritten());

    tw.reset();
    try printer.printLiteral(.{ .Char = 'x' });
    try testing.expectEqualStrings("'x'", tw.getWritten());

    tw.reset();
    try printer.printLiteral(.{ .String = "hello" });
    try testing.expectEqualStrings("\"hello\"", tw.getWritten());
}

// ── Value tests ────────────────────────────────────────────────────────

test "pretty: Val.Unit" {
    const result = try renderVal(.{ .Unit = {} });
    try testing.expectEqualStrings("()", result);
}

test "pretty: Val.Lit" {
    const result = try renderVal(.{ .Lit = .{ .Int = 42 } });
    try testing.expectEqualStrings("#42", result);
}

test "pretty: Val.Var" {
    const result = try renderVal(.{ .Var = testName("x", 1) });
    try testing.expectEqualStrings("x_1", result);
}

test "pretty: Val.ValTag" {
    const result = try renderVal(.{ .ValTag = conTag("Nil", 0) });
    try testing.expectEqualStrings("CNil", result);
}

test "pretty: Val.ConstTagNode" {
    const result = try renderVal(.{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 42 } }},
    } });
    try testing.expectEqualStrings("(CJust_1 #42)", result);
}

test "pretty: Val.ConstTagNode with multiple fields" {
    const result = try renderVal(.{ .ConstTagNode = .{
        .tag = conTag("Cons", 1),
        .fields = &.{
            .{ .Var = testName("h", 2) },
            .{ .Var = testName("t", 3) },
        },
    } });
    try testing.expectEqualStrings("(CCons_1 h_2 t_3)", result);
}

test "pretty: Val.ConstTagNode nullary" {
    const result = try renderVal(.{ .ConstTagNode = .{
        .tag = conTag("Nothing", 1),
        .fields = &.{},
    } });
    try testing.expectEqualStrings("(CNothing_1)", result);
}

test "pretty: Val.VarTagNode" {
    const result = try renderVal(.{ .VarTagNode = .{
        .tag_var = testName("t", 5),
        .fields = &.{.{ .Var = testName("x", 1) }},
    } });
    try testing.expectEqualStrings("(t_5 x_1)", result);
}

// ── Case pattern tests ─────────────────────────────────────────────────

test "pretty: CPat.NodePat" {
    var buf: [128]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);
    try printer.printCPat(.{ .NodePat = .{
        .tag = conTag("Just", 1),
        .fields = &.{testName("x", 2)},
    } });
    try testing.expectEqualStrings("(CJust_1 x_2)", tw.getWritten());
}

test "pretty: CPat.LitPat" {
    var buf: [128]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);
    try printer.printCPat(.{ .LitPat = .{ .Int = 0 } });
    try testing.expectEqualStrings("#0", tw.getWritten());
}

test "pretty: CPat.TagPat" {
    var buf: [128]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);
    try printer.printCPat(.{ .TagPat = conTag("Nil", 1) });
    try testing.expectEqualStrings("CNil_1", tw.getWritten());
}

test "pretty: CPat.DefaultPat" {
    var buf: [128]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = grinPrinter(&tw);
    try printer.printCPat(.{ .DefaultPat = {} });
    try testing.expectEqualStrings("_", tw.getWritten());
}

// ── Expression tests ───────────────────────────────────────────────────

test "pretty: Expr.Return" {
    const result = try renderExpr(.{ .Return = .{ .Lit = .{ .Int = 42 } } });
    try testing.expectEqualStrings("pure #42", result);
}

test "pretty: Expr.Store" {
    const result = try renderExpr(.{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 5 } }},
    } } });
    try testing.expectEqualStrings("store (CJust_1 #5)", result);
}

test "pretty: Expr.Fetch without index" {
    const result = try renderExpr(.{ .Fetch = .{ .ptr = testName("p", 1), .index = null } });
    try testing.expectEqualStrings("fetch p_1", result);
}

test "pretty: Expr.Fetch with index" {
    const result = try renderExpr(.{ .Fetch = .{ .ptr = testName("p", 1), .index = 2 } });
    try testing.expectEqualStrings("fetch p_1[2]", result);
}

test "pretty: Expr.Update" {
    const result = try renderExpr(.{ .Update = .{
        .ptr = testName("p", 1),
        .val = .{ .ConstTagNode = .{
            .tag = conTag("Just", 2),
            .fields = &.{.{ .Lit = .{ .Int = 99 } }},
        } },
    } });
    try testing.expectEqualStrings("update p_1 (CJust_2 #99)", result);
}

test "pretty: Expr.App" {
    const result = try renderExpr(.{ .App = .{
        .name = testName("f", 2),
        .args = &.{.{ .Var = testName("x", 1) }},
    } });
    try testing.expectEqualStrings("f_2 x_1", result);
}

test "pretty: Expr.App with multiple args" {
    const result = try renderExpr(.{ .App = .{
        .name = testName("add", 1),
        .args = &.{
            .{ .Var = testName("x", 2) },
            .{ .Var = testName("y", 3) },
        },
    } });
    try testing.expectEqualStrings("add_1 x_2 y_3", result);
}

test "pretty: Expr.App with no args" {
    const result = try renderExpr(.{ .App = .{
        .name = testName("main", 1),
        .args = &.{},
    } });
    try testing.expectEqualStrings("main_1", result);
}

// ── Bind tests ─────────────────────────────────────────────────────────

test "pretty: Expr.Bind (store >>= fetch)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const lhs = try alloc.create(ir.Expr);
    lhs.* = .{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 42 } }},
    } } };

    const rhs = try alloc.create(ir.Expr);
    rhs.* = .{ .Fetch = .{ .ptr = testName("p", 2), .index = null } };

    const result = try renderExpr(.{ .Bind = .{
        .lhs = lhs,
        .pat = .{ .Var = testName("p", 2) },
        .rhs = rhs,
    } });

    try testing.expectEqualStrings(
        \\store (CJust_1 #42) ;
        \\\p_2 ->
        \\  fetch p_2
    , result);
}

// ── Case tests ─────────────────────────────────────────────────────────

test "pretty: Expr.Case" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body1 = try alloc.create(ir.Expr);
    body1.* = .{ .Return = .{ .Var = testName("x", 10) } };

    const body2 = try alloc.create(ir.Expr);
    body2.* = .{ .Return = .{ .Lit = .{ .Int = 0 } } };

    const alts = try alloc.alloc(ir.Alt, 2);
    alts[0] = .{
        .pat = .{ .NodePat = .{
            .tag = conTag("Just", 1),
            .fields = &.{testName("x", 10)},
        } },
        .body = body1,
    };
    alts[1] = .{
        .pat = .{ .DefaultPat = {} },
        .body = body2,
    };

    const result = try renderExpr(.{ .Case = .{
        .scrutinee = .{ .Var = testName("val", 4) },
        .alts = alts,
    } });

    try testing.expectEqualStrings(
        \\case val_4 of
        \\  (CJust_1 x_10) ->
        \\    pure x_10
        \\  _ ->
        \\    pure #0
    , result);
}

// ── Def tests ──────────────────────────────────────────────────────────

test "pretty: Def (identity function)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(ir.Expr);
    body.* = .{ .Return = .{ .Var = testName("x", 2) } };

    const params = try alloc.alloc(ir.Name, 1);
    params[0] = testName("x", 2);

    const result = try renderDef(.{
        .name = testName("id", 1),
        .params = params,
        .body = body,
    });

    try testing.expectEqualStrings(
        \\id_1 x_2 =
        \\  pure x_2
    , result);
}

test "pretty: Def with no params (main)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(ir.Expr);
    body.* = .{ .Return = .{ .Unit = {} } };

    const result = try renderDef(.{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    });

    try testing.expectEqualStrings(
        \\main_1 =
        \\  pure ()
    , result);
}

// ── Program tests ──────────────────────────────────────────────────────

test "pretty: Program with two defs" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const id_body = try alloc.create(ir.Expr);
    id_body.* = .{ .Return = .{ .Var = testName("x", 2) } };

    const main_body = try alloc.create(ir.Expr);
    main_body.* = .{ .App = .{
        .name = testName("id", 1),
        .args = &.{.{ .Lit = .{ .Int = 42 } }},
    } };

    const defs = try alloc.alloc(ir.Def, 2);
    defs[0] = .{
        .name = testName("id", 1),
        .params = &.{testName("x", 2)},
        .body = id_body,
    };
    defs[1] = .{
        .name = testName("main", 3),
        .params = &.{},
        .body = main_body,
    };

    const result = try renderProgram(.{ .defs = defs });

    try testing.expectEqualStrings(
        \\id_1 x_2 =
        \\  pure x_2
        \\
        \\main_3 =
        \\  id_1 #42
        \\
    , result);
}

// ── Nested expression test (eval pattern) ──────────────────────────────

test "pretty: nested store-bind-case (eval pattern)" {
    // Represents:
    //   store (CJust [42]) ;
    //   \p ->
    //     fetch p ;
    //     \val ->
    //       case val of
    //         (CJust x) ->
    //           pure x
    //         _ ->
    //           pure #0
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Inner: case val of ...
    const ret_x = try alloc.create(ir.Expr);
    ret_x.* = .{ .Return = .{ .Var = testName("x", 10) } };

    const ret_zero = try alloc.create(ir.Expr);
    ret_zero.* = .{ .Return = .{ .Lit = .{ .Int = 0 } } };

    const alts = try alloc.alloc(ir.Alt, 2);
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

    const case_expr = try alloc.create(ir.Expr);
    case_expr.* = .{ .Case = .{
        .scrutinee = .{ .Var = testName("val", 4) },
        .alts = alts,
    } };

    // Middle: fetch p >>= \val -> case ...
    const fetch_expr = try alloc.create(ir.Expr);
    fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 3), .index = null } };

    const inner_bind = try alloc.create(ir.Expr);
    inner_bind.* = .{ .Bind = .{
        .lhs = fetch_expr,
        .pat = .{ .Var = testName("val", 4) },
        .rhs = case_expr,
    } };

    // Outer: store (CJust [42]) >>= \p -> ...
    const store_expr = try alloc.create(ir.Expr);
    store_expr.* = .{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 42 } }},
    } } };

    const result = try renderExpr(.{ .Bind = .{
        .lhs = store_expr,
        .pat = .{ .Var = testName("p", 3) },
        .rhs = inner_bind,
    } });

    try testing.expectEqualStrings(
        \\store (CJust_1 #42) ;
        \\\p_3 ->
        \\  fetch p_3 ;
        \\  \val_4 ->
        \\    case val_4 of
        \\      (CJust_1 x_10) ->
        \\        pure x_10
        \\      _ ->
        \\        pure #0
    , result);
}

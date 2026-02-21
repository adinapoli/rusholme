//! Core IR Pretty-Printer.
//!
//! Renders Core IR (System F_C) into a readable string representation.
//! Designed to write directly to any `std.io.Writer` to avoid allocations,
//! making it fully compatible with the `Diagnostic` rendering pipeline.

const std = @import("std");
const ast = @import("ast.zig");

/// A pretty-printer for Core IR that writes directly to any `std.io.Writer`.
pub fn CorePrinter(comptime WriterType: type) type {
    return struct {
        writer: WriterType,
        indent_level: u32 = 0,

        const Self = @This();
        const INDENT_WIDTH = 2;

        pub fn init(writer: WriterType) Self {
            return .{ .writer = writer };
        }

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

        pub fn printName(self: *Self, name: ast.Name) anyerror!void {
            if (name.unique.value == 0) {
                // If unique is 0, it might be a built-in or unscoped name, just print the base
                try self.write(name.base);
            } else {
                var buf: [128]u8 = undefined;
                const s = try std.fmt.bufPrint(&buf, "{s}_{d}", .{ name.base, name.unique.value });
                try self.write(s);
            }
        }

        pub fn printId(self: *Self, id: ast.Id, with_type: bool) anyerror!void {
            if (with_type) {
                try self.write("(");
            }
            try self.printName(id.name);
            if (with_type) {
                try self.write(" :: ");
                try self.printType(id.ty);
                try self.write(")");
            }
        }

        pub fn printLiteral(self: *Self, lit: ast.Literal) anyerror!void {
            var buf: [128]u8 = undefined;
            const s = switch (lit) {
                .Int => |i| try std.fmt.bufPrint(&buf, "{d}", .{i}),
                .Float => |f| try std.fmt.bufPrint(&buf, "{d}", .{f}),
                .Char => |c| try std.fmt.bufPrint(&buf, "'{u}'", .{c}),
                .String => |st| try std.fmt.bufPrint(&buf, "\"{s}\"", .{st}),
            };
            try self.write(s);
        }

        fn needsParens(ty: ast.CoreType) bool {
            return switch (ty) {
                .FunTy, .ForAllTy => true,
                .TyCon => |tc| tc.args.len > 0,
                .TyVar => false,
            };
        }

        pub fn printType(self: *Self, ty: ast.CoreType) anyerror!void {
            switch (ty) {
                .TyVar => |n| try self.printName(n),
                .TyCon => |tc| {
                    try self.printName(tc.name);
                    for (tc.args) |arg| {
                        try self.writeByte(' ');
                        const parens = needsParens(arg);
                        if (parens) try self.writeByte('(');
                        try self.printType(arg);
                        if (parens) try self.writeByte(')');
                    }
                },
                .FunTy => |f| {
                    const arg_parens = needsParens(f.arg.*);
                    if (arg_parens) try self.writeByte('(');
                    try self.printType(f.arg.*);
                    if (arg_parens) try self.writeByte(')');

                    try self.write(" -> ");
                    try self.printType(f.res.*);
                },
                .ForAllTy => |fa| {
                    try self.write("forall ");
                    try self.printName(fa.binder);
                    try self.write(". ");
                    try self.printType(fa.body.*);
                },
            }
        }

        pub fn printExpr(self: *Self, expr: ast.Expr) anyerror!void {
            switch (expr) {
                .Var => |v| try self.printName(v.name),
                .Lit => |l| try self.printLiteral(l.val),
                .App => |a| {
                    try self.printExpr(a.fn_expr.*);
                    try self.writeByte(' ');
                    const param_parens = switch (a.arg.*) {
                        .Var, .Lit, .Type, .Coercion => false,
                        else => true,
                    };
                    if (param_parens) try self.writeByte('(');
                    try self.printExpr(a.arg.*);
                    if (param_parens) try self.writeByte(')');
                },
                .Lam => |l| {
                    try self.write("\\");
                    try self.printId(l.binder, true);
                    try self.write(" -> ");
                    try self.printExpr(l.body.*);
                },
                .Let => |l| {
                    try self.write("let ");
                    switch (l.bind) {
                        .NonRec => |nr| {
                            try self.printBindPair(nr);
                            try self.newline();
                            try self.writeIndent();
                        },
                        .Rec => |r| {
                            try self.write("rec {");
                            try self.newline();
                            self.indent();
                            for (r, 0..) |bp, i| {
                                if (i > 0) try self.newline();
                                try self.writeIndent();
                                try self.printBindPair(bp);
                                try self.write(";");
                            }
                            self.dedent();
                            try self.newline();
                            try self.writeIndent();
                            try self.write("}");
                            try self.newline();
                            try self.writeIndent();
                        },
                    }
                    try self.write("in ");
                    try self.printExpr(l.body.*);
                },
                .Case => |c| {
                    try self.write("case ");
                    try self.printExpr(c.scrutinee.*);
                    try self.write(" of ");
                    try self.printId(c.binder, true);
                    try self.write(" {");
                    self.indent();
                    for (c.alts) |alt| {
                        try self.newline();
                        try self.writeIndent();
                        try self.printAlt(alt);
                    }
                    self.dedent();
                    try self.newline();
                    try self.writeIndent();
                    try self.write("}");
                },
                .Type => |t| {
                    try self.write("@");
                    const parens = needsParens(t);
                    if (parens) try self.writeByte('(');
                    try self.printType(t);
                    if (parens) try self.writeByte(')');
                },
                .Coercion => {
                    try self.write("~co~");
                },
            }
        }

        pub fn printDataDecl(self: *Self, dd: ast.CoreDataDecl) anyerror!void {
            try self.write("data ");
            try self.printName(dd.name);
            for (dd.tyvars) |tv| {
                try self.writeByte(' ');
                try self.printName(tv);
            }
            if (dd.constructors.len > 0) {
                try self.write(" = ");
                for (dd.constructors, 0..) |con, i| {
                    if (i > 0) try self.write(" | ");
                    try self.printId(con, true);
                }
            }
        }

        pub fn printProgram(self: *Self, program: ast.CoreProgram) anyerror!void {
            for (program.data_decls, 0..) |dd, i| {
                if (i > 0) {
                    try self.newline();
                }
                try self.printDataDecl(dd);
                try self.newline();
            }

            if (program.data_decls.len > 0 and program.binds.len > 0) {
                try self.newline();
            }

            for (program.binds, 0..) |bind, i| {
                if (i > 0) {
                    try self.newline();
                    try self.newline();
                }
                switch (bind) {
                    .NonRec => |nr| try self.printBindPair(nr),
                    .Rec => |r| {
                        try self.write("rec {");
                        try self.newline();
                        self.indent();
                        for (r, 0..) |bp, j| {
                            if (j > 0) try self.newline();
                            try self.writeIndent();
                            try self.printBindPair(bp);
                            try self.write(";");
                        }
                        self.dedent();
                        try self.newline();
                        try self.writeIndent();
                        try self.write("}");
                    },
                }
            }
        }

        fn printBindPair(self: *Self, bp: ast.BindPair) anyerror!void {
            try self.printId(bp.binder, true);
            try self.write(" = ");
            try self.printExpr(bp.rhs.*);
        }

        fn printAlt(self: *Self, alt: ast.Alt) anyerror!void {
            switch (alt.con) {
                .DataAlt => |name| {
                    try self.printName(name);
                    for (alt.binders) |b| {
                        try self.writeByte(' ');
                        try self.printId(b, true);
                    }
                },
                .LitAlt => |lit| {
                    try self.printLiteral(lit);
                },
                .Default => {
                    try self.write("_");
                },
            }
            try self.write(" -> ");
            try self.printExpr(alt.body.*);
        }
    };
}

/// Helper to instantiate a printer for a given writer.
pub fn corePrinter(writer: anytype) CorePrinter(@TypeOf(writer)) {
    return CorePrinter(@TypeOf(writer)).init(writer);
}

// ── Tests ──────────────────────────────────────────────────────────────
const testing = std.testing;

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

    // Required by std.fmt.format which might duck-type write instead of writeAll
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

fn testSpan() ast.SourceSpan {
    return ast.SourceSpan.init(
        ast.SourcePos.init(1, 1, 1),
        ast.SourcePos.init(1, 1, 10),
    );
}

fn testName(base: []const u8, unique: u64) ast.Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn intType() ast.CoreType {
    return .{ .TyCon = .{ .name = testName("Int", 0), .args = &.{} } };
}

fn testId(base: []const u8, unique: u64) ast.Id {
    return .{
        .name = testName(base, unique),
        .ty = intType(),
        .span = testSpan(),
    };
}

test "pretty print Literal" {
    var buf: [1024]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };

    var printer = corePrinter(&tw);
    try printer.printLiteral(.{ .Int = 42 });
    try testing.expectEqualStrings("42", tw.getWritten());

    tw.reset();
    try printer.printLiteral(.{ .String = "hello" });
    try testing.expectEqualStrings("\"hello\"", tw.getWritten());
}

test "pretty print CoreType" {
    var buf: [1024]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };

    var printer = corePrinter(&tw);

    // TyVar
    try printer.printType(.{ .TyVar = testName("a", 1) });
    try testing.expectEqualStrings("a_1", tw.getWritten());

    // TyCon
    tw.reset();
    const maybe_int = ast.CoreType{ .TyCon = .{
        .name = testName("Maybe", 0),
        .args = &.{intType()},
    } };
    try printer.printType(maybe_int);
    try testing.expectEqualStrings("Maybe Int", tw.getWritten());

    // FunTy
    tw.reset();
    const a_var = ast.CoreType{ .TyVar = testName("a", 1) };
    const fun = ast.CoreType{ .FunTy = .{ .arg = &a_var, .res = &maybe_int } };
    try printer.printType(fun);
    try testing.expectEqualStrings("a_1 -> Maybe Int", tw.getWritten());

    // ForAllTy
    tw.reset();
    const fa = ast.CoreType{ .ForAllTy = .{ .binder = testName("a", 1), .body = &fun } };
    try printer.printType(fa);
    try testing.expectEqualStrings("forall a_1. a_1 -> Maybe Int", tw.getWritten());
}

test "pretty print Expr" {
    var buf: [1024]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = corePrinter(&tw);

    // Var
    try printer.printExpr(.{ .Var = testId("x", 1) });
    try testing.expectEqualStrings("x_1", tw.getWritten());

    // App
    tw.reset();
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const f = try alloc.create(ast.Expr);
    f.* = .{ .Var = testId("f", 2) };
    const x = try alloc.create(ast.Expr);
    x.* = .{ .Var = testId("x", 1) };

    try printer.printExpr(.{ .App = .{ .fn_expr = f, .arg = x, .span = testSpan() } });
    try testing.expectEqualStrings("f_2 x_1", tw.getWritten());

    // Lam
    tw.reset();
    try printer.printExpr(.{ .Lam = .{ .binder = testId("x", 1), .body = x, .span = testSpan() } });
    try testing.expectEqualStrings("\\(x_1 :: Int) -> x_1", tw.getWritten());

    // Let NonRec
    tw.reset();
    const bound = ast.Bind{ .NonRec = .{ .binder = testId("x", 1), .rhs = x } };
    try printer.printExpr(.{ .Let = .{ .bind = bound, .body = x, .span = testSpan() } });
    try testing.expectEqualStrings(
        \\let (x_1 :: Int) = x_1
        \\in x_1
    , tw.getWritten());
}

test "pretty print Case" {
    var buf: [1024]u8 = undefined;
    var tw = TestWriter{ .buf = &buf };
    var printer = corePrinter(&tw);

    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const scrut = try alloc.create(ast.Expr);
    scrut.* = .{ .Var = testId("x", 1) };

    const body = try alloc.create(ast.Expr);
    body.* = .{ .Lit = .{ .val = .{ .Int = 0 }, .span = testSpan() } };

    const alts = try alloc.alloc(ast.Alt, 2);
    alts[0] = .{
        .con = .{ .DataAlt = testName("Just", 0) },
        .binders = &.{testId("y", 2)},
        .body = body,
    };
    alts[1] = .{
        .con = .{ .Default = {} },
        .binders = &.{},
        .body = scrut,
    };

    try printer.printExpr(.{ .Case = .{
        .scrutinee = scrut,
        .binder = testId("wild", 99),
        .ty = intType(),
        .alts = alts,
        .span = testSpan(),
    } });

    try testing.expectEqualStrings(
        \\case x_1 of (wild_99 :: Int) {
        \\  Just (y_2 :: Int) -> 0
        \\  _ -> x_1
        \\}
    , tw.getWritten());
}

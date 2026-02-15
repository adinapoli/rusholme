//! Lexer token types for Haskell source code.
//!
//! This module defines the complete set of token types for lexing Haskell 2010,
//! including keywords, literals, identifiers, layout tokens, and special symbols.
//!
//! Every token is wrapped in a `LocatedToken` that carries a `SourceSpan` for
//! precise error reporting and source location tracking.
//!
//! Reference: GHC's compiler/GHC/Parser/Lexer.x

const std = @import("std");
const span_mod = @import("../diagnostics/span.zig");
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;

/// A token tagged with its source location.
pub const LocatedToken = struct {
    token: Token,
    span: SourceSpan,

    pub fn init(token: Token, span_val: SourceSpan) LocatedToken {
        return .{ .token = token, .span = span_val };
    }

    pub fn format(self: LocatedToken, comptime fmt: []const u8, opts: std.fmt.FormatOptions, writer: anytype) !void {
        try self.token.format(fmt, opts, writer);
        try writer.print(" @ {d}:{d}-{d}:{d}", .{
            self.span.start.line,
            self.span.start.column,
            self.span.end.line,
            self.span.end.column,
        });
    }
};

/// A Haskell token.
///
/// Covers all Haskell 2010 tokens: keywords, literals, identifiers,
/// layout tokens (both explicit and virtual/inserted), special symbols,
/// comments, pragmas, and EOF.
pub const Token = union(enum) {
    // ── Keywords ───────────────────────────────────────────────────────
    kw_module,
    kw_where,
    kw_import,
    kw_qualified,
    kw_as,
    kw_hiding,
    kw_let,
    kw_in,
    kw_case,
    kw_of,
    kw_if,
    kw_then,
    kw_else,
    kw_do,
    kw_data,
    kw_type,
    kw_newtype,
    kw_class,
    kw_instance,
    kw_deriving,
    kw_default,
    kw_foreign,
    kw_forall,
    kw_infixl,
    kw_infixr,
    kw_infix,

    // ── Literals ───────────────────────────────────────────────────────
    lit_integer: i64,
    lit_float: f64,
    lit_char: u21,
    lit_string: []const u8,

    // ── Identifiers ────────────────────────────────────────────────────
    /// Lowercase-starting identifier: foo, bar', x1
    varid: []const u8,
    /// Uppercase-starting identifier: Just, Data.Map
    conid: []const u8,
    /// Operator symbol: +, >>=, <$>
    varsym: []const u8,
    /// Constructor operator (starts with :): :, :+:
    consym: []const u8,

    // ── Layout tokens (explicit) ───────────────────────────────────────
    /// Explicit open brace: {
    open_brace,
    /// Explicit close brace: }
    close_brace,
    /// Explicit semicolon: ;
    semi,

    // ── Layout tokens (virtual / inserted by layout rule) ──────────────
    /// Virtual open brace (inserted by layout rule)
    v_open_brace,
    /// Virtual close brace (inserted by layout rule)
    v_close_brace,
    /// Virtual semicolon (inserted by layout rule)
    v_semi,

    // ── Special symbols ────────────────────────────────────────────────
    /// (
    open_paren,
    /// )
    close_paren,
    /// [
    open_bracket,
    /// ]
    close_bracket,
    /// ,
    comma,
    /// ..
    dotdot,
    /// ::
    dcolon,
    /// =
    equals,
    /// backslash (lambda)
    backslash,
    /// |
    pipe,
    /// ->
    arrow_right,
    /// <-
    arrow_left,
    /// @
    at,
    /// ~
    tilde,
    /// =>
    darrow,
    /// _
    underscore,
    /// - (distinguished from varsym for negation / layout)
    minus,

    // ── Other ──────────────────────────────────────────────────────────
    /// End of file
    eof,
    /// Line comment (-- ...)
    line_comment: []const u8,
    /// Block comment ({- ... -})
    block_comment: []const u8,
    /// Pragma ({-# ... #-})
    pragma: []const u8,

    // ── Classification helpers ─────────────────────────────────────────

    /// Returns true if this token is a keyword.
    pub fn isKeyword(self: Token) bool {
        return switch (self) {
            .kw_module,
            .kw_where,
            .kw_import,
            .kw_qualified,
            .kw_as,
            .kw_hiding,
            .kw_let,
            .kw_in,
            .kw_case,
            .kw_of,
            .kw_if,
            .kw_then,
            .kw_else,
            .kw_do,
            .kw_data,
            .kw_type,
            .kw_newtype,
            .kw_class,
            .kw_instance,
            .kw_deriving,
            .kw_default,
            .kw_foreign,
            .kw_forall,
            .kw_infixl,
            .kw_infixr,
            .kw_infix,
            => true,
            else => false,
        };
    }

    /// Returns true if this token is a literal value.
    pub fn isLiteral(self: Token) bool {
        return switch (self) {
            .lit_integer, .lit_float, .lit_char, .lit_string => true,
            else => false,
        };
    }

    /// Returns true if this token is a virtual layout token
    /// (inserted by the layout rule, not present in source).
    pub fn isLayoutVirtual(self: Token) bool {
        return switch (self) {
            .v_open_brace, .v_close_brace, .v_semi => true,
            else => false,
        };
    }

    /// Look up a keyword token from its string representation.
    /// Returns null if the string is not a keyword.
    pub fn keywordFromString(s: []const u8) ?Token {
        const map = std.StaticStringMap(Token).initComptime(.{
            .{ "module", .kw_module },
            .{ "where", .kw_where },
            .{ "import", .kw_import },
            .{ "qualified", .kw_qualified },
            .{ "as", .kw_as },
            .{ "hiding", .kw_hiding },
            .{ "let", .kw_let },
            .{ "in", .kw_in },
            .{ "case", .kw_case },
            .{ "of", .kw_of },
            .{ "if", .kw_if },
            .{ "then", .kw_then },
            .{ "else", .kw_else },
            .{ "do", .kw_do },
            .{ "data", .kw_data },
            .{ "type", .kw_type },
            .{ "newtype", .kw_newtype },
            .{ "class", .kw_class },
            .{ "instance", .kw_instance },
            .{ "deriving", .kw_deriving },
            .{ "default", .kw_default },
            .{ "foreign", .kw_foreign },
            .{ "forall", .kw_forall },
            .{ "infixl", .kw_infixl },
            .{ "infixr", .kw_infixr },
            .{ "infix", .kw_infix },
        });
        return map.get(s);
    }

    pub fn format(self: Token, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        switch (self) {
            // Keywords
            .kw_module => try writer.writeAll("module"),
            .kw_where => try writer.writeAll("where"),
            .kw_import => try writer.writeAll("import"),
            .kw_qualified => try writer.writeAll("qualified"),
            .kw_as => try writer.writeAll("as"),
            .kw_hiding => try writer.writeAll("hiding"),
            .kw_let => try writer.writeAll("let"),
            .kw_in => try writer.writeAll("in"),
            .kw_case => try writer.writeAll("case"),
            .kw_of => try writer.writeAll("of"),
            .kw_if => try writer.writeAll("if"),
            .kw_then => try writer.writeAll("then"),
            .kw_else => try writer.writeAll("else"),
            .kw_do => try writer.writeAll("do"),
            .kw_data => try writer.writeAll("data"),
            .kw_type => try writer.writeAll("type"),
            .kw_newtype => try writer.writeAll("newtype"),
            .kw_class => try writer.writeAll("class"),
            .kw_instance => try writer.writeAll("instance"),
            .kw_deriving => try writer.writeAll("deriving"),
            .kw_default => try writer.writeAll("default"),
            .kw_foreign => try writer.writeAll("foreign"),
            .kw_forall => try writer.writeAll("forall"),
            .kw_infixl => try writer.writeAll("infixl"),
            .kw_infixr => try writer.writeAll("infixr"),
            .kw_infix => try writer.writeAll("infix"),

            // Literals
            .lit_integer => |v| try writer.print("integer({d})", .{v}),
            .lit_float => |v| try writer.print("float({d})", .{v}),
            .lit_char => |v| try writer.print("char({u})", .{v}),
            .lit_string => |v| try writer.print("string(\"{s}\")", .{v}),

            // Identifiers
            .varid => |v| try writer.print("varid({s})", .{v}),
            .conid => |v| try writer.print("conid({s})", .{v}),
            .varsym => |v| try writer.print("varsym({s})", .{v}),
            .consym => |v| try writer.print("consym({s})", .{v}),

            // Layout tokens (explicit)
            .open_brace => try writer.writeAll("{"),
            .close_brace => try writer.writeAll("}"),
            .semi => try writer.writeAll(";"),

            // Layout tokens (virtual)
            .v_open_brace => try writer.writeAll("v{"),
            .v_close_brace => try writer.writeAll("v}"),
            .v_semi => try writer.writeAll("v;"),

            // Special symbols
            .open_paren => try writer.writeAll("("),
            .close_paren => try writer.writeAll(")"),
            .open_bracket => try writer.writeAll("["),
            .close_bracket => try writer.writeAll("]"),
            .comma => try writer.writeAll(","),
            .dotdot => try writer.writeAll(".."),
            .dcolon => try writer.writeAll("::"),
            .equals => try writer.writeAll("="),
            .backslash => try writer.writeAll("\\"),
            .pipe => try writer.writeAll("|"),
            .arrow_right => try writer.writeAll("->"),
            .arrow_left => try writer.writeAll("<-"),
            .at => try writer.writeAll("@"),
            .tilde => try writer.writeAll("~"),
            .darrow => try writer.writeAll("=>"),
            .underscore => try writer.writeAll("_"),
            .minus => try writer.writeAll("-"),

            // Other
            .eof => try writer.writeAll("<eof>"),
            .line_comment => |v| try writer.print("comment({s})", .{v}),
            .block_comment => |v| try writer.print("block_comment({s})", .{v}),
            .pragma => |v| try writer.print("pragma({s})", .{v}),
        }
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

test "Token keyword classification" {
    try std.testing.expect(Token.kw_module.isKeyword());
    try std.testing.expect(Token.kw_where.isKeyword());
    try std.testing.expect(Token.kw_let.isKeyword());
    try std.testing.expect(Token.kw_forall.isKeyword());
    try std.testing.expect(Token.kw_infix.isKeyword());

    // Non-keywords
    try std.testing.expect(!Token.eof.isKeyword());
    try std.testing.expect(!(Token{ .varid = "x" }).isKeyword());
    try std.testing.expect(!(Token{ .lit_integer = 42 }).isKeyword());
    try std.testing.expect(!Token.open_paren.isKeyword());
}

test "Token literal classification" {
    try std.testing.expect((Token{ .lit_integer = 42 }).isLiteral());
    try std.testing.expect((Token{ .lit_float = 3.14 }).isLiteral());
    try std.testing.expect((Token{ .lit_char = 'a' }).isLiteral());
    try std.testing.expect((Token{ .lit_string = "hello" }).isLiteral());

    // Non-literals
    try std.testing.expect(!Token.kw_module.isLiteral());
    try std.testing.expect(!(Token{ .varid = "x" }).isLiteral());
    try std.testing.expect(!Token.open_paren.isLiteral());
}

test "Token virtual layout classification" {
    // Virtual tokens
    try std.testing.expect(Token.v_open_brace.isLayoutVirtual());
    try std.testing.expect(Token.v_close_brace.isLayoutVirtual());
    try std.testing.expect(Token.v_semi.isLayoutVirtual());

    // Explicit layout tokens are NOT virtual
    try std.testing.expect(!Token.open_brace.isLayoutVirtual());
    try std.testing.expect(!Token.close_brace.isLayoutVirtual());
    try std.testing.expect(!Token.semi.isLayoutVirtual());

    // Other tokens
    try std.testing.expect(!Token.kw_where.isLayoutVirtual());
    try std.testing.expect(!Token.eof.isLayoutVirtual());
}

test "Token.keywordFromString" {
    // Valid keywords
    try std.testing.expectEqual(Token.kw_module, Token.keywordFromString("module").?);
    try std.testing.expectEqual(Token.kw_where, Token.keywordFromString("where").?);
    try std.testing.expectEqual(Token.kw_let, Token.keywordFromString("let").?);
    try std.testing.expectEqual(Token.kw_in, Token.keywordFromString("in").?);
    try std.testing.expectEqual(Token.kw_case, Token.keywordFromString("case").?);
    try std.testing.expectEqual(Token.kw_of, Token.keywordFromString("of").?);
    try std.testing.expectEqual(Token.kw_if, Token.keywordFromString("if").?);
    try std.testing.expectEqual(Token.kw_then, Token.keywordFromString("then").?);
    try std.testing.expectEqual(Token.kw_else, Token.keywordFromString("else").?);
    try std.testing.expectEqual(Token.kw_do, Token.keywordFromString("do").?);
    try std.testing.expectEqual(Token.kw_data, Token.keywordFromString("data").?);
    try std.testing.expectEqual(Token.kw_type, Token.keywordFromString("type").?);
    try std.testing.expectEqual(Token.kw_newtype, Token.keywordFromString("newtype").?);
    try std.testing.expectEqual(Token.kw_class, Token.keywordFromString("class").?);
    try std.testing.expectEqual(Token.kw_instance, Token.keywordFromString("instance").?);
    try std.testing.expectEqual(Token.kw_deriving, Token.keywordFromString("deriving").?);
    try std.testing.expectEqual(Token.kw_default, Token.keywordFromString("default").?);
    try std.testing.expectEqual(Token.kw_foreign, Token.keywordFromString("foreign").?);
    try std.testing.expectEqual(Token.kw_forall, Token.keywordFromString("forall").?);
    try std.testing.expectEqual(Token.kw_infixl, Token.keywordFromString("infixl").?);
    try std.testing.expectEqual(Token.kw_infixr, Token.keywordFromString("infixr").?);
    try std.testing.expectEqual(Token.kw_infix, Token.keywordFromString("infix").?);
    try std.testing.expectEqual(Token.kw_import, Token.keywordFromString("import").?);
    try std.testing.expectEqual(Token.kw_qualified, Token.keywordFromString("qualified").?);
    try std.testing.expectEqual(Token.kw_as, Token.keywordFromString("as").?);
    try std.testing.expectEqual(Token.kw_hiding, Token.keywordFromString("hiding").?);

    // Non-keywords return null
    try std.testing.expect(Token.keywordFromString("foo") == null);
    try std.testing.expect(Token.keywordFromString("bar") == null);
    try std.testing.expect(Token.keywordFromString("Module") == null);
    try std.testing.expect(Token.keywordFromString("") == null);
}

test "Token.format keywords" {
    var buf: [32]u8 = undefined;

    const s1 = try std.fmt.bufPrint(&buf, "{}", .{Token.kw_module});
    try std.testing.expectEqualStrings("module", s1);

    const s2 = try std.fmt.bufPrint(&buf, "{}", .{Token.kw_forall});
    try std.testing.expectEqualStrings("forall", s2);
}

test "Token.format literals" {
    var buf: [64]u8 = undefined;

    const s1 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .lit_integer = 42 }});
    try std.testing.expectEqualStrings("integer(42)", s1);

    const s2 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .lit_string = "hello" }});
    try std.testing.expectEqualStrings("string(\"hello\")", s2);
}

test "Token.format identifiers" {
    var buf: [64]u8 = undefined;

    const s1 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .varid = "foo" }});
    try std.testing.expectEqualStrings("varid(foo)", s1);

    const s2 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .conid = "Just" }});
    try std.testing.expectEqualStrings("conid(Just)", s2);

    const s3 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .varsym = ">>=" }});
    try std.testing.expectEqualStrings("varsym(>>=)", s3);

    const s4 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .consym = ":" }});
    try std.testing.expectEqualStrings("consym(:)", s4);
}

test "Token.format special symbols" {
    var buf: [16]u8 = undefined;

    const cases = .{
        .{ Token.open_paren, "(" },
        .{ Token.close_paren, ")" },
        .{ Token.open_bracket, "[" },
        .{ Token.close_bracket, "]" },
        .{ Token.comma, "," },
        .{ Token.dotdot, ".." },
        .{ Token.dcolon, "::" },
        .{ Token.equals, "=" },
        .{ Token.backslash, "\\" },
        .{ Token.pipe, "|" },
        .{ Token.arrow_right, "->" },
        .{ Token.arrow_left, "<-" },
        .{ Token.at, "@" },
        .{ Token.tilde, "~" },
        .{ Token.darrow, "=>" },
        .{ Token.underscore, "_" },
        .{ Token.minus, "-" },
    };

    inline for (cases) |c| {
        const s = try std.fmt.bufPrint(&buf, "{}", .{c[0]});
        try std.testing.expectEqualStrings(c[1], s);
    }
}

test "Token.format layout tokens" {
    var buf: [16]u8 = undefined;

    // Explicit
    const s1 = try std.fmt.bufPrint(&buf, "{}", .{Token.open_brace});
    try std.testing.expectEqualStrings("{", s1);
    const s2 = try std.fmt.bufPrint(&buf, "{}", .{Token.close_brace});
    try std.testing.expectEqualStrings("}", s2);
    const s3 = try std.fmt.bufPrint(&buf, "{}", .{Token.semi});
    try std.testing.expectEqualStrings(";", s3);

    // Virtual (prefixed with 'v')
    const s4 = try std.fmt.bufPrint(&buf, "{}", .{Token.v_open_brace});
    try std.testing.expectEqualStrings("v{", s4);
    const s5 = try std.fmt.bufPrint(&buf, "{}", .{Token.v_close_brace});
    try std.testing.expectEqualStrings("v}", s5);
    const s6 = try std.fmt.bufPrint(&buf, "{}", .{Token.v_semi});
    try std.testing.expectEqualStrings("v;", s6);
}

test "Token.format eof and comments" {
    var buf: [64]u8 = undefined;

    const s1 = try std.fmt.bufPrint(&buf, "{}", .{Token.eof});
    try std.testing.expectEqualStrings("<eof>", s1);

    const s2 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .line_comment = "a comment" }});
    try std.testing.expectEqualStrings("comment(a comment)", s2);

    const s3 = try std.fmt.bufPrint(&buf, "{}", .{Token{ .pragma = "LANGUAGE GADTs" }});
    try std.testing.expectEqualStrings("pragma(LANGUAGE GADTs)", s3);
}

test "LocatedToken construction and format" {
    var buf: [64]u8 = undefined;

    const span = SourceSpan.init(
        SourcePos.init(1, 5, 10),
        SourcePos.init(1, 5, 16),
    );
    const loc = LocatedToken.init(.kw_module, span);

    try std.testing.expectEqual(Token.kw_module, loc.token);
    try std.testing.expectEqual(@as(u32, 5), loc.span.start.line);
    try std.testing.expectEqual(@as(u32, 10), loc.span.start.column);

    const s = try std.fmt.bufPrint(&buf, "{}", .{loc});
    try std.testing.expectEqualStrings("module @ 5:10-5:16", s);
}

test "LocatedToken with identifier payload" {
    var buf: [64]u8 = undefined;

    const span = SourceSpan.init(
        SourcePos.init(1, 10, 1),
        SourcePos.init(1, 10, 4),
    );
    const loc = LocatedToken.init(.{ .varid = "foo" }, span);

    const s = try std.fmt.bufPrint(&buf, "{}", .{loc});
    try std.testing.expectEqualStrings("varid(foo) @ 10:1-10:4", s);
}

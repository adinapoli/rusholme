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

    pub fn format(self: LocatedToken, w: *std.Io.Writer) std.Io.Writer.Error!void {
        try self.token.format(w);
        try w.print(" @ {d}:{d}-{d}:{d}", .{
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

    pub fn format(self: Token, w: *std.Io.Writer) std.Io.Writer.Error!void {
        switch (self) {
            // Keywords
            .kw_module => try w.writeAll("module"),
            .kw_where => try w.writeAll("where"),
            .kw_import => try w.writeAll("import"),
            .kw_qualified => try w.writeAll("qualified"),
            .kw_as => try w.writeAll("as"),
            .kw_hiding => try w.writeAll("hiding"),
            .kw_let => try w.writeAll("let"),
            .kw_in => try w.writeAll("in"),
            .kw_case => try w.writeAll("case"),
            .kw_of => try w.writeAll("of"),
            .kw_if => try w.writeAll("if"),
            .kw_then => try w.writeAll("then"),
            .kw_else => try w.writeAll("else"),
            .kw_do => try w.writeAll("do"),
            .kw_data => try w.writeAll("data"),
            .kw_type => try w.writeAll("type"),
            .kw_newtype => try w.writeAll("newtype"),
            .kw_class => try w.writeAll("class"),
            .kw_instance => try w.writeAll("instance"),
            .kw_deriving => try w.writeAll("deriving"),
            .kw_default => try w.writeAll("default"),
            .kw_foreign => try w.writeAll("foreign"),
            .kw_forall => try w.writeAll("forall"),
            .kw_infixl => try w.writeAll("infixl"),
            .kw_infixr => try w.writeAll("infixr"),
            .kw_infix => try w.writeAll("infix"),

            // Literals
            .lit_integer => |v| try w.print("integer({d})", .{v}),
            .lit_float => |v| try w.print("float({d})", .{v}),
            .lit_char => |v| try w.print("char({u})", .{v}),
            .lit_string => |v| try w.print("string(\"{s}\")", .{v}),

            // Identifiers
            .varid => |v| try w.print("varid({s})", .{v}),
            .conid => |v| try w.print("conid({s})", .{v}),
            .varsym => |v| try w.print("varsym({s})", .{v}),
            .consym => |v| try w.print("consym({s})", .{v}),

            // Layout tokens (explicit)
            .open_brace => try w.writeAll("{"),
            .close_brace => try w.writeAll("}"),
            .semi => try w.writeAll(";"),

            // Layout tokens (virtual)
            .v_open_brace => try w.writeAll("v{"),
            .v_close_brace => try w.writeAll("v}"),
            .v_semi => try w.writeAll("v;"),

            // Special symbols
            .open_paren => try w.writeAll("("),
            .close_paren => try w.writeAll(")"),
            .open_bracket => try w.writeAll("["),
            .close_bracket => try w.writeAll("]"),
            .comma => try w.writeAll(","),
            .dotdot => try w.writeAll(".."),
            .dcolon => try w.writeAll("::"),
            .equals => try w.writeAll("="),
            .backslash => try w.writeAll("\\"),
            .pipe => try w.writeAll("|"),
            .arrow_right => try w.writeAll("->"),
            .arrow_left => try w.writeAll("<-"),
            .at => try w.writeAll("@"),
            .tilde => try w.writeAll("~"),
            .darrow => try w.writeAll("=>"),
            .underscore => try w.writeAll("_"),
            .minus => try w.writeAll("-"),

            // Other
            .eof => try w.writeAll("<eof>"),
            .line_comment => |v| try w.print("comment({s})", .{v}),
            .block_comment => |v| try w.print("block_comment({s})", .{v}),
            .pragma => |v| try w.print("pragma({s})", .{v}),
        }
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

test "Token keyword classification" {
    const kw_module: Token = .kw_module;
    const kw_where: Token = .kw_where;
    const kw_let: Token = .kw_let;
    const kw_forall: Token = .kw_forall;
    const kw_infix: Token = .kw_infix;
    try std.testing.expect(kw_module.isKeyword());
    try std.testing.expect(kw_where.isKeyword());
    try std.testing.expect(kw_let.isKeyword());
    try std.testing.expect(kw_forall.isKeyword());
    try std.testing.expect(kw_infix.isKeyword());

    // Non-keywords
    const eof_tok: Token = .eof;
    const open_paren_tok: Token = .open_paren;
    try std.testing.expect(!eof_tok.isKeyword());
    try std.testing.expect(!(Token{ .varid = "x" }).isKeyword());
    try std.testing.expect(!(Token{ .lit_integer = 42 }).isKeyword());
    try std.testing.expect(!open_paren_tok.isKeyword());
}

test "Token literal classification" {
    try std.testing.expect((Token{ .lit_integer = 42 }).isLiteral());
    try std.testing.expect((Token{ .lit_float = 3.14 }).isLiteral());
    try std.testing.expect((Token{ .lit_char = 'a' }).isLiteral());
    try std.testing.expect((Token{ .lit_string = "hello" }).isLiteral());

    // Non-literals
    const kw: Token = .kw_module;
    const paren: Token = .open_paren;
    try std.testing.expect(!kw.isLiteral());
    try std.testing.expect(!(Token{ .varid = "x" }).isLiteral());
    try std.testing.expect(!paren.isLiteral());
}

test "Token virtual layout classification" {
    // Virtual tokens
    const v_open: Token = .v_open_brace;
    const v_close: Token = .v_close_brace;
    const v_s: Token = .v_semi;
    try std.testing.expect(v_open.isLayoutVirtual());
    try std.testing.expect(v_close.isLayoutVirtual());
    try std.testing.expect(v_s.isLayoutVirtual());

    // Explicit layout tokens are NOT virtual
    const e_open: Token = .open_brace;
    const e_close: Token = .close_brace;
    const e_semi: Token = .semi;
    try std.testing.expect(!e_open.isLayoutVirtual());
    try std.testing.expect(!e_close.isLayoutVirtual());
    try std.testing.expect(!e_semi.isLayoutVirtual());

    // Other tokens
    const kw: Token = .kw_where;
    const eof_tok: Token = .eof;
    try std.testing.expect(!kw.isLayoutVirtual());
    try std.testing.expect(!eof_tok.isLayoutVirtual());
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

    const kw1: Token = .kw_module;
    const s1 = try std.fmt.bufPrint(&buf, "{f}", .{kw1});
    try std.testing.expectEqualStrings("module", s1);

    const kw2: Token = .kw_forall;
    const s2 = try std.fmt.bufPrint(&buf, "{f}", .{kw2});
    try std.testing.expectEqualStrings("forall", s2);
}

test "Token.format literals" {
    var buf: [64]u8 = undefined;

    const s1 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .lit_integer = 42 }});
    try std.testing.expectEqualStrings("integer(42)", s1);

    const s2 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .lit_string = "hello" }});
    try std.testing.expectEqualStrings("string(\"hello\")", s2);
}

test "Token.format identifiers" {
    var buf: [64]u8 = undefined;

    const s1 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .varid = "foo" }});
    try std.testing.expectEqualStrings("varid(foo)", s1);

    const s2 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .conid = "Just" }});
    try std.testing.expectEqualStrings("conid(Just)", s2);

    const s3 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .varsym = ">>=" }});
    try std.testing.expectEqualStrings("varsym(>>=)", s3);

    const s4 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .consym = ":" }});
    try std.testing.expectEqualStrings("consym(:)", s4);
}

test "Token.format special symbols" {
    var buf: [16]u8 = undefined;

    const open_paren: Token = .open_paren;
    const close_paren: Token = .close_paren;
    const open_bracket: Token = .open_bracket;
    const close_bracket: Token = .close_bracket;
    const comma_tok: Token = .comma;
    const dotdot_tok: Token = .dotdot;
    const dcolon_tok: Token = .dcolon;
    const equals_tok: Token = .equals;
    const backslash_tok: Token = .backslash;
    const pipe_tok: Token = .pipe;
    const arrow_r: Token = .arrow_right;
    const arrow_l: Token = .arrow_left;
    const at_tok: Token = .at;
    const tilde_tok: Token = .tilde;
    const darrow_tok: Token = .darrow;
    const underscore_tok: Token = .underscore;
    const minus_tok: Token = .minus;

    const cases = .{
        .{ open_paren, "(" },
        .{ close_paren, ")" },
        .{ open_bracket, "[" },
        .{ close_bracket, "]" },
        .{ comma_tok, "," },
        .{ dotdot_tok, ".." },
        .{ dcolon_tok, "::" },
        .{ equals_tok, "=" },
        .{ backslash_tok, "\\" },
        .{ pipe_tok, "|" },
        .{ arrow_r, "->" },
        .{ arrow_l, "<-" },
        .{ at_tok, "@" },
        .{ tilde_tok, "~" },
        .{ darrow_tok, "=>" },
        .{ underscore_tok, "_" },
        .{ minus_tok, "-" },
    };

    inline for (cases) |c| {
        const s = try std.fmt.bufPrint(&buf, "{f}", .{c[0]});
        try std.testing.expectEqualStrings(c[1], s);
    }
}

test "Token.format layout tokens" {
    var buf: [16]u8 = undefined;

    // Explicit
    const ob: Token = .open_brace;
    const s1 = try std.fmt.bufPrint(&buf, "{f}", .{ob});
    try std.testing.expectEqualStrings("{", s1);
    const cb: Token = .close_brace;
    const s2 = try std.fmt.bufPrint(&buf, "{f}", .{cb});
    try std.testing.expectEqualStrings("}", s2);
    const sm: Token = .semi;
    const s3 = try std.fmt.bufPrint(&buf, "{f}", .{sm});
    try std.testing.expectEqualStrings(";", s3);

    // Virtual (prefixed with 'v')
    const vob: Token = .v_open_brace;
    const s4 = try std.fmt.bufPrint(&buf, "{f}", .{vob});
    try std.testing.expectEqualStrings("v{", s4);
    const vcb: Token = .v_close_brace;
    const s5 = try std.fmt.bufPrint(&buf, "{f}", .{vcb});
    try std.testing.expectEqualStrings("v}", s5);
    const vs: Token = .v_semi;
    const s6 = try std.fmt.bufPrint(&buf, "{f}", .{vs});
    try std.testing.expectEqualStrings("v;", s6);
}

test "Token.format eof and comments" {
    var buf: [64]u8 = undefined;

    const eof_tok: Token = .eof;
    const s1 = try std.fmt.bufPrint(&buf, "{f}", .{eof_tok});
    try std.testing.expectEqualStrings("<eof>", s1);

    const s2 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .line_comment = "a comment" }});
    try std.testing.expectEqualStrings("comment(a comment)", s2);

    const s3 = try std.fmt.bufPrint(&buf, "{f}", .{Token{ .pragma = "LANGUAGE GADTs" }});
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

    const s = try std.fmt.bufPrint(&buf, "{f}", .{loc});
    try std.testing.expectEqualStrings("module @ 5:10-5:16", s);
}

test "LocatedToken with identifier payload" {
    var buf: [64]u8 = undefined;

    const span = SourceSpan.init(
        SourcePos.init(1, 10, 1),
        SourcePos.init(1, 10, 4),
    );
    const loc = LocatedToken.init(.{ .varid = "foo" }, span);

    const s = try std.fmt.bufPrint(&buf, "{f}", .{loc});
    try std.testing.expectEqualStrings("varid(foo) @ 10:1-10:4", s);
}

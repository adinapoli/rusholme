//! Recursive descent parser for Haskell source code.
//!
//! The Parser consumes a layout-processed token stream and builds an AST.
//! It supports lookahead, error recovery, and integrates with the
//! diagnostic infrastructure for structured error reporting.

const std = @import("std");
const lexer_mod = @import("lexer.zig");
const layout_mod = @import("layout.zig");
const ast_mod = @import("ast.zig");
const span_mod = @import("../diagnostics/span.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");

const Token = lexer_mod.Token;
const LocatedToken = lexer_mod.LocatedToken;
const LayoutProcessor = layout_mod.LayoutProcessor;
const Lexer = lexer_mod.Lexer;
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;
const Diagnostic = diag_mod.Diagnostic;
const DiagnosticCollector = diag_mod.DiagnosticCollector;

/// Tag type for comparing tokens without caring about payloads.
const TokenTag = std.meta.Tag(Token);

pub const ParseError = error{
    UnexpectedToken,
    UnexpectedEOF,
    InvalidSyntax,
} || std.mem.Allocator.Error;

/// Recursive descent parser for Haskell.
///
/// Wraps a `LayoutProcessor` (which wraps a `Lexer`), providing lookahead,
/// consumption helpers, and error recovery. Parse methods return AST nodes
/// or `ParseError`.
pub const Parser = struct {
    allocator: std.mem.Allocator,
    layout: *LayoutProcessor,
    diagnostics: *DiagnosticCollector,

    /// Lookahead buffer. Tokens are pulled from the layout processor
    /// on demand and buffered here for arbitrary lookahead.
    lookahead: std.ArrayListUnmanaged(LocatedToken) = .empty,

    /// Span of the last successfully consumed token.
    last_span: SourceSpan,

    pub fn init(
        allocator: std.mem.Allocator,
        layout: *LayoutProcessor,
        diagnostics: *DiagnosticCollector,
    ) Parser {
        return .{
            .allocator = allocator,
            .layout = layout,
            .diagnostics = diagnostics,
            .last_span = SourceSpan.init(
                SourcePos.init(1, 1, 1),
                SourcePos.init(1, 1, 1),
            ),
        };
    }

    pub fn deinit(self: *Parser) void {
        for (self.lookahead.items) |tok| {
            tok.token.deinit(self.allocator);
        }
        self.lookahead.deinit(self.allocator);
    }

    // ── Lookahead ──────────────────────────────────────────────────────

    /// Ensure at least `n` tokens are in the lookahead buffer.
    fn fillLookahead(self: *Parser, n: usize) !void {
        while (self.lookahead.items.len < n) {
            const tok = try self.layout.nextToken();
            try self.lookahead.append(self.allocator, tok);
        }
    }

    /// Peek at the current token without consuming it.
    pub fn peek(self: *Parser) !LocatedToken {
        try self.fillLookahead(1);
        return self.lookahead.items[0];
    }

    /// Peek at the token `offset` positions ahead (0 = current).
    pub fn peekAt(self: *Parser, offset: usize) !LocatedToken {
        try self.fillLookahead(offset + 1);
        return self.lookahead.items[offset];
    }

    /// Peek at the tag of the current token.
    pub fn peekTag(self: *Parser) !TokenTag {
        return std.meta.activeTag((try self.peek()).token);
    }

    /// Check if the current token matches the given tag.
    pub fn check(self: *Parser, tag: TokenTag) !bool {
        return (try self.peekTag()) == tag;
    }

    /// Check if the current token is EOF.
    pub fn atEnd(self: *Parser) !bool {
        return try self.check(.eof);
    }

    // ── Consumption ────────────────────────────────────────────────────

    /// Consume and return the current token unconditionally.
    pub fn advance(self: *Parser) !LocatedToken {
        try self.fillLookahead(1);
        const tok = self.lookahead.orderedRemove(0);
        self.last_span = tok.span;
        return tok;
    }

    /// Consume the current token if it matches `tag`. Returns the token
    /// on success, null on mismatch (does not consume or emit an error).
    pub fn match(self: *Parser, tag: TokenTag) !?LocatedToken {
        if (try self.check(tag)) {
            return try self.advance();
        }
        return null;
    }

    /// Consume the current token, asserting it matches `tag`.
    /// On mismatch, emits a diagnostic and returns `ParseError.UnexpectedToken`.
    pub fn expect(self: *Parser, tag: TokenTag) ParseError!LocatedToken {
        if (try self.check(tag)) {
            return try self.advance();
        }
        const got = try self.peek();
        var buf: [128]u8 = undefined;
        const msg = std.fmt.bufPrint(&buf, "expected {s}, got {s}", .{
            @tagName(tag),
            @tagName(std.meta.activeTag(got.token)),
        }) catch "unexpected token";
        try self.emitErrorMsg(got.span, msg);
        return error.UnexpectedToken;
    }

    /// Consume a virtual or explicit open brace.
    pub fn expectOpenBrace(self: *Parser) ParseError!LocatedToken {
        if (try self.check(.v_open_brace)) return try self.advance();
        if (try self.check(.open_brace)) return try self.advance();
        const got = try self.peek();
        try self.emitErrorMsg(got.span, "expected '{' or layout block");
        return error.UnexpectedToken;
    }

    /// Consume a virtual or explicit close brace.
    pub fn expectCloseBrace(self: *Parser) ParseError!LocatedToken {
        if (try self.check(.v_close_brace)) return try self.advance();
        if (try self.check(.close_brace)) return try self.advance();
        const got = try self.peek();
        try self.emitErrorMsg(got.span, "expected '}' or end of layout block");
        return error.UnexpectedToken;
    }

    /// Consume a virtual or explicit semicolon.
    pub fn expectSemi(self: *Parser) ParseError!LocatedToken {
        if (try self.check(.v_semi)) return try self.advance();
        if (try self.check(.semi)) return try self.advance();
        const got = try self.peek();
        try self.emitErrorMsg(got.span, "expected ';' or newline at same indentation");
        return error.UnexpectedToken;
    }

    /// Check if the current token is a semicolon (virtual or explicit).
    pub fn checkSemi(self: *Parser) !bool {
        const tag = try self.peekTag();
        return tag == .v_semi or tag == .semi;
    }

    /// Check if the current token is a close brace (virtual or explicit).
    pub fn checkCloseBrace(self: *Parser) !bool {
        const tag = try self.peekTag();
        return tag == .v_close_brace or tag == .close_brace;
    }

    /// Consume a semicolon if present. Returns true if consumed.
    pub fn matchSemi(self: *Parser) !bool {
        if (try self.checkSemi()) {
            _ = try self.advance();
            return true;
        }
        return false;
    }

    /// Consume a varid token and return its string payload.
    pub fn expectVarId(self: *Parser) ParseError!struct { name: []const u8, span: SourceSpan } {
        const tok = try self.expect(.varid);
        return .{ .name = tok.token.varid, .span = tok.span };
    }

    /// Consume a conid token and return its string payload.
    pub fn expectConId(self: *Parser) ParseError!struct { name: []const u8, span: SourceSpan } {
        const tok = try self.expect(.conid);
        return .{ .name = tok.token.conid, .span = tok.span };
    }

    // ── Combinators ────────────────────────────────────────────────────

    /// Parse zero or more items using `parseFn`, stopping when the
    /// current token doesn't match what `parseFn` expects (it must
    /// return null to signal "no match").
    pub fn many(
        self: *Parser,
        comptime T: type,
        parseFn: *const fn (*Parser) ParseError!?T,
    ) ParseError![]const T {
        var items: std.ArrayListUnmanaged(T) = .empty;
        while (true) {
            const item = try parseFn(self) orelse break;
            try items.append(self.allocator, item);
        }
        return items.toOwnedSlice(self.allocator);
    }

    /// Parse one or more items.
    pub fn many1(
        self: *Parser,
        comptime T: type,
        parseFn: *const fn (*Parser) ParseError!?T,
    ) ParseError![]const T {
        var items: std.ArrayListUnmanaged(T) = .empty;
        const first = try parseFn(self) orelse {
            const got = try self.peek();
            try self.emitErrorMsg(got.span, "expected at least one item");
            return error.UnexpectedToken;
        };
        try items.append(self.allocator, first);
        while (true) {
            const item = try parseFn(self) orelse break;
            try items.append(self.allocator, item);
        }
        return items.toOwnedSlice(self.allocator);
    }

    /// Parse items separated by a delimiter token tag.
    /// Returns an empty slice if no items match.
    pub fn sepBy(
        self: *Parser,
        comptime T: type,
        parseFn: *const fn (*Parser) ParseError!?T,
        sep: TokenTag,
    ) ParseError![]const T {
        var items: std.ArrayListUnmanaged(T) = .empty;
        const first = try parseFn(self) orelse return items.toOwnedSlice(self.allocator);
        try items.append(self.allocator, first);
        while (try self.match(sep) != null) {
            const item = try parseFn(self) orelse {
                const got = try self.peek();
                try self.emitErrorMsg(got.span, "expected item after separator");
                return error.UnexpectedToken;
            };
            try items.append(self.allocator, item);
        }
        return items.toOwnedSlice(self.allocator);
    }

    /// Parse items separated by a delimiter, requiring at least one.
    pub fn sepBy1(
        self: *Parser,
        comptime T: type,
        parseFn: *const fn (*Parser) ParseError!?T,
        sep: TokenTag,
    ) ParseError![]const T {
        var items: std.ArrayListUnmanaged(T) = .empty;
        const first = try parseFn(self) orelse {
            const got = try self.peek();
            try self.emitErrorMsg(got.span, "expected at least one item");
            return error.UnexpectedToken;
        };
        try items.append(self.allocator, first);
        while (try self.match(sep) != null) {
            const item = try parseFn(self) orelse {
                const got = try self.peek();
                try self.emitErrorMsg(got.span, "expected item after separator");
                return error.UnexpectedToken;
            };
            try items.append(self.allocator, item);
        }
        return items.toOwnedSlice(self.allocator);
    }

    /// Parse items separated by semicolons (virtual or explicit) within
    /// braces (virtual or explicit). This is the core combinator for
    /// layout-delimited blocks like `where { decl; decl; ... }`.
    pub fn layoutBlock(
        self: *Parser,
        comptime T: type,
        parseFn: *const fn (*Parser) ParseError!?T,
    ) ParseError![]const T {
        _ = try self.expectOpenBrace();
        var items: std.ArrayListUnmanaged(T) = .empty;

        while (true) {
            if (try self.checkCloseBrace()) break;
            if (try self.atEnd()) break;

            const item = try parseFn(self) orelse break;
            try items.append(self.allocator, item);

            // Consume trailing semicolons
            while (try self.matchSemi()) {}
        }

        _ = try self.expectCloseBrace();
        return items.toOwnedSlice(self.allocator);
    }

    // ── Error recovery ─────────────────────────────────────────────────

    /// Skip tokens until we reach a synchronization point: a semicolon,
    /// close brace, or EOF. Used for error recovery to skip past a
    /// malformed declaration and resume parsing the next one.
    pub fn synchronize(self: *Parser) !void {
        while (true) {
            const tag = try self.peekTag();
            switch (tag) {
                .semi, .v_semi, .close_brace, .v_close_brace, .eof => return,
                else => {
                    const tok = try self.advance();
                    tok.token.deinit(self.allocator);
                },
            }
        }
    }

    // ── Span helpers ───────────────────────────────────────────────────

    /// Create a span from `start` to the end of the last consumed token.
    pub fn spanFrom(self: *Parser, start: SourceSpan) SourceSpan {
        return start.merge(self.last_span);
    }

    /// Get the span of the current (not yet consumed) token.
    pub fn currentSpan(self: *Parser) !SourceSpan {
        return (try self.peek()).span;
    }

    // ── Diagnostics ────────────────────────────────────────────────────

    fn emitErrorMsg(self: *Parser, span_val: SourceSpan, message: []const u8) !void {
        const owned_msg = try self.allocator.dupe(u8, message);
        try self.diagnostics.emit(self.allocator, Diagnostic{
            .severity = .@"error",
            .code = .parse_error,
            .span = span_val,
            .message = owned_msg,
        });
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

fn testSpan() SourceSpan {
    return SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 1));
}

/// Helper to create a Parser from source text for testing.
fn initTestParser(
    allocator: std.mem.Allocator,
    source: []const u8,
    lexer: *Lexer,
    layout: *LayoutProcessor,
    diags: *DiagnosticCollector,
) Parser {
    lexer.* = Lexer.init(allocator, source, 1);
    layout.* = LayoutProcessor.init(allocator, lexer);
    diags.* = DiagnosticCollector.init();
    return Parser.init(allocator, layout, diags);
}

test "Parser.peek returns current token without consuming" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const tok1 = try parser.peek();
    const tok2 = try parser.peek();
    // Peeking twice should return the same token
    try std.testing.expectEqual(
        std.meta.activeTag(tok1.token),
        std.meta.activeTag(tok2.token),
    );
}

test "Parser.advance consumes tokens in order" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const tok1 = try parser.advance();
    try std.testing.expectEqual(TokenTag.kw_module, std.meta.activeTag(tok1.token));

    const tok2 = try parser.advance();
    try std.testing.expectEqual(TokenTag.conid, std.meta.activeTag(tok2.token));
    tok2.token.deinit(allocator);

    const tok3 = try parser.advance();
    try std.testing.expectEqual(TokenTag.kw_where, std.meta.activeTag(tok3.token));
}

test "Parser.check returns true for matching tag" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    try std.testing.expect(try parser.check(.kw_module));
    try std.testing.expect(!try parser.check(.kw_where));
}

test "Parser.expect succeeds on correct token" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const tok = try parser.expect(.kw_module);
    try std.testing.expectEqual(TokenTag.kw_module, std.meta.activeTag(tok.token));
}

test "Parser.expect fails on wrong token and emits diagnostic" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer {
        // Free diagnostic messages
        for (diags.diagnostics.items) |d| {
            allocator.free(d.message);
        }
        diags.deinit(allocator);
    }

    const result = parser.expect(.kw_where);
    try std.testing.expectError(error.UnexpectedToken, result);
    try std.testing.expect(diags.hasErrors());
}

test "Parser.match returns null on mismatch without error" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const result = try parser.match(.kw_where);
    try std.testing.expect(result == null);
    try std.testing.expect(!diags.hasErrors());
    // Token was not consumed
    try std.testing.expect(try parser.check(.kw_module));
}

test "Parser.peekAt provides lookahead" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const tok0 = try parser.peekAt(0);
    const tok1 = try parser.peekAt(1);
    try std.testing.expectEqual(TokenTag.kw_module, std.meta.activeTag(tok0.token));
    try std.testing.expectEqual(TokenTag.conid, std.meta.activeTag(tok1.token));
}

test "Parser.synchronize skips to next declaration boundary" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    // "foo bar baz" gets wrapped in virtual braces by layout processor.
    // After consuming the v_open_brace, synchronize should skip tokens
    // until it hits the v_close_brace.
    var parser = initTestParser(allocator, "foo bar baz", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    _ = try parser.expectOpenBrace(); // consume virtual {
    try parser.synchronize(); // skips foo, bar, baz — stops at virtual }
    try std.testing.expect(try parser.checkCloseBrace());
}

test "Parser.spanFrom creates merged span" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "module Main where", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const start = (try parser.peek()).span;
    _ = try parser.advance(); // module
    const tok = try parser.advance(); // Main
    tok.token.deinit(allocator);
    const span = parser.spanFrom(start);
    // Span should cover from "module" to "Main"
    try std.testing.expectEqual(@as(u32, 1), span.start.column);
    try std.testing.expect(span.end.column > span.start.column);
}

test "Parser.layoutBlock parses semicolon-separated items" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    // "x\ny\nz" — the layout processor will insert virtual braces and semis
    var parser = initTestParser(allocator, "x\ny\nz", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const parseVarId = struct {
        fn f(p: *Parser) ParseError!?[]const u8 {
            const tok = try p.match(.varid) orelse return null;
            return tok.token.varid;
        }
    }.f;

    const items = try parser.layoutBlock([]const u8, parseVarId);
    defer allocator.free(items);

    try std.testing.expectEqual(@as(usize, 3), items.len);
    try std.testing.expectEqualStrings("x", items[0]);
    try std.testing.expectEqualStrings("y", items[1]);
    try std.testing.expectEqualStrings("z", items[2]);
}

test "Parser.expectOpenBrace accepts virtual braces" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    // Simple input that triggers a virtual open brace at the start
    var parser = initTestParser(allocator, "x", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const tok = try parser.expectOpenBrace();
    try std.testing.expectEqual(TokenTag.v_open_brace, std.meta.activeTag(tok.token));
}

test "Parser.checkSemi detects virtual semicolons" {
    const allocator = std.testing.allocator;
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, "x\ny", &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    _ = try parser.expectOpenBrace(); // virtual {
    _ = try parser.advance(); // x
    // Next should be a virtual semicolon
    try std.testing.expect(try parser.checkSemi());
}

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

    /// Fixity environment for operator precedence parsing.
    /// Maps operator names to their precedence and associativity.
    /// Keys are owned (heap-duped) strings freed on deinit.
    fixity_env: std.StringHashMap(ast_mod.FixityInfo),

    /// Default fixity for operators without a declaration (Haskell 2010 §4.4.2).
    const default_fixity = ast_mod.FixityInfo{ .precedence = 9, .fixity = .InfixL };

    pub fn init(
        allocator: std.mem.Allocator,
        layout: *LayoutProcessor,
        diagnostics: *DiagnosticCollector,
    ) ParseError!Parser {
        var parser = Parser{
            .allocator = allocator,
            .layout = layout,
            .diagnostics = diagnostics,
            .last_span = SourceSpan.init(
                SourcePos.init(1, 1, 1),
                SourcePos.init(1, 1, 1),
            ),
            .fixity_env = std.StringHashMap(ast_mod.FixityInfo).init(allocator),
        };

        try parser.initBuiltInFixities();

        return parser;
    }

    pub fn deinit(self: *Parser) void {
        var it = self.fixity_env.keyIterator();
        while (it.next()) |key| {
            self.allocator.free(key.*);
        }
        self.fixity_env.deinit();

        for (self.lookahead.items) |tok| {
            tok.token.deinit(self.allocator);
        }
        self.lookahead.deinit(self.allocator);
    }

    // ── Fixity environment ─────────────────────────────────────────────

    /// Haskell 2010 Prelude fixity declarations (Report §9, PreludeList).
    fn initBuiltInFixities(self: *Parser) ParseError!void {
        // infixr 9  .
        try self.registerFixity(".", .InfixR, 9);
        // infixl 9  !!
        try self.registerFixity("!!", .InfixL, 9);
        // infixr 8  ^, ^^, **
        try self.registerFixity("^", .InfixR, 8);
        try self.registerFixity("^^", .InfixR, 8);
        try self.registerFixity("**", .InfixR, 8);
        // infixl 7  *, /
        try self.registerFixity("*", .InfixL, 7);
        try self.registerFixity("/", .InfixL, 7);
        // infixl 6  +, -
        try self.registerFixity("+", .InfixL, 6);
        try self.registerFixity("-", .InfixL, 6);
        // infixr 5  :, ++
        try self.registerFixity(":", .InfixR, 5);
        try self.registerFixity("++", .InfixR, 5);
        // infix  4  ==, /=, <, <=, >=, >
        try self.registerFixity("==", .InfixN, 4);
        try self.registerFixity("/=", .InfixN, 4);
        try self.registerFixity("<", .InfixN, 4);
        try self.registerFixity("<=", .InfixN, 4);
        try self.registerFixity(">", .InfixN, 4);
        try self.registerFixity(">=", .InfixN, 4);
        // infixr 3  &&
        try self.registerFixity("&&", .InfixR, 3);
        // infixr 2  ||
        try self.registerFixity("||", .InfixR, 2);
        // infixl 1  >>, >>=
        try self.registerFixity(">>", .InfixL, 1);
        try self.registerFixity(">>=", .InfixL, 1);
        // infixr 1  =<<
        try self.registerFixity("=<<", .InfixR, 1);
        // infixr 0  $, $!
        try self.registerFixity("$", .InfixR, 0);
        try self.registerFixity("$!", .InfixR, 0);
    }

    /// Register an operator's fixity in the environment.
    /// If the operator already exists, the old entry is replaced and its
    /// heap-duped key is freed.
    fn registerFixity(self: *Parser, op: []const u8, fixity: ast_mod.Fixity, precedence: u8) ParseError!void {
        const info = ast_mod.FixityInfo{ .precedence = precedence, .fixity = fixity };

        // If the key already exists, free the old key and reuse the slot.
        if (self.fixity_env.getEntry(op)) |entry| {
            entry.value_ptr.* = info;
            return;
        }

        const key = try self.allocator.dupe(u8, op);
        errdefer self.allocator.free(key);
        try self.fixity_env.put(key, info);
    }

    /// Look up fixity for an operator. Returns null if not registered.
    fn getFixity(self: *Parser, op: []const u8) ?ast_mod.FixityInfo {
        return self.fixity_env.get(op);
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

    // ── Module parsing ─────────────────────────────────────────────────

    /// Parse a complete Haskell module.
    ///
    /// ```
    /// module  ->  module modid [exports] where body
    ///         |   body
    /// body    ->  { topdecls }
    /// ```
    pub fn parseModule(self: *Parser) ParseError!ast_mod.Module {
        const start = try self.currentSpan();

        var module_name: []const u8 = "Main";
        var exports: ?[]const ast_mod.ExportSpec = null;

        if (try self.check(.kw_module)) {
            _ = try self.advance(); // consume 'module'
            const name_tok = try self.expect(.conid);
            module_name = name_tok.token.conid;
            if (try self.check(.open_paren)) {
                exports = try self.parseExportList();
            }
            _ = try self.expect(.kw_where);
        }

        // Parse body: { impdecls ; topdecls }
        _ = try self.expectOpenBrace();

        var imports: std.ArrayListUnmanaged(ast_mod.ImportDecl) = .empty;
        var decls: std.ArrayListUnmanaged(ast_mod.Decl) = .empty;

        // Parse imports (they come first)
        while (try self.check(.kw_import)) {
            const imp = try self.parseImportDecl();
            try imports.append(self.allocator, imp);
            while (try self.matchSemi()) {}
        }

        // Parse top-level declarations
        while (true) {
            if (try self.checkCloseBrace()) break;
            if (try self.atEnd()) break;

            const decl = self.parseTopDecl() catch |err| switch (err) {
                error.UnexpectedToken, error.InvalidSyntax => {
                    try self.synchronize();
                    while (try self.matchSemi()) {}
                    continue;
                },
                else => return err,
            };
            if (decl) |d| {
                try decls.append(self.allocator, d);
            }
            while (try self.matchSemi()) {}
        }

        _ = try self.expectCloseBrace();

        return ast_mod.Module{
            .module_name = module_name,
            .exports = exports,
            .imports = try imports.toOwnedSlice(self.allocator),
            .declarations = try decls.toOwnedSlice(self.allocator),
            .span = self.spanFrom(start),
        };
    }

    // ── Export list ────────────────────────────────────────────────────

    fn parseExportList(self: *Parser) ParseError![]const ast_mod.ExportSpec {
        _ = try self.expect(.open_paren);
        var specs: std.ArrayListUnmanaged(ast_mod.ExportSpec) = .empty;

        while (true) {
            if (try self.check(.close_paren)) break;

            const spec = try self.parseExportSpec();
            try specs.append(self.allocator, spec);

            if (try self.match(.comma) == null) break;
        }

        _ = try self.expect(.close_paren);
        return specs.toOwnedSlice(self.allocator);
    }

    fn parseExportSpec(self: *Parser) ParseError!ast_mod.ExportSpec {
        // module ModName
        if (try self.check(.kw_module)) {
            _ = try self.advance();
            const name_tok = try self.expect(.conid);
            return .{ .Module = name_tok.token.conid };
        }
        // ConId (..)  or  ConId
        if (try self.check(.conid)) {
            const tok = try self.advance();
            if (try self.check(.open_paren)) {
                _ = try self.advance();
                _ = try self.expect(.dotdot);
                _ = try self.expect(.close_paren);
                return .{ .Type = .{ .name = tok.token.conid, .with_constructors = true } };
            }
            return .{ .Con = tok.token.conid };
        }
        // varid
        if (try self.check(.varid)) {
            const tok = try self.advance();
            return .{ .Var = tok.token.varid };
        }
        // ( varsym ) — operator export
        if (try self.check(.open_paren)) {
            _ = try self.advance();
            const op_tok = try self.expect(.varsym);
            _ = try self.expect(.close_paren);
            return .{ .Var = op_tok.token.varsym };
        }
        const got = try self.peek();
        try self.emitErrorMsg(got.span, "expected export specification");
        return error.UnexpectedToken;
    }

    // ── Import declarations ────────────────────────────────────────────

    fn parseImportDecl(self: *Parser) ParseError!ast_mod.ImportDecl {
        const start = (try self.expect(.kw_import)).span;
        const qualified = (try self.match(.kw_qualified)) != null;
        const name_tok = try self.expect(.conid);

        var as_alias: ?[]const u8 = null;
        if (try self.match(.kw_as) != null) {
            const alias_tok = try self.expect(.conid);
            as_alias = alias_tok.token.conid;
        }

        var specs: ?ast_mod.ImportSpecs = null;
        const is_hiding = (try self.match(.kw_hiding)) != null;
        if (is_hiding or try self.check(.open_paren)) {
            specs = try self.parseImportSpecs(is_hiding);
        }

        return ast_mod.ImportDecl{
            .module_name = name_tok.token.conid,
            .qualified = qualified,
            .as_alias = as_alias,
            .specs = specs,
            .span = self.spanFrom(start),
        };
    }

    fn parseImportSpecs(self: *Parser, hiding: bool) ParseError!ast_mod.ImportSpecs {
        _ = try self.expect(.open_paren);
        var items: std.ArrayListUnmanaged(ast_mod.ImportSpec) = .empty;

        while (true) {
            if (try self.check(.close_paren)) break;

            const tag = try self.peekTag();
            if (tag == .varid) {
                const tok = try self.advance();
                try items.append(self.allocator, .{ .Var = tok.token.varid });
            } else if (tag == .conid) {
                const tok = try self.advance();
                try items.append(self.allocator, .{ .TyCon = tok.token.conid });
            } else if (tag == .open_paren) {
                // ( varsym ) — operator import
                _ = try self.advance();
                const op = try self.expect(.varsym);
                _ = try self.expect(.close_paren);
                try items.append(self.allocator, .{ .Var = op.token.varsym });
            } else {
                break;
            }

            if (try self.match(.comma) == null) break;
        }

        _ = try self.expect(.close_paren);
        return ast_mod.ImportSpecs{
            .hiding = hiding,
            .items = try items.toOwnedSlice(self.allocator),
        };
    }

    // ── Top-level declarations ─────────────────────────────────────────

    fn parseTopDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const tag = try self.peekTag();
        return switch (tag) {
            .kw_data => try self.parseDataDecl(),
            .kw_newtype => try self.parseNewtypeDecl(),
            .kw_type => try self.parseTypeAliasDecl(),
            .kw_class => try self.parseClassDecl(),
            .kw_instance => try self.parseInstanceDecl(),
            .kw_default => try self.parseDefaultDecl(),
            .kw_infixl, .kw_infixr, .kw_infix => try self.parseFixityDecl(),
            .varid => try self.parseValueDecl(),
            .open_paren => try self.parseValueDecl(),
            .eof, .v_close_brace, .close_brace => null,
            else => {
                const got = try self.peek();
                try self.emitErrorMsg(got.span, "expected declaration");
                return error.UnexpectedToken;
            },
        };
    }

    // ── Value declarations (type sigs and bindings) ────────────────────

    /// Parse a value-level declaration. This handles both type signatures
    /// and function/pattern bindings by lookahead:
    ///   - `name :: type`  → TypeSig
    ///   - `name pats = expr` → FunBind
    ///   - `( op ) :: type` → TypeSig for operator
    fn parseValueDecl(self: *Parser) ParseError!?ast_mod.Decl {
        // Check for operator type sig: ( op ) :: ...
        if (try self.check(.open_paren)) {
            const tok1 = try self.peekAt(1);
            if (std.meta.activeTag(tok1.token) == .varsym) {
                const tok2 = try self.peekAt(2);
                if (std.meta.activeTag(tok2.token) == .close_paren) {
                    _ = try self.advance(); // (
                    const op = try self.advance(); // operator
                    _ = try self.advance(); // )
                    _ = try self.expect(.dcolon);
                    const ty = try self.parseType();
                    return .{ .TypeSig = .{
                        .names = try self.allocSlice([]const u8, &.{op.token.varsym}),
                        .type = ty,
                        .span = self.spanFrom(op.span),
                    } };
                }
            }
        }

        const start = try self.currentSpan();
        const name_tok = try self.expect(.varid);
        const name = name_tok.token.varid;

        // Type signature: name :: type
        if (try self.check(.dcolon) or (try self.check(.consym) and std.mem.eql(u8, (try self.peek()).token.consym, "::"))) {
            _ = try self.advance(); // consume ::
            const ty = try self.parseType();
            return .{ .TypeSig = .{
                .names = try self.allocSlice([]const u8, &.{name}),
                .type = ty,
                .span = self.spanFrom(start),
            } };
        }

        // Infix function definition: pat1 `name` pat2 = rhs
        // (Haskell 2010 §4.4.3: funlhs → pat varop pat)
        // Detected by: varid already consumed, next token is backtick.
        if (try self.check(.backtick)) {
            // The already-consumed varid is the left-hand argument pattern.
            const lhs_pat = ast_mod.Pattern{ .Var = .{ .name = name, .span = name_tok.span } };

            _ = try self.advance(); // consume opening backtick

            // Parse the function name (varid or conid in backticks)
            const fn_name_tok = try self.peek();
            const fn_name: []const u8 = switch (std.meta.activeTag(fn_name_tok.token)) {
                .varid => blk: {
                    _ = try self.advance();
                    break :blk fn_name_tok.token.varid;
                },
                .conid => blk: {
                    _ = try self.advance();
                    break :blk fn_name_tok.token.conid;
                },
                else => {
                    try self.emitErrorMsg(fn_name_tok.span, "expected function name in backtick infix definition");
                    return error.UnexpectedToken;
                },
            };

            _ = try self.expect(.backtick); // consume closing backtick

            // Parse the right-hand argument pattern.
            const rhs_pat = try self.parseArgPattern();

            const rhs = try self.parseRhs();
            const where_clause = try self.parseWhereClause();

            const eq = ast_mod.Match{
                .patterns = try self.allocSlice(ast_mod.Pattern, &.{ lhs_pat, rhs_pat }),
                .rhs = rhs,
                .where_clause = where_clause,
                .span = self.spanFrom(start),
            };

            return .{ .FunBind = .{
                .name = fn_name,
                .equations = try self.allocSlice(ast_mod.Match, &.{eq}),
                .span = self.spanFrom(start),
            } };
        }

        // Function binding: name [patterns] = expr [where ...]
        // or guarded: name [patterns] | guard = expr
        // Each argument is an apat (Haskell 2010 §3.17.2): an atomic pattern
        // optionally followed by @apat (as-pattern).
        var patterns: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
        while (true) {
            const pat = try self.tryParseArgPattern() orelse break;
            try patterns.append(self.allocator, pat);
        }

        const rhs = try self.parseRhs();
        const where_clause = try self.parseWhereClause();

        const eq = ast_mod.Match{
            .patterns = try patterns.toOwnedSlice(self.allocator),
            .rhs = rhs,
            .where_clause = where_clause,
            .span = self.spanFrom(start),
        };

        return .{ .FunBind = .{
            .name = name,
            .equations = try self.allocSlice(ast_mod.Match, &.{eq}),
            .span = self.spanFrom(start),
        } };
    }

    fn parseRhs(self: *Parser) ParseError!ast_mod.Rhs {
        if (try self.check(.pipe)) {
            return try self.parseGuardedRhs();
        }
        _ = try self.expect(.equals);
        const expr = try self.parseExpr();
        return .{ .UnGuarded = expr };
    }

    fn parseGuardedRhs(self: *Parser) ParseError!ast_mod.Rhs {
        var guards: std.ArrayListUnmanaged(ast_mod.GuardedRhs) = .empty;
        while (try self.check(.pipe)) {
            _ = try self.advance(); // consume |
            const guard_expr = try self.parseExpr();
            _ = try self.expect(.equals);
            const rhs_expr = try self.parseExpr();
            try guards.append(self.allocator, .{
                .guards = try self.allocSlice(ast_mod.Guard, &.{.{ .ExprGuard = guard_expr }}),
                .rhs = rhs_expr,
            });
        }
        return .{ .Guarded = try guards.toOwnedSlice(self.allocator) };
    }

    fn parseWhereClause(self: *Parser) ParseError!?[]const ast_mod.Decl {
        if (try self.match(.kw_where) == null) return null;

        _ = try self.expectOpenBrace();
        var decls: std.ArrayListUnmanaged(ast_mod.Decl) = .empty;

        while (true) {
            if (try self.checkCloseBrace()) break;
            if (try self.atEnd()) break;

            const decl = self.parseTopDecl() catch |err| switch (err) {
                error.UnexpectedToken, error.InvalidSyntax => {
                    try self.synchronize();
                    while (try self.matchSemi()) {}
                    continue;
                },
                else => return err,
            };
            if (decl) |d| {
                try decls.append(self.allocator, d);
            }
            while (try self.matchSemi()) {}
        }

        _ = try self.expectCloseBrace();
        return try decls.toOwnedSlice(self.allocator);
    }

    // ── Data declarations ──────────────────────────────────────────────

    fn parseDataDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_data)).span;
        const name_tok = try self.expect(.conid);

        // Type variables
        var tyvars: std.ArrayListUnmanaged([]const u8) = .empty;
        while (try self.check(.varid)) {
            const tv = try self.advance();
            try tyvars.append(self.allocator, tv.token.varid);
        }

        // Check for GADT-style declaration: data T a where { ... }
        // GADT constructors have the form: Con :: Type
        const is_gadt = try self.check(.kw_where);

        var constructors: std.ArrayListUnmanaged(ast_mod.ConDecl) = .empty;
        if (try self.match(.equals) != null) {
            // Standard Haskell 98 style: data T a = Con1 ... | Con2 ...
            const first = try self.parseConDecl();
            try constructors.append(self.allocator, first);
            while (try self.match(.pipe) != null) {
                const con = try self.parseConDecl();
                try constructors.append(self.allocator, con);
            }
        } else if (is_gadt) {
            // GADT style: data T a where { Con1 :: Type1 ; Con2 :: Type2 }
            _ = try self.advance(); // consume `where`
            _ = try self.expectOpenBrace();
            while (true) {
                if (try self.checkCloseBrace()) break;
                if (try self.atEnd()) break;

                const con = try self.parseGADTConDecl();
                try constructors.append(self.allocator, con);

                while (try self.matchSemi()) {}
            }
            _ = try self.expectCloseBrace();
        }

        // Deriving
        const deriving = try self.parseDerivingClause();

        return .{ .Data = .{
            .name = name_tok.token.conid,
            .tyvars = try tyvars.toOwnedSlice(self.allocator),
            .constructors = try constructors.toOwnedSlice(self.allocator),
            .deriving = deriving,
            .span = self.spanFrom(start),
        } };
    }

    /// Parse a GADT constructor declaration: Con :: Type
    fn parseGADTConDecl(self: *Parser) ParseError!ast_mod.ConDecl {
        const start = try self.currentSpan();
        const name_tok = try self.expect(.conid);

        // Parse the type annotation :: Type
        _ = try self.expect(.dcolon);
        const gadt_type = try self.parseType();

        return ast_mod.ConDecl{
            .name = name_tok.token.conid,
            .fields = &.{}, // GADT constructors don't use fields
            .span = self.spanFrom(start),
            .gadt_type = gadt_type,
        };
    }

    // Parse standard (H98) constructor declaration: Con t1 t2 ...
    fn parseConDecl(self: *Parser) ParseError!ast_mod.ConDecl {
        const start = try self.currentSpan();
        const name_tok = try self.expect(.conid);

        var fields: std.ArrayListUnmanaged(ast_mod.FieldDecl) = .empty;
        // Parse fields as atomic types (constructor arguments)
        while (true) {
            const ty = try self.tryParseAtomicType() orelse break;
            try fields.append(self.allocator, .{ .Plain = ty });
        }

        return ast_mod.ConDecl{
            .name = name_tok.token.conid,
            .fields = try fields.toOwnedSlice(self.allocator),
            .span = self.spanFrom(start),
        };
    }

    fn parseDerivingClause(self: *Parser) ParseError![]const []const u8 {
        if (try self.match(.kw_deriving) == null) return &.{};

        if (try self.check(.open_paren)) {
            _ = try self.advance();
            var classes: std.ArrayListUnmanaged([]const u8) = .empty;
            while (true) {
                if (try self.check(.close_paren)) break;
                const cls = try self.expect(.conid);
                try classes.append(self.allocator, cls.token.conid);
                if (try self.match(.comma) == null) break;
            }
            _ = try self.expect(.close_paren);
            return classes.toOwnedSlice(self.allocator);
        }

        // Single class: deriving Show
        const cls = try self.expect(.conid);
        return self.allocSlice([]const u8, &.{cls.token.conid});
    }

    // ── Newtype declarations ───────────────────────────────────────────

    fn parseNewtypeDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_newtype)).span;
        const name_tok = try self.expect(.conid);

        var tyvars: std.ArrayListUnmanaged([]const u8) = .empty;
        while (try self.check(.varid)) {
            const tv = try self.advance();
            try tyvars.append(self.allocator, tv.token.varid);
        }

        _ = try self.expect(.equals);
        const constructor = try self.parseConDecl();
        const deriving = try self.parseDerivingClause();

        return .{ .Newtype = .{
            .name = name_tok.token.conid,
            .tyvars = try tyvars.toOwnedSlice(self.allocator),
            .constructor = constructor,
            .deriving = deriving,
            .span = self.spanFrom(start),
        } };
    }

    // ── Type alias ─────────────────────────────────────────────────────

    fn parseTypeAliasDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_type)).span;
        const name_tok = try self.expect(.conid);

        var tyvars: std.ArrayListUnmanaged([]const u8) = .empty;
        while (try self.check(.varid)) {
            const tv = try self.advance();
            try tyvars.append(self.allocator, tv.token.varid);
        }

        _ = try self.expect(.equals);
        const ty = try self.parseType();

        return .{ .Type = .{
            .name = name_tok.token.conid,
            .tyvars = try tyvars.toOwnedSlice(self.allocator),
            .type = ty,
            .span = self.spanFrom(start),
        } };
    }

    // ── Class declaration ──────────────────────────────────────────────

    fn parseClassDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_class)).span;

        // Parse optional superclass context: (Super a) => ...
        const context = try self.parseContextOptional();

        // Parse class name
        const name_tok = try self.expect(.conid);

        // Parse type variables
        var tyvars: std.ArrayListUnmanaged([]const u8) = .empty;
        while (try self.check(.varid)) {
            const tv = try self.advance();
            try tyvars.append(self.allocator, tv.token.varid);
        }

        // Parse class body: type signatures and optional default implementations.
        //
        // A class body may contain two kinds of items (Haskell 2010 §4.3.1):
        //   1. Type signatures:  `name :: Type`
        //   2. Default equations: `name pat… = expr` (on a separate layout line)
        //
        // We collect type signatures and default equations independently,
        // then merge them by method name into ClassMethod nodes.
        //
        // Maps are keyed by name ([]const u8) into their respective lists.
        // We use parallel slices rather than a hash map to avoid dependency on
        // external map libraries while keeping the code simple.
        const MethodTypeSig = struct { name: []const u8, type: ast_mod.Type };
        const MethodDefault = struct { name: []const u8, impl: ast_mod.Match };

        var type_sigs: std.ArrayListUnmanaged(MethodTypeSig) = .empty;
        var defaults: std.ArrayListUnmanaged(MethodDefault) = .empty;

        if (try self.match(.kw_where) != null) {
            _ = try self.expectOpenBrace();
            while (true) {
                if (try self.checkCloseBrace()) break;
                if (try self.atEnd()) break;

                // Determine the method name and whether this item is a type
                // signature or a default equation.
                //
                // Type sig:   `name :: Type`  or  `(op) :: Type`
                // Default eq: `name pats… = rhs`  (name followed by non-`::`).

                // Handle parenthesized operator name: (==) :: …
                const item_name: []const u8 = if (try self.check(.open_paren)) blk: {
                    const tok1 = try self.peekAt(1);
                    if (std.meta.activeTag(tok1.token) == .varsym) {
                        const tok2 = try self.peekAt(2);
                        if (std.meta.activeTag(tok2.token) == .close_paren) {
                            _ = try self.advance(); // (
                            const op_tok = try self.advance(); // operator symbol
                            _ = try self.advance(); // )
                            break :blk op_tok.token.varsym;
                        }
                    }
                    // Not an operator — unexpected open paren in class body.
                    const got = try self.peek();
                    try self.emitErrorMsg(got.span, "expected method name in class declaration");
                    return error.UnexpectedToken;
                } else if (try self.check(.varid)) blk: {
                    break :blk (try self.advance()).token.varid;
                } else {
                    const got = try self.peek();
                    try self.emitErrorMsg(got.span, "expected method name in class declaration");
                    return error.UnexpectedToken;
                };

                if (try self.check(.dcolon)) {
                    // Type signature: name :: Type
                    _ = try self.advance(); // consume ::
                    const ty = try self.parseType();
                    try type_sigs.append(self.allocator, .{ .name = item_name, .type = ty });
                } else {
                    // Default equation: name pats… = rhs [where …]
                    var pats: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
                    while (try self.tryParseArgPattern()) |pat| {
                        try pats.append(self.allocator, pat);
                    }
                    const rhs = try self.parseRhs();
                    const where_clause = try self.parseWhereClause();
                    const impl = ast_mod.Match{
                        .patterns = try pats.toOwnedSlice(self.allocator),
                        .rhs = rhs,
                        .where_clause = where_clause,
                        .span = self.spanFrom(start),
                    };
                    try defaults.append(self.allocator, .{ .name = item_name, .impl = impl });
                }

                while (try self.matchSemi()) {}
            }
            _ = try self.expectCloseBrace();
        }

        // Merge type signatures and default equations into ClassMethod nodes.
        // Every type signature becomes a method; a default equation without a
        // corresponding type signature is silently dropped (ill-formed class).
        var methods: std.ArrayListUnmanaged(ast_mod.ClassMethod) = .empty;
        for (type_sigs.items) |sig| {
            // Look up a matching default equation by name.
            var default_impl: ?ast_mod.Match = null;
            for (defaults.items) |def| {
                if (std.mem.eql(u8, def.name, sig.name)) {
                    default_impl = def.impl;
                    break;
                }
            }
            try methods.append(self.allocator, .{
                .name = sig.name,
                .type = sig.type,
                .default_implementation = default_impl,
            });
        }

        return .{ .Class = .{
            .context = context,
            .class_name = name_tok.token.conid,
            .tyvars = try tyvars.toOwnedSlice(self.allocator),
            .methods = try methods.toOwnedSlice(self.allocator),
            .span = self.spanFrom(start),
        } };
    }

    // ── Instance declaration ───────────────────────────────────────────

    fn parseInstanceDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_instance)).span;

        // Parse optional context from the instance head
        const context = try self.parseContextOptional();

        // Parse the instance type (e.g., Eq Bool or Monad (Maybe a))
        const ty = try self.parseType();

        var bindings: std.ArrayListUnmanaged(ast_mod.FunBinding) = .empty;
        if (try self.match(.kw_where) != null) {
            _ = try self.expectOpenBrace();
            while (true) {
                if (try self.checkCloseBrace()) break;
                if (try self.atEnd()) break;

                const decl = self.parseTopDecl() catch |err| switch (err) {
                    error.UnexpectedToken, error.InvalidSyntax => {
                        try self.synchronize();
                        while (try self.matchSemi()) {}
                        continue;
                    },
                    else => return err,
                };
                if (decl) |d| {
                    switch (d) {
                        .FunBind => |fb| try bindings.append(self.allocator, fb),
                        else => {},
                    }
                }
                while (try self.matchSemi()) {}
            }
            _ = try self.expectCloseBrace();
        }

        return .{ .Instance = .{
            .context = context,
            .constructor_type = ty,
            .bindings = try bindings.toOwnedSlice(self.allocator),
            .span = self.spanFrom(start),
        } };
    }

    // ── Default declaration ────────────────────────────────────────────

    fn parseDefaultDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_default)).span;
        _ = try self.expect(.open_paren);
        var types: std.ArrayListUnmanaged(ast_mod.Type) = .empty;
        while (true) {
            if (try self.check(.close_paren)) break;
            const ty = try self.parseType();
            try types.append(self.allocator, ty);
            if (try self.match(.comma) == null) break;
        }
        _ = try self.expect(.close_paren);

        return .{ .Default = .{
            .types = try types.toOwnedSlice(self.allocator),
            .span = self.spanFrom(start),
        } };
    }

    // ── Fixity declarations ────────────────────────────────────────────

    fn parseFixityDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = try self.currentSpan();
        const fixity_tok = try self.advance();
        const fixity: ast_mod.Fixity = switch (std.meta.activeTag(fixity_tok.token)) {
            .kw_infixl => .InfixL,
            .kw_infixr => .InfixR,
            .kw_infix => .InfixN,
            else => unreachable,
        };

        // Parse precedence (optional, defaults to 9)
        var prec: u8 = 9;
        if (try self.check(.lit_integer)) {
            const prec_tok = try self.advance();
            prec = @intCast(@min(9, @max(0, prec_tok.token.lit_integer)));
        }

        // Parse operator names and register them in the fixity environment.
        // Names may be symbol operators (varsym/consym) or backtick-quoted
        // identifiers (varid/conid inside backticks).
        while (true) {
            const tag = try self.peekTag();
            const op_name: []const u8 = if (tag == .varsym)
                (try self.advance()).token.varsym
            else if (tag == .consym)
                (try self.advance()).token.consym
            else if (tag == .varid)
                (try self.advance()).token.varid
            else if (tag == .backtick) blk: {
                // `name` — backtick-wrapped identifier in fixity declaration
                _ = try self.advance(); // opening backtick
                const id_tok = try self.peek();
                const id_name: []const u8 = switch (std.meta.activeTag(id_tok.token)) {
                    .varid => blk2: {
                        _ = try self.advance();
                        break :blk2 id_tok.token.varid;
                    },
                    .conid => blk2: {
                        _ = try self.advance();
                        break :blk2 id_tok.token.conid;
                    },
                    else => {
                        try self.emitErrorMsg(id_tok.span, "expected identifier in backtick fixity declaration");
                        return error.UnexpectedToken;
                    },
                };
                _ = try self.expect(.backtick); // closing backtick
                break :blk id_name;
            } else
                break;

            try self.registerFixity(op_name, fixity, prec);

            if (try self.match(.comma) == null) break;
        }

        // Fixity declarations are parser metadata; they don't produce AST nodes.
        // TODO: Add FixityDecl to Decl union when needed for pretty-printing.
        _ = start;
        return null;
    }

    // ── Type parsing ───────────────────────────────────────────────────
    // (Issue #32: Type expressions)

    /// Parse a complete type, including optional forall quantification
    /// and type class constraints.
    ///
    /// Grammar:
    ///   type        -> forall . type | context=> type | ty
    ///   forall      -> forall tyvars . type
    ///   context     -> ( constraints ) => | constraint =>
    ///   constraints -> constraint , constraints | constraint
    ///   constraint  -> qtycon tyvar_1 ... tyvar_n | ( type )
    ///   ty          -> tyapps (-> ty)*
    ///   tyapps      -> tyapp tyapp*
    ///   tyapp       -> atype
    ///   atype       -> gtycon | tyvar | ( ty ) | ( tys ) | [ ty ]
    ///   tys         -> ty , tys | ty
    ///
    /// Precedence:
    ///   forall:   outermost, binds over context
    ///   context:  binds over -> and type application
    ///   function: right-associative, lowest precedence in type expressions
    ///   app:      left-associative
    fn parseType(self: *Parser) ParseError!ast_mod.Type {
        // forall quantification: forall a b. Type
        if (try self.check(.kw_forall)) {
            return try self.parseForall();
        }

        // context: (Eq a, Show a) => Type OR Eq a => Type
        // Check for parenthesized context first
        if (try self.parseContextOptional()) |ctx| {
            // Consumed the context and =>, now parse the type
            const ty = try self.parseTy();
            return .{
                .Forall = .{
                    .tyvars = &.{},
                    .context = ctx,
                    .type = try self.allocNode(ast_mod.Type, ty),
                },
            };
        }

        // Check for single constraint without parentheses: Eq a => Type
        if (try self.check(.conid)) {
            // This might be a context: ConId => Type
            // Use lookahead to see if after the conid and types we see =>
            if (try self.lookaheadForSingleContextConstraint()) {
                return try self.parseSingleContextType();
            }
        }

        return try self.parseTy();
    }

    /// Look ahead to check if we have a single constraint context: ConId ... =>
    fn lookaheadForSingleContextConstraint(self: *Parser) ParseError!bool {
        // Current token is conid (already checked by caller)
        // Peek ahead: conid + types + =>
        var offset: u32 = 1;

        // Skip past type applications (conid, varid, or parenthesized types)
        while (true) {
            const tok = try self.peekAt(offset);
            offset += 1;
            switch (std.meta.activeTag(tok.token)) {
                .varid => {}, // type variable, continue
                .conid => {}, // type constructor, continue
                .open_paren => {
                    // Skip over parenthesized type
                    var depth: u32 = 1;
                    while (depth > 0) {
                        const p = try self.peekAt(offset);
                        offset += 1;
                        switch (std.meta.activeTag(p.token)) {
                            .open_paren => depth += 1,
                            .close_paren => depth -= 1,
                            .eof => return false,
                            else => {},
                        }
                    }
                },
                .open_bracket => {
                    // Skip over list type
                    var depth: u32 = 1;
                    while (depth > 0) {
                        const b = try self.peekAt(offset);
                        offset += 1;
                        switch (std.meta.activeTag(b.token)) {
                            .open_bracket => depth += 1,
                            .close_bracket => depth -= 1,
                            .eof => return false,
                            else => {},
                        }
                    }
                },
                .darrow => return true, // Found =>, this is a context!
                else => return false, // Found something else, not a context
            }
        }
    }

    /// Parse a type with a single (non-parenthesized) constraint: Eq a => Type
    fn parseSingleContextType(self: *Parser) ParseError!ast_mod.Type {
        // Parse the single constraint
        const class_tok = try self.expect(.conid);

        // Parse the type applications for this constraint
        var types: std.ArrayListUnmanaged(ast_mod.Type) = .empty;
        while (try self.isTypeStart()) {
            const ty = try self.parseTypeApp();
            try types.append(self.allocator, ty);
        }

        // Expect =>
        _ = try self.expect(.darrow);

        // Parse the actual type
        const ty = try self.parseTy();

        return .{
            .Forall = .{
                .tyvars = &.{},
                .context = .{
                    .constraints = try self.allocSlice(ast_mod.Assertion, &.{
                        .{
                            .class_name = class_tok.token.conid,
                            .types = try types.toOwnedSlice(self.allocator),
                        },
                    }),
                },
                .type = try self.allocNode(ast_mod.Type, ty),
            },
        };
    }

    /// Parse forall quantification: `forall a b c. Type`
    fn parseForall(self: *Parser) ParseError!ast_mod.Type {
        _ = try self.expect(.kw_forall);

        // Parse type variables
        var tyvars: std.ArrayListUnmanaged([]const u8) = .empty;
        while (try self.check(.varid)) {
            const tv = try self.advance();
            try tyvars.append(self.allocator, tv.token.varid);
        }

        // Expect dot (lexed as varsym)
        const dot_tok = try self.expect(.varsym);
        if (!std.mem.eql(u8, dot_tok.token.varsym, ".")) {
            try self.emitErrorMsg(dot_tok.span, "expected '.' after type variables in forall quantification");
            return error.UnexpectedToken;
        }

        // Parse optional context (can be parenthesized or single)
        var context: ?ast_mod.Context = null;
        if (try self.parseContextOptional()) |ctx| {
            context = ctx;
        } else if (try self.check(.conid) and try self.lookaheadForSingleContextConstraint()) {
            context = .{
                .constraints = try self.parseSingleContextConstraints(),
            };
        }

        // Parse the type
        const ty = try self.parseTy();

        return .{
            .Forall = .{
                .tyvars = try tyvars.toOwnedSlice(self.allocator),
                .context = context,
                .type = try self.allocNode(ast_mod.Type, ty),
            },
        };
    }

    /// Parse single context constraints (without parentheses but WITH =>) for use in forall
    /// Returns just the constraints slice
    fn parseSingleContextConstraints(self: *Parser) ParseError![]const ast_mod.Assertion {
        var constraints: std.ArrayListUnmanaged(ast_mod.Assertion) = .empty;

        const class_tok = try self.expect(.conid);

        // Parse the type applications for this constraint
        var types: std.ArrayListUnmanaged(ast_mod.Type) = .empty;
        while (try self.isTypeStart()) {
            const ty = try self.parseTypeApp();
            try types.append(self.allocator, ty);
        }

        try constraints.append(self.allocator, .{
            .class_name = class_tok.token.conid,
            .types = try types.toOwnedSlice(self.allocator),
        });

        // Consume the =>
        _ = try self.expect(.darrow);

        return try constraints.toOwnedSlice(self.allocator);
    }

    /// Parse an optional context prefix, handling two forms (Haskell 2010 §4.1.3):
    ///
    ///   Parenthesized: `(Eq a, Show b) =>`  — one or more constraints in parens
    ///   Bare single:   `Eq a =>`            — exactly one constraint, no parens
    ///
    /// Returns null if no context is present. Uses lookahead to distinguish a
    /// context from the declaration head that follows it (e.g. the class name).
    fn parseContextOptional(self: *Parser) ParseError!?ast_mod.Context {
        const tag = try self.peekTag();

        // ── Parenthesized context: ( constraints ) => ──────────────────────
        if (tag == .open_paren) {
            // Token 1 must be conid (class name) for a context.
            const tok1 = try self.peekAt(1);
            if (std.meta.activeTag(tok1.token) != .conid) return null;

            // Scan forward through balanced parens to find ) followed by =>.
            var depth: u32 = 1;
            var offset: u32 = 1;
            while (depth > 0) {
                offset += 1;
                const tok = try self.peekAt(offset);
                switch (std.meta.activeTag(tok.token)) {
                    .open_paren => depth += 1,
                    .close_paren => depth -= 1,
                    .eof => return null,
                    else => {},
                }
            }
            offset += 1;
            const after_paren = try self.peekAt(offset);
            if (std.meta.activeTag(after_paren.token) != .darrow) return null;

            // Confirmed parenthesized context — consume it.
            _ = try self.advance(); // (
            const constraints = try self.parseConstraints();
            _ = try self.expect(.close_paren);
            _ = try self.expect(.darrow);
            return ast_mod.Context{ .constraints = constraints };
        }

        // ── Bare single-constraint context: ClassName tyvar … => ───────────
        // Only attempted when the caller is in a declaration-head position
        // (class/instance head), where darrow cannot appear in the head itself.
        // The lookahead is identical to lookaheadForSingleContextConstraint but
        // restricted to tokens that could only appear in a type constraint
        // (no arrow, no equals, no where, no braces).
        if (tag == .conid) {
            if (try self.lookaheadBareContext()) {
                const constraint = try self.parseConstraint();
                _ = try self.expect(.darrow);
                const constraints = try self.allocSlice(ast_mod.Assertion, &.{constraint});
                return ast_mod.Context{ .constraints = constraints };
            }
        }

        return null;
    }

    /// Lookahead check: is the current conid token the start of a bare
    /// single-constraint context followed by `=>`?
    ///
    /// Scans forward skipping conids, varids, and balanced parens/brackets.
    /// Returns true only if `=>` is found before any token that can only
    /// appear in a declaration head (arrow `->`, `=`, `where`, braces, EOF).
    ///
    /// This is deliberately conservative: it returns false if it sees `->`,
    /// which cannot appear inside a constraint but CAN appear in a type after
    /// the constraint. This prevents misidentifying `Eq a -> b` as a context.
    fn lookaheadBareContext(self: *Parser) ParseError!bool {
        var offset: u32 = 1; // start past the already-peeked conid
        while (true) {
            const tok = try self.peekAt(offset);
            switch (std.meta.activeTag(tok.token)) {
                .darrow => return true,
                // Tokens that terminate the bare constraint scan without darrow.
                .arrow_right, .equals, .kw_where,
                .open_brace, .v_open_brace, .close_brace, .v_close_brace,
                .semi, .v_semi, .eof => return false,
                .open_paren => {
                    // Skip balanced parens (e.g. Monad (m a) =>)
                    offset += 1;
                    var depth: u32 = 1;
                    while (depth > 0) {
                        const inner = try self.peekAt(offset);
                        offset += 1;
                        switch (std.meta.activeTag(inner.token)) {
                            .open_paren => depth += 1,
                            .close_paren => depth -= 1,
                            .eof => return false,
                            else => {},
                        }
                    }
                },
                .open_bracket => {
                    // Skip balanced brackets (e.g. Container [] =>)
                    offset += 1;
                    var depth: u32 = 1;
                    while (depth > 0) {
                        const inner = try self.peekAt(offset);
                        offset += 1;
                        switch (std.meta.activeTag(inner.token)) {
                            .open_bracket => depth += 1,
                            .close_bracket => depth -= 1,
                            .eof => return false,
                            else => {},
                        }
                    }
                },
                else => {}, // varid, conid, etc. — part of constraint
            }
            offset += 1;
        }
    }

    /// Parse context constraints: `Eq a, Show b`, where we already know this is a context
    /// Assumes we've consumed the opening paren and confirmed the first token is conid
    fn parseConstraints(self: *Parser) ParseError![]const ast_mod.Assertion {
        var constraints: std.ArrayListUnmanaged(ast_mod.Assertion) = .empty;

        // Parse first constraint
        const first = try self.parseConstraint();
        try constraints.append(self.allocator, first);

        // Parse additional constraints separated by commas
        while (try self.match(.comma) != null) {
            const constraint = try self.parseConstraint();
            try constraints.append(self.allocator, constraint);
        }

        return try constraints.toOwnedSlice(self.allocator);
    }

    /// Parse a single constraint: `Eq a`, `Show Int`, `Monad m`
    /// assumes the first token is a conid (already checked by caller)
    fn parseConstraint(self: *Parser) ParseError!ast_mod.Assertion {
        // Class name (must be a conid)
        const class_tok = try self.expect(.conid);

        // Parse the type applications: could be a single tyvar or a more complex type
        var types: std.ArrayListUnmanaged(ast_mod.Type) = .empty;

        while (try self.isTypeStart()) {
            const ty = try self.parseTypeApp();
            try types.append(self.allocator, ty);
        }

        // If no types were parsed, we need at least one
        if (types.items.len == 0) {
            try self.emitErrorMsg(class_tok.span, "type constraint requires at least one type argument");
            return error.UnexpectedToken;
        }

        return ast_mod.Assertion{
            .class_name = class_tok.token.conid,
            .types = try types.toOwnedSlice(self.allocator),
        };
    }

    /// Check if current token can start a type
    fn isTypeStart(self: *Parser) ParseError!bool {
        const tag = try self.peekTag();
        return switch (tag) {
            .varid, .conid, .open_paren, .open_bracket => true,
            else => false,
        };
    }

    /// Parse a type without forall or context (the base type expressions)
    fn parseTy(self: *Parser) ParseError!ast_mod.Type {
        const ty = try self.parseTypeApp();

        // Function arrow: a -> b -> c (right-associative)
        if (try self.check(.arrow_right)) {
            return try self.parseFunType(ty);
        }

        return ty;
    }

    /// Parse a function type: `ty -> ty -> ty` (right-associative)
    fn parseFunType(self: *Parser, first_ty: ast_mod.Type) ParseError!ast_mod.Type {
        var parts: std.ArrayListUnmanaged(*const ast_mod.Type) = .empty;
        const first = try self.allocNode(ast_mod.Type, first_ty);
        try parts.append(self.allocator, first);

        while (try self.match(.arrow_right) != null) {
            const next = try self.parseTy();
            try parts.append(self.allocator, try self.allocNode(ast_mod.Type, next));
        }

        return .{ .Fun = try parts.toOwnedSlice(self.allocator) };
    }

    fn parseTypeApp(self: *Parser) ParseError!ast_mod.Type {
        var parts: std.ArrayListUnmanaged(*const ast_mod.Type) = .empty;
        const first = try self.parseAtomicType();
        try parts.append(self.allocator, try self.allocNode(ast_mod.Type, first));

        while (true) {
            const arg = try self.tryParseAtomicType() orelse break;
            try parts.append(self.allocator, try self.allocNode(ast_mod.Type, arg));
        }

        if (parts.items.len == 1) {
            const only = parts.items[0].*;
            self.allocator.destroy(parts.items[0]);
            self.allocator.free(try parts.toOwnedSlice(self.allocator));
            return only;
        }

        return .{ .App = try parts.toOwnedSlice(self.allocator) };
    }

    fn parseAtomicType(self: *Parser) ParseError!ast_mod.Type {
        return try self.tryParseAtomicType() orelse {
            const got = try self.peek();
            try self.emitErrorMsg(got.span, "expected type");
            return error.UnexpectedToken;
        };
    }

    fn tryParseAtomicType(self: *Parser) ParseError!?ast_mod.Type {
        const tag = try self.peekTag();
        switch (tag) {
            .conid => {
                const tok = try self.advance();
                return .{ .Con = .{
                    .name = tok.token.conid,
                    .span = tok.span,
                } };
            },
            .varid => {
                const tok = try self.advance();
                return .{ .Var = tok.token.varid };
            },
            .open_paren => {
                _ = try self.advance();
                // Unit type ()
                if (try self.check(.close_paren)) {
                    _ = try self.advance();
                    return .{ .Tuple = &.{} };
                }
                // Tuple type or parenthesized type
                const first = try self.parseType();
                if (try self.check(.comma)) {
                    var parts: std.ArrayListUnmanaged(*const ast_mod.Type) = .empty;
                    try parts.append(self.allocator, try self.allocNode(ast_mod.Type, first));
                    while (try self.match(.comma) != null) {
                        const next = try self.parseType();
                        try parts.append(self.allocator, try self.allocNode(ast_mod.Type, next));
                    }
                    _ = try self.expect(.close_paren);
                    return .{ .Tuple = try parts.toOwnedSlice(self.allocator) };
                }
                _ = try self.expect(.close_paren);
                return .{ .Paren = try self.allocNode(ast_mod.Type, first) };
            },
            .open_bracket => {
                _ = try self.advance();
                const inner = try self.parseType();
                _ = try self.expect(.close_bracket);
                return .{ .List = try self.allocNode(ast_mod.Type, inner) };
            },
            else => return null,
        }
    }

    // ── Expression parsing ───────────────────────────────────────────
    //
    // Grammar hierarchy (Haskell 2010 §3):
    //   exp      → infixexp                  (top level)
    //   infixexp → lexp (qop lexp)*          (infix operators, prec 0–9)
    //   lexp     → fexp                      (lambda/let/case/if/do are issue #30)
    //   fexp     → aexp (aexp)*              (function application, highest prec)
    //   aexp     → var | con | lit | (exp) | [exp,…] | …
    //
    // We use precedence climbing for the infixexp level.

    fn parseExpr(self: *Parser) ParseError!ast_mod.Expr {
        // parseInfixExpr delegates to continueInfixExpr which handles
        // both operator climbing and type annotations (expr :: Type).
        return self.parseInfixExpr(0);
    }

    /// Check if we're looking at a type annotation (::)
    fn isTypeAnnotation(self: *Parser) ParseError!bool {
        const tag = try self.peekTag();
        if (tag == .dcolon) return true;
        if (tag == .consym) {
            const tok = try self.peek();
            return std.mem.eql(u8, tok.token.consym, "::");
        }
        return false;
    }

    /// Parse a type annotation: expr :: Type
    fn parseTypeAnnotation(self: *Parser, left_expr: ast_mod.Expr) ParseError!ast_mod.Expr {
        _ = try self.advance(); // consume ::
        const ty = try self.parseType();
        return .{ .TypeAnn = .{
            .expr = try self.allocNode(ast_mod.Expr, left_expr),
            .type = ty,
        } };
    }

    /// Precedence climbing for infix operators.
    ///
    /// Parses a function-application chain (fexp) as the initial LHS, then
    /// delegates to `continueInfixExpr` for the climbing loop. Handles
    /// varsym, consym, binary minus, and backtick-enclosed identifiers.
    ///
    /// Backtick infix: `f`  →  InfixApp with op.name = "f"
    /// (Haskell 2010 §3.4)
    fn parseInfixExpr(self: *Parser, min_prec: u8) ParseError!ast_mod.Expr {
        const lhs = try self.parseAppExpr();
        return self.continueInfixExpr(lhs, min_prec);
    }

    /// Continue precedence climbing from an already-parsed LHS expression.
    ///
    /// This is the infix-climbing loop of `parseInfixExpr` factored out so
    /// that callers (e.g. the parenthesised-expression parser) can provide
    /// an LHS that was parsed by a different means (e.g. `parseAppExpr`) and
    /// still get full operator support including backtick infix.
    ///
    /// Also handles type annotations (`expr :: Type`) which are not strictly
    /// infix operators but appear in expression position.
    fn continueInfixExpr(self: *Parser, initial_lhs: ast_mod.Expr, min_prec: u8) ParseError!ast_mod.Expr {
        var lhs = initial_lhs;

        while (true) {
            const tag = try self.peekTag();

            const is_sym = (tag == .varsym or tag == .consym);
            const is_minus = (tag == .minus);
            const is_backtick = (tag == .backtick);
            if (!is_sym and !is_minus and !is_backtick) break;

            const op_tok: LocatedToken = try self.peek();
            const op_name: []const u8 = if (is_backtick) blk: {
                const id_tok = try self.peekAt(1);
                const id_name: []const u8 = switch (std.meta.activeTag(id_tok.token)) {
                    .varid => id_tok.token.varid,
                    .conid => id_tok.token.conid,
                    else => break,
                };
                const close_tok = try self.peekAt(2);
                if (std.meta.activeTag(close_tok.token) != .backtick) break;
                break :blk id_name;
            } else if (is_minus)
                "-"
            else switch (op_tok.token) {
                .varsym => |s| s,
                .consym => |c| c,
                else => unreachable,
            };

            const info = self.getFixity(op_name) orelse default_fixity;
            if (info.precedence < min_prec) break;
            if (info.fixity == .InfixN and info.precedence == min_prec and min_prec > 0) break;

            const next_prec: u8 = switch (info.fixity) {
                .InfixL, .InfixN => info.precedence + 1,
                .InfixR => info.precedence,
            };

            const op_span: SourceSpan = if (is_backtick) blk: {
                const bt1 = try self.advance();
                const id = try self.advance();
                const bt2 = try self.advance();
                break :blk bt1.span.merge(bt2.span).merge(id.span);
            } else blk: {
                _ = try self.advance();
                break :blk op_tok.span;
            };

            const rhs = try self.parseInfixExpr(next_prec);

            const lhs_node = try self.allocNode(ast_mod.Expr, lhs);
            const rhs_node = try self.allocNode(ast_mod.Expr, rhs);
            lhs = .{ .InfixApp = .{
                .left = lhs_node,
                .op = .{ .name = op_name, .span = op_span },
                .right = rhs_node,
            } };
        }

        // Type annotation: expr :: Type
        // Binds looser than all infix operators, so we check after the climbing loop.
        if (try self.isTypeAnnotation()) {
            return self.parseTypeAnnotation(lhs);
        }

        return lhs;
    }

    /// Parse a function application chain: `f x y z` → App(App(App(f, x), y), z).
    fn parseAppExpr(self: *Parser) ParseError!ast_mod.Expr {
        var func = try self.parseAtomicExpr();

        while (true) {
            const arg = try self.tryParseAtomicExpr() orelse break;
            const fn_node = try self.allocNode(ast_mod.Expr, func);
            const arg_node = try self.allocNode(ast_mod.Expr, arg);
            func = .{ .App = .{ .fn_expr = fn_node, .arg_expr = arg_node } };
        }

        return func;
    }

    fn parseAtomicExpr(self: *Parser) ParseError!ast_mod.Expr {
        return try self.tryParseAtomicExpr() orelse {
            const got = try self.peek();
            try self.emitErrorMsg(got.span, "expected expression");
            return error.UnexpectedToken;
        };
    }

    fn tryParseAtomicExpr(self: *Parser) ParseError!?ast_mod.Expr {
        const tag = try self.peekTag();
        switch (tag) {
            .varid => {
                const tok = try self.advance();
                return .{ .Var = .{ .name = tok.token.varid, .span = tok.span } };
            },
            .conid => {
                const tok = try self.advance();
                return .{ .Var = .{ .name = tok.token.conid, .span = tok.span } };
            },
            .lit_integer => {
                const tok = try self.advance();
                return .{ .Lit = .{ .Int = .{ .value = tok.token.lit_integer, .span = tok.span } } };
            },
            .lit_float => {
                const tok = try self.advance();
                return .{ .Lit = .{ .Float = .{ .value = tok.token.lit_float, .span = tok.span } } };
            },
            .lit_string => {
                const tok = try self.advance();
                return .{ .Lit = .{ .String = .{ .value = tok.token.lit_string, .span = tok.span } } };
            },
            .lit_char => {
                const tok = try self.advance();
                return .{ .Lit = .{ .Char = .{ .value = tok.token.lit_char, .span = tok.span } } };
            },
            .open_paren => {
                _ = try self.advance();
                const next_tag = try self.peekTag();

                // Check for right operator section: (op expr) or (op)
                // Right sections start with a symbol operator or backtick identifier.
                if (next_tag == .varsym or next_tag == .consym or next_tag == .minus) {
                    const op_tok = try self.advance();
                    const op_name: []const u8 = if (next_tag == .minus)
                        "-"
                    else switch (op_tok.token) {
                        .varsym => |s| s,
                        .consym => |c| c,
                        else => unreachable,
                    };

                    // Right section with expression: (op expr)
                    if (try self.check(.close_paren)) {
                        _ = try self.advance();
                        // Just the operator: (+), (-), etc. — operator as expression.
                        return .{ .Var = .{ .name = op_name, .span = op_tok.span } };
                    }

                    const right_expr = try self.parseExpr();
                    _ = try self.expect(.close_paren);
                    return .{ .RightSection = .{
                        .op = .{ .name = op_name, .span = op_tok.span },
                        .expr = try self.allocNode(ast_mod.Expr, right_expr),
                    } };
                }

                // Backtick right section: (`f` expr) or (`f`)
                // (Haskell 2010 §3.5: operator section with backtick function)
                if (next_tag == .backtick) {
                    const bt1 = try self.advance(); // opening backtick
                    const id_tok = try self.peek();
                    const op_name: []const u8 = switch (std.meta.activeTag(id_tok.token)) {
                        .varid => blk: {
                            _ = try self.advance();
                            break :blk id_tok.token.varid;
                        },
                        .conid => blk: {
                            _ = try self.advance();
                            break :blk id_tok.token.conid;
                        },
                        else => {
                            // Not a backtick section — fall through to normal paren parsing.
                            // Put backtick back by... we can't un-advance. Emit error.
                            try self.emitErrorMsg(id_tok.span, "expected identifier after backtick in section");
                            return error.UnexpectedToken;
                        },
                    };
                    const bt2 = try self.expect(.backtick); // closing backtick
                    const op_span = bt1.span.merge(bt2.span);

                    if (try self.check(.close_paren)) {
                        _ = try self.advance();
                        // (`f`) — operator as expression
                        return .{ .Var = .{ .name = op_name, .span = op_span } };
                    }

                    const right_expr = try self.parseExpr();
                    _ = try self.expect(.close_paren);
                    return .{ .RightSection = .{
                        .op = .{ .name = op_name, .span = op_span },
                        .expr = try self.allocNode(ast_mod.Expr, right_expr),
                    } };
                }

                // Unit: ()
                if (try self.check(.close_paren)) {
                    _ = try self.advance();
                    return .{ .Tuple = &.{} };
                }

                // Parse the first APP/atomic expression (not full expr, to avoid consuming infix ops for left sections)
                var first = try self.parseAppExpr();

                // Check for type annotation on the first atom: (expr :: type)
                if (try self.isTypeAnnotation()) {
                    first = try self.parseTypeAnnotation(first);
                }

                // Check for tuple: (a, b, c)
                if (try self.check(.comma)) {
                    var items: std.ArrayListUnmanaged(ast_mod.Expr) = .empty;
                    try items.append(self.allocator, first);
                    while (try self.match(.comma) != null) {
                        if (try self.check(.close_paren)) {
                            // Trailing comma
                            break;
                        }
                        const item = try self.parseExpr();
                        try items.append(self.allocator, item);
                    }
                    _ = try self.expect(.close_paren);
                    return .{ .Tuple = try items.toOwnedSlice(self.allocator) };
                }

                // Check for left operator section: (expr op)
                // Handles symbol operators (varsym/consym/minus) and backtick
                // identifiers, each followed immediately by close_paren.
                const op_tag = try self.peekTag();
                if (op_tag == .varsym or op_tag == .consym or op_tag == .minus) {
                    const after_op = try self.peekAt(1);
                    if (std.meta.activeTag(after_op.token) == .close_paren) {
                        // It's a left section: (expr op)
                        const op_tok = try self.advance();
                        const op_name: []const u8 = if (op_tag == .minus)
                            "-"
                        else switch (op_tok.token) {
                            .varsym => |s| s,
                            .consym => |c| c,
                            else => unreachable,
                        };
                        _ = try self.expect(.close_paren);
                        return .{ .LeftSection = .{
                            .expr = try self.allocNode(ast_mod.Expr, first),
                            .op = .{ .name = op_name, .span = op_tok.span },
                        } };
                    }
                }
                // Backtick left section: (expr `f`)
                if (op_tag == .backtick) {
                    const id_tok2 = try self.peekAt(1);
                    const after_id = try self.peekAt(2);
                    const is_id = std.meta.activeTag(id_tok2.token) == .varid or
                        std.meta.activeTag(id_tok2.token) == .conid;
                    const is_bt2 = std.meta.activeTag(after_id.token) == .backtick;
                    const after_bt2 = try self.peekAt(3);
                    if (is_id and is_bt2 and std.meta.activeTag(after_bt2.token) == .close_paren) {
                        // Left section: (expr `f`)
                        const bt1 = try self.advance(); // opening backtick
                        const fn_id = try self.advance(); // identifier
                        const bt2 = try self.advance(); // closing backtick
                        _ = try self.expect(.close_paren);
                        const bt_name: []const u8 = switch (std.meta.activeTag(fn_id.token)) {
                            .varid => fn_id.token.varid,
                            .conid => fn_id.token.conid,
                            else => unreachable,
                        };
                        return .{ .LeftSection = .{
                            .expr = try self.allocNode(ast_mod.Expr, first),
                            .op = .{ .name = bt_name, .span = bt1.span.merge(bt2.span) },
                        } };
                    }
                }

                // Handle infix expressions inside parentheses: (a + b), (k `div` 2).
                // Use continueInfixExpr which shares the precedence-climbing logic
                // from parseInfixExpr (including backtick support) but accepts an
                // already-parsed LHS, avoiding re-parsing `first` as an app-chain.
                const paren_result = try self.continueInfixExpr(first, 0);

                _ = try self.expect(.close_paren);
                return .{ .Paren = try self.allocNode(ast_mod.Expr, paren_result) };
            },
            .open_bracket => {
                const open_tok = try self.advance();
                if (try self.check(.close_bracket)) {
                    _ = try self.advance();
                    return .{ .List = &.{} };
                }

                // Parse the first expression.
                const first = try self.parseExpr();

                // Arithmetic sequence: [e ..] or [e .. e']
                if (try self.match(.dotdot)) |_| {
                    if (try self.check(.close_bracket)) {
                        // [e ..]  — EnumFrom
                        const close_tok = try self.advance();
                        const span = open_tok.span.merge(close_tok.span);
                        return .{ .EnumFrom = .{
                            .from = try self.allocNode(ast_mod.Expr, first),
                            .span = span,
                        } };
                    } else {
                        // [e .. e']  — EnumFromTo
                        const to = try self.parseExpr();
                        const close_tok = try self.expect(.close_bracket);
                        const span = open_tok.span.merge(close_tok.span);
                        return .{ .EnumFromTo = .{
                            .from = try self.allocNode(ast_mod.Expr, first),
                            .to = try self.allocNode(ast_mod.Expr, to),
                            .span = span,
                        } };
                    }
                }

                // List comprehension: [e | qual, qual, ...]
                // The pipe token is `.pipe` (|).
                if (try self.check(.pipe)) {
                    _ = try self.advance(); // consume '|'
                    const qualifiers = try self.parseQualifiers();
                    const close_tok = try self.expect(.close_bracket);
                    _ = close_tok;
                    return .{ .ListComp = .{
                        .expr = try self.allocNode(ast_mod.Expr, first),
                        .qualifiers = qualifiers,
                    } };
                }

                // Either a list literal or [e, e' ..] / [e, e' .. e''].
                // Consume optional comma-separated elements.
                var items: std.ArrayListUnmanaged(ast_mod.Expr) = .empty;
                try items.append(self.allocator, first);

                while (try self.match(.comma) != null) {
                    if (try self.check(.close_bracket)) {
                        // Trailing comma — plain list
                        break;
                    }
                    const item = try self.parseExpr();
                    try items.append(self.allocator, item);

                    // After the second element check for dotdot: [e, e' ..] or [e, e' .. e'']
                    if (items.items.len == 2) {
                        if (try self.match(.dotdot)) |_| {
                            const e_from = items.items[0];
                            const e_then = items.items[1];
                            items.deinit(self.allocator);
                            if (try self.check(.close_bracket)) {
                                // [e, e' ..]  — EnumFromThen
                                const close_tok = try self.advance();
                                const span = open_tok.span.merge(close_tok.span);
                                return .{ .EnumFromThen = .{
                                    .from = try self.allocNode(ast_mod.Expr, e_from),
                                    .then = try self.allocNode(ast_mod.Expr, e_then),
                                    .span = span,
                                } };
                            } else {
                                // [e, e' .. e'']  — EnumFromThenTo
                                const e_to = try self.parseExpr();
                                const close_tok = try self.expect(.close_bracket);
                                const span = open_tok.span.merge(close_tok.span);
                                return .{ .EnumFromThenTo = .{
                                    .from = try self.allocNode(ast_mod.Expr, e_from),
                                    .then = try self.allocNode(ast_mod.Expr, e_then),
                                    .to = try self.allocNode(ast_mod.Expr, e_to),
                                    .span = span,
                                } };
                            }
                        }
                    }
                }
                _ = try self.expect(.close_bracket);
                return .{ .List = try items.toOwnedSlice(self.allocator) };
            },
            .minus => {
                _ = try self.advance();
                const inner = try self.parseAtomicExpr();
                return .{ .Negate = try self.allocNode(ast_mod.Expr, inner) };
            },
            .backslash => return try self.parseLambda(),
            .kw_if => return try self.parseIf(),
            .kw_let => return try self.parseLet(),
            .kw_case => return try self.parseCase(),
            .kw_do => return try self.parseDo(),
            else => return null,
        }
    }

    /// Parse a lambda expression: \x y z -> x + y + z
    fn parseLambda(self: *Parser) ParseError!ast_mod.Expr {
        _ = try self.expect(.backslash);
        var pats: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
        while (!try self.check(.arrow_right)) {
            const name_tok = try self.expect(.varid);
            // Lambda patterns are only simple variable patterns
            try pats.append(self.allocator, .{ .Var = .{ .name = name_tok.token.varid, .span = name_tok.span } });
        }
        _ = try self.expect(.arrow_right);
        const body = try self.parseExpr();
        return .{ .Lambda = .{
            .patterns = try pats.toOwnedSlice(self.allocator),
            .body = try self.allocNode(ast_mod.Expr, body),
        } };
    }

    /// Parse an if expression: if cond then true_expr else false_expr
    fn parseIf(self: *Parser) ParseError!ast_mod.Expr {
        _ = try self.expect(.kw_if);
        const condition = try self.parseExpr();
        _ = try self.expect(.kw_then);
        const then_expr = try self.parseExpr();
        _ = try self.expect(.kw_else);
        const else_expr = try self.parseExpr();
        return .{ .If = .{
            .condition = try self.allocNode(ast_mod.Expr, condition),
            .then_expr = try self.allocNode(ast_mod.Expr, then_expr),
            .else_expr = try self.allocNode(ast_mod.Expr, else_expr),
        } };
    }

    /// Parse a let expression: let x = 1; y = 2 in x + y
    fn parseLet(self: *Parser) ParseError!ast_mod.Expr {
        _ = try self.expect(.kw_let);

        // Handle explicit or virtual open brace for let bindings
        if (try self.check(.open_brace) or try self.check(.v_open_brace)) {
            _ = try self.advance(); // consume { or virtual {
            var binds: std.ArrayListUnmanaged(ast_mod.Decl) = .empty;
            while (true) {
                if (try self.check(.close_brace) or try self.check(.v_close_brace)) {
                    _ = try self.advance(); // consume } or virtual }
                    break;
                }
                if (try self.atEnd()) break;
                const decl = try self.parseTopDecl() orelse break;
                try binds.append(self.allocator, decl);
                while (try self.matchSemi()) {}
            }
            _ = try self.expect(.kw_in);
            const body = try self.parseExpr();
            return .{ .Let = .{
                .binds = try binds.toOwnedSlice(self.allocator),
                .body = try self.allocNode(ast_mod.Expr, body),
            } };
        } else {
            // Single binding without braces: let x = 1 in x + 1
            const decl = try self.parseTopDecl() orelse {
                const got = try self.peek();
                try self.emitErrorMsg(got.span, "expected let binding");
                return error.UnexpectedToken;
            };
            var binds: std.ArrayListUnmanaged(ast_mod.Decl) = .empty;
            try binds.append(self.allocator, decl);
            _ = try self.expect(.kw_in);
            const body = try self.parseExpr();
            return .{ .Let = .{
                .binds = try binds.toOwnedSlice(self.allocator),
                .body = try self.allocNode(ast_mod.Expr, body),
            } };
        }
    }

    /// Parse a case expression: case x of { 0 -> "zero"; _ -> "other" }
    fn parseCase(self: *Parser) ParseError!ast_mod.Expr {
        _ = try self.expect(.kw_case);
        const scrutinee = try self.parseExpr();
        _ = try self.expect(.kw_of);
        _ = try self.expectOpenBrace();
        var alts: std.ArrayListUnmanaged(ast_mod.Alt) = .empty;
        const first_alt = try self.parseAlt();
        try alts.append(self.allocator, first_alt);
        while (try self.match(.semi) != null) {
            if (try self.tryParseAlt()) |alt| {
                try alts.append(self.allocator, alt);
            } else {
                // Allow trailing semicolon
                break;
            }
        }
        _ = try self.expectCloseBrace();
        return .{ .Case = .{
            .scrutinee = try self.allocNode(ast_mod.Expr, scrutinee),
            .alts = try alts.toOwnedSlice(self.allocator),
        } };
    }

    /// Parse a single case alternative: pattern -> expr where binds
    fn parseAlt(self: *Parser) ParseError!ast_mod.Alt {
        const pat = try self.parsePattern();
        const arrow_tok = try self.expect(.arrow_right);
        const start = pat.getSpan().merge(arrow_tok.span);
        const rhs = try self.parseRhs();
        return .{
            .pattern = pat,
            .rhs = rhs,
            .where_clause = null,
            .span = start,
        };
    }

    /// Try to parse a case alternative without error
    fn tryParseAlt(self: *Parser) ParseError!?ast_mod.Alt {
        if (try self.isPatternStart()) {
            return try self.parseAlt();
        }
        return null;
    }

    /// Parse do notation: do { x <- action; return x }
    fn parseDo(self: *Parser) ParseError!ast_mod.Expr {
        _ = try self.expect(.kw_do);
        _ = try self.expectOpenBrace();
        var stmts: std.ArrayListUnmanaged(ast_mod.Stmt) = .empty;

        while (true) {
            // Consume any leading semicolons (empty statements from layout).
            while (try self.matchSemi()) {}
            if (try self.checkCloseBrace()) break;
            if (try self.atEnd()) break;

            // Haskell 2010 §3.14: a do-statement is one of:
            //   let decls     — LetStmt (no "in"!)
            //   pat <- exp    — Generator
            //   exp           — plain statement
            if (try self.check(.kw_let)) {
                const let_stmt = try self.parseDoLet();
                try stmts.append(self.allocator, let_stmt);
                _ = try self.match(.semi);
                continue;
            }

            if (try self.isExprStart()) {
                // Could be a bind or a plain expression
                const expr = try self.parseExpr();
                // Check if it's a bind: pattern <- action
                if (try self.check(.arrow_left)) {
                    _ = try self.advance();
                    const action = try self.parseExpr();
                    // Extract pattern from the expression (should be a variable)
                    const binding_pat: ast_mod.Pattern = switch (expr) {
                        .Var => |q| .{ .Var = .{ .name = q.name, .span = q.span } },
                        else => {
                            try self.emitErrorMsg(expr.getSpan(), "bind pattern must be a variable");
                            return error.InvalidSyntax;
                        },
                    };
                    const gen = ast_mod.Stmt{ .Generator = .{ .pat = binding_pat, .expr = action } };
                    try stmts.append(self.allocator, gen);
                } else {
                    try stmts.append(self.allocator, .{ .Stmt = expr });
                }
                _ = try self.match(.semi);
            } else {
                break;
            }
        }
        _ = try self.expectCloseBrace();
        return .{ .Do = try stmts.toOwnedSlice(self.allocator) };
    }

    /// Parse a list of list-comprehension qualifiers separated by commas.
    ///
    /// qualifier → pat <- expr   (generator)
    ///           | let decls     (let qualifier, no 'in')
    ///           | expr          (boolean guard)
    ///
    /// Haskell 2010 §3.11
    fn parseQualifiers(self: *Parser) ParseError![]const ast_mod.Qualifier {
        var qualifiers: std.ArrayListUnmanaged(ast_mod.Qualifier) = .empty;
        const first = try self.parseQualifier();
        try qualifiers.append(self.allocator, first);
        while (try self.match(.comma) != null) {
            const q = try self.parseQualifier();
            try qualifiers.append(self.allocator, q);
        }
        return qualifiers.toOwnedSlice(self.allocator);
    }

    /// Parse a single list-comprehension qualifier.
    ///
    /// We disambiguate generator vs. guard using lookahead:
    ///   - `let` keyword → let qualifier
    ///   - parse expression, then if followed by `<-` it is a generator
    ///
    /// The let qualifier opens a layout block (like do-let) but without `in`.
    fn parseQualifier(self: *Parser) ParseError!ast_mod.Qualifier {
        // Let qualifier: let { decls }
        if (try self.check(.kw_let)) {
            _ = try self.advance(); // consume 'let'
            _ = try self.expectOpenBrace();
            var binds: std.ArrayListUnmanaged(ast_mod.Decl) = .empty;
            while (true) {
                if (try self.checkCloseBrace()) break;
                if (try self.atEnd()) break;
                const decl = try self.parseTopDecl() orelse break;
                try binds.append(self.allocator, decl);
                while (try self.matchSemi()) {}
            }
            _ = try self.expectCloseBrace();
            // A let qualifier desugars to a let expression with the
            // bound names in scope for subsequent qualifiers. We
            // represent it as a Guard wrapping a Let with a unit body,
            // which is sufficient for parsing purposes. The renamer/
            // desugarer will handle it properly.
            //
            // Per Haskell 2010 §3.11, let qualifiers are a first-class
            // construct; we store them as a special Guard expression.
            // Since the AST Qualifier union only has Generator and
            // Qualifier (guard), we represent a let-qualifier as a
            // guard whose expression is a Let with a unit body. A
            // follow-up issue will add LetQualifier to ast.Qualifier.
            // See: https://github.com/adinapoli/rusholme/issues/216
            const unit = ast_mod.Expr{ .Tuple = &.{} };
            const let_expr = ast_mod.Expr{ .Let = .{
                .binds = try binds.toOwnedSlice(self.allocator),
                .body = try self.allocNode(ast_mod.Expr, unit),
            } };
            return .{ .Qualifier = let_expr };
        }

        // Generator or guard: parse an expression first, then check for `<-`.
        //
        // For generators the left-hand side is a pattern, but since patterns
        // and expressions overlap syntactically for variable/constructor names
        // we parse an expression and convert it. Simple variables and
        // constructor patterns can be recovered from Expr nodes.
        const expr_or_pat = try self.parseExpr();

        if (try self.check(.arrow_left)) {
            _ = try self.advance(); // consume '<-'
            const gen_expr = try self.parseExpr();
            // Convert the expression to a pattern.  The common cases are:
            //   Var → Pattern.Var
            //   Con with args → Pattern.Con
            //   Tuple of vars → Pattern.Tuple
            //   Wildcard (_) is parsed as a Var named "_" — handle below.
            const gen_pat = try self.exprToPattern(expr_or_pat);
            return .{ .Generator = .{ .pat = gen_pat, .expr = gen_expr } };
        }

        // Plain boolean guard
        return .{ .Qualifier = expr_or_pat };
    }

    /// Convert an expression node to a pattern node for generator qualifiers.
    ///
    /// This is a best-effort conversion for the common cases that appear in
    /// list comprehension generators:
    ///   Var name   → Pattern.Var
    ///   Tuple      → Pattern.Tuple
    ///   Lit        → Pattern.Lit
    ///   Paren expr → Pattern.Paren
    ///   Con (App)  → Pattern.Con (constructor application)
    ///
    /// Complex patterns that require explicit pattern syntax (e.g. `(x:xs)`)
    /// must appear in a proper pattern position in a generator; those will
    /// naturally be parsed as expressions wrapping Paren which contains an
    /// InfixApp. Such cases are left for a future parser improvement.
    fn exprToPattern(self: *Parser, expr: ast_mod.Expr) ParseError!ast_mod.Pattern {
        return switch (expr) {
            .Var => |q| .{ .Var = .{ .name = q.name, .span = q.span } },
            .Lit => |l| .{ .Lit = l },
            .Tuple => |exprs| blk: {
                var pats: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
                for (exprs) |e| {
                    const p = try self.exprToPattern(e);
                    try pats.append(self.allocator, p);
                }
                const span = if (exprs.len > 0)
                    exprs[0].getSpan().merge(exprs[exprs.len - 1].getSpan())
                else
                    self.last_span;
                break :blk .{ .Tuple = .{
                    .patterns = try pats.toOwnedSlice(self.allocator),
                    .span = span,
                } };
            },
            .Paren => |inner| blk: {
                const inner_pat = try self.exprToPattern(inner.*);
                break :blk .{ .Paren = .{
                    .pat = try self.allocNode(ast_mod.Pattern, inner_pat),
                    .span = inner.getSpan(),
                } };
            },
            .App => |app| blk: {
                // Constructor application: Con arg1 arg2
                // fn_expr must be a Var (constructor name).
                switch (app.fn_expr.*) {
                    .Var => |q| {
                        const arg_pat = try self.exprToPattern(app.arg_expr.*);
                        break :blk .{ .Con = .{
                            .name = q,
                            .args = try self.allocSlice(ast_mod.Pattern, &.{arg_pat}),
                            .span = app.fn_expr.getSpan().merge(app.arg_expr.getSpan()),
                        } };
                    },
                    else => {
                        try self.emitErrorMsg(app.fn_expr.getSpan(), "expected constructor pattern in generator");
                        return error.InvalidSyntax;
                    },
                }
            },
            .InfixApp => |infix| blk: {
                // Infix constructor: p : ps
                const left_pat = try self.exprToPattern(infix.left.*);
                const right_pat = try self.exprToPattern(infix.right.*);
                break :blk .{ .InfixCon = .{
                    .left = try self.allocNode(ast_mod.Pattern, left_pat),
                    .con = infix.op,
                    .right = try self.allocNode(ast_mod.Pattern, right_pat),
                } };
            },
            else => {
                try self.emitErrorMsg(expr.getSpan(), "invalid pattern in list comprehension generator");
                return error.InvalidSyntax;
            },
        };
    }

    /// Parse `let decls` as a do-statement (Haskell 2010 §3.14).
    ///
    /// Unlike the let-expression form (`let decls in expr`), a let-statement
    /// inside a do-block has no `in`.  The layout rule opens and closes the
    /// binding group via virtual braces, just like a let-expression binding
    /// group.
    fn parseDoLet(self: *Parser) ParseError!ast_mod.Stmt {
        _ = try self.expect(.kw_let);
        _ = try self.expectOpenBrace();

        var binds: std.ArrayListUnmanaged(ast_mod.Decl) = .empty;
        while (true) {
            if (try self.checkCloseBrace()) break;
            if (try self.atEnd()) break;
            const decl = try self.parseTopDecl() orelse break;
            try binds.append(self.allocator, decl);
            while (try self.matchSemi()) {}
        }
        _ = try self.expectCloseBrace();

        return .{ .LetStmt = try binds.toOwnedSlice(self.allocator) };
    }

    /// Check if current token could start an expression
    fn isExprStart(self: *Parser) ParseError!bool {
        const tag = try self.peekTag();
        return switch (tag) {
            .varid, .conid, .lit_integer, .lit_float, .lit_string, .lit_char, .open_paren, .open_bracket, .minus, .backslash, .kw_if, .kw_let, .kw_case, .kw_do => true,
            else => false,
        };
    }

    // ── Pattern parsing ─────────────────────────────────────────────────

    /// Main entry point for pattern parsing.
    /// Handles: as-patterns, negation, infix constructors, and atomic patterns.
    pub fn parsePattern(self: *Parser) ParseError!ast_mod.Pattern {
        const start = try self.currentSpan();

        // Handle negated pattern: -x, -5, -Just 5
        if (try self.check(.minus)) {
            const minus_tok = try self.advance();
            const pat = try self.parsePattern();
            return .{ .Negate = .{
                .pat = try self.allocNode(ast_mod.Pattern, pat),
                .span = minus_tok.span.merge(pat.getSpan()),
            } };
        }

        const pat = try self.parseAtomicPattern();

        // Handle as-pattern: xs@(x:rest)
        if (try self.check(.at)) {
            _ = try self.advance();
            const right_pat = try self.parsePattern();
            // Get the variable name from the left pattern (must be a varid)
            switch (pat) {
                .Var => |v| {
                    return .{ .AsPar = .{
                        .name = v.name,
                        .name_span = v.span,
                        .pat = try self.allocNode(ast_mod.Pattern, right_pat),
                        .span = v.span.merge(right_pat.getSpan()),
                    } };
                },
                else => {
                    try self.emitErrorMsg(start, "as-pattern requires a variable name on the left of @");
                    return error.InvalidSyntax;
                },
            }
        }

        // Handle infix constructor pattern: x : xs, True && True
        // Look for operator symbols
        if (self.isAtomPattern(pat) and try self.isInfixOp()) {
            const tok = try self.advance();
            const op_name = switch (tok.token) {
                .varsym => |s| s,
                .consym => |c| c,
                else => unreachable,
            };
            const right_pat = try self.parsePattern();
            return .{ .InfixCon = .{
                .left = try self.allocNode(ast_mod.Pattern, pat),
                .con = .{ .name = op_name, .span = tok.span },
                .right = try self.allocNode(ast_mod.Pattern, right_pat),
            } };
        }

        return pat;
    }

    /// Try to parse a pattern without raising an error. Returns null if no pattern found.
    pub fn tryParsePattern(self: *Parser) ParseError!?ast_mod.Pattern {
        if (try self.isPatternStart()) {
            return try self.parsePattern();
        }
        return null;
    }

    /// Check if the current token could start a pattern.
    fn isPatternStart(self: *Parser) ParseError!bool {
        const tag = try self.peekTag();
        return switch (tag) {
            .varid, .conid, .underscore, .lit_integer, .lit_char, .lit_string, .minus, .open_paren, .open_bracket => true,
            else => false,
        };
    }

    /// Check if current is an infix operator (varsym or consym).
    fn isInfixOp(self: *Parser) ParseError!bool {
        const tag = try self.peekTag();
        return tag == .varsym or tag == .consym;
    }

    /// Check if a pattern is an "atom" pattern (can appear on left of infix op).
    fn isAtomPattern(_: *Parser, pat: ast_mod.Pattern) bool {
        return switch (pat) {
            .Var, .Con, .Lit, .Wild, .Paren, .Bang, .Tuple, .List => true,
            else => false,
        };
    }

    /// Parse an atomic pattern (no as-pattern, no infix, no negation).
    fn parseAtomicPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const tag = try self.peekTag();
        return switch (tag) {
            .varid => try self.parseVarPattern(),
            .conid => try self.parseConPattern(),
            .underscore => try self.parseWildPattern(),
            .lit_integer, .lit_char, .lit_string => try self.parseLitPattern(),
            .open_paren => try self.parseParenOrTuplePattern(),
            .open_bracket => try self.parseListPattern(),
            else => {
                const got = try self.peek();
                try self.emitErrorMsg(got.span, "expected pattern");
                return error.UnexpectedToken;
            },
        };
    }

    /// Parse variable pattern: x, foo, bar'
    fn parseVarPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const tok = try self.expect(.varid);
        return .{ .Var = .{ .name = tok.token.varid, .span = tok.span } };
    }

    /// Parse constructor pattern: Just x, Nothing, True
    fn parseConPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const tok = try self.expect(.conid);

        // Try to parse constructor arguments.
        // Each argument is an apat (Haskell 2010 §3.17.2): atomic pattern
        // with optional as-pattern suffix, but no infix constructors.
        var args: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
        defer args.deinit(self.allocator);

        while (try self.isPatternStart()) {
            const arg = try self.parseArgPattern();
            try args.append(self.allocator, arg);
        }

        const args_slice = try self.allocSlice(ast_mod.Pattern, args.items);
        const end_span = if (args.items.len > 0) args.items[args.items.len - 1].getSpan() else tok.span;
        return .{ .Con = .{
            .name = .{ .name = tok.token.conid, .span = tok.span },
            .args = args_slice,
            .span = tok.span.merge(end_span),
        } };
    }

    /// Parse wildcard pattern: _
    fn parseWildPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const tok = try self.expect(.underscore);
        return .{ .Wild = tok.span };
    }

    /// Parse literal pattern: 42, 'a', "hello"
    fn parseLitPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const tag = try self.peekTag();
        return switch (tag) {
            .lit_integer => {
                const tok = try self.advance();
                return .{ .Lit = .{ .Int = .{ .value = tok.token.lit_integer, .span = tok.span } } };
            },
            .lit_char => {
                const tok = try self.advance();
                return .{ .Lit = .{ .Char = .{ .value = tok.token.lit_char, .span = tok.span } } };
            },
            .lit_string => {
                const tok = try self.advance();
                return .{ .Lit = .{ .String = .{ .value = tok.token.lit_string, .span = tok.span } } };
            },
            else => unreachable,
        };
    }

    /// Parse parenthesized pattern or tuple: (Just x), (a, b, c), ()
    fn parseParenOrTuplePattern(self: *Parser) ParseError!ast_mod.Pattern {
        const open_tok = try self.expect(.open_paren);

        // Check for unit pattern: ()
        if (try self.check(.close_paren)) {
            const close_tok = try self.advance();
            return .{ .Tuple = .{ .patterns = &.{}, .span = open_tok.span.merge(close_tok.span) } };
        }

        // Parse first pattern
        const first = try self.parsePattern();

        // Check if this is a tuple: check for comma after first pattern
        if (try self.check(.comma)) {
            // Tuple pattern: (a, b, c)
            var patterns: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
            try patterns.append(self.allocator, first);

            while (try self.check(.comma)) {
                _ = try self.advance();
                const pat = try self.parsePattern();
                try patterns.append(self.allocator, pat);
            }

            const close_tok = try self.expect(.close_paren);
            return .{ .Tuple = .{
                .patterns = try self.allocSlice(ast_mod.Pattern, patterns.items),
                .span = open_tok.span.merge(close_tok.span),
            } };
        }

        // Single parenthesized pattern: (Just x)
        const close_tok = try self.expect(.close_paren);
        return .{ .Paren = .{
            .pat = try self.allocNode(ast_mod.Pattern, first),
            .span = open_tok.span.merge(close_tok.span),
        } };
    }

    /// Parse list pattern: [], [x, y], [x:xs]
    fn parseListPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const open_tok = try self.expect(.open_bracket);

        // Check for empty list: []
        if (try self.check(.close_bracket)) {
            const close_tok = try self.advance();
            return .{ .List = .{ .patterns = &.{}, .span = open_tok.span.merge(close_tok.span) } };
        }

        // Parse first pattern
        const first = try self.parsePattern();

        // Check for cons pattern: [x:xs]
        // The : is tokenized as consym
        if (try self.check(.consym)) {
            const cons_tok = try self.advance();
            // Verify it's actually the : operator (could be other consyms like :+:)
            if (std.mem.eql(u8, cons_tok.token.consym, ":")) {
                const rest = try self.parsePattern();
                _ = try self.expect(.close_bracket);

                // Create an InfixCon pattern with : operator
                // Note: InfixCon derives its span from left/right
                return .{ .InfixCon = .{
                    .left = try self.allocNode(ast_mod.Pattern, first),
                    .con = .{ .name = ":", .span = cons_tok.span },
                    .right = try self.allocNode(ast_mod.Pattern, rest),
                } };
            } else {
                // Got a consym other than :, treat as regular list with operator
                // For now, error out since this is unusual
                try self.emitErrorMsg(cons_tok.span, "expected : for list cons, got other constructor operator");
                return error.UnexpectedToken;
            }
        }

        // Regular list pattern: [x, y, z]
        var patterns: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
        try patterns.append(self.allocator, first);

        while (try self.check(.comma)) {
            _ = try self.advance();
            const pat = try self.parsePattern();
            try patterns.append(self.allocator, pat);
        }

        const close_tok = try self.expect(.close_bracket);
        return .{ .List = .{
            .patterns = try self.allocSlice(ast_mod.Pattern, patterns.items),
            .span = open_tok.span.merge(close_tok.span),
        } };
    }

    /// Legacy function for backward compatibility. Tries to parse an atomic pattern.
    /// Used for function arguments in value declarations.
    fn tryParseAtomicPattern(self: *Parser) ParseError!?ast_mod.Pattern {
        if (try self.isPatternStart()) {
            return try self.parseAtomicPattern();
        }
        return null;
    }

    /// Parse an argument pattern (apat per Haskell 2010 §3.17.2).
    ///
    /// An apat is an atomic pattern with an optional as-pattern suffix:
    ///   var [ @ apat ]   — as-pattern
    ///   gcon             — constructor (nullary)
    ///   literal
    ///   _                — wildcard
    ///   ( pat )          — parenthesized
    ///   ( pat1, ... )    — tuple
    ///   [ pat1, ... ]    — list
    ///
    /// Unlike `parsePattern`, this does NOT consume infix constructor operators
    /// (`:`, `||`, etc.), making it safe to use for function arguments and
    /// constructor arguments where the caller owns the infix level.
    fn parseArgPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const atom = try self.parseAtomicPattern();

        // Check for as-pattern: var@apat
        if (atom == .Var and try self.check(.at)) {
            _ = try self.advance(); // consume @
            const rhs = try self.parseArgPattern();
            return .{ .AsPar = .{
                .name = atom.Var.name,
                .name_span = atom.Var.span,
                .pat = try self.allocNode(ast_mod.Pattern, rhs),
                .span = atom.Var.span.merge(rhs.getSpan()),
            } };
        }

        return atom;
    }

    /// Try to parse an argument pattern; returns null if no pattern starts here.
    fn tryParseArgPattern(self: *Parser) ParseError!?ast_mod.Pattern {
        if (try self.isPatternStart()) {
            return try self.parseArgPattern();
        }
        return null;
    }

    // ── Allocation helpers ─────────────────────────────────────────────

    fn allocNode(self: *Parser, comptime T: type, value: T) ParseError!*const T {
        const ptr = try self.allocator.create(T);
        ptr.* = value;
        return ptr;
    }

    fn allocSlice(self: *Parser, comptime T: type, items: []const T) ParseError![]const T {
        return self.allocator.dupe(T, items);
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
    return Parser.init(allocator, layout, diags) catch |err| switch (err) {
        error.OutOfMemory => @panic("OOM in initTestParser"),
        error.UnexpectedToken, error.UnexpectedEOF, error.InvalidSyntax => @panic("parse error in initTestParser"),
    };
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

// ── Infix expression tests ─────────────────────────────────────────

/// Helper: parse `module M where\n<source>` and return the RHS expression
/// of the first FunBind declaration. Uses an ArenaAllocator wrapping
/// std.testing.allocator so all AST nodes are freed automatically.
fn parseTestExpr(
    arena: *std.heap.ArenaAllocator,
    source: []const u8,
) !ast_mod.Expr {
    const allocator = arena.allocator();
    const full = try std.fmt.allocPrint(allocator, "module M where\n{s}", .{source});
    var lexer = Lexer.init(allocator, full, 1);
    var layout = LayoutProcessor.init(allocator, &lexer);
    var diags = DiagnosticCollector.init();
    var parser = Parser.init(allocator, &layout, &diags) catch |err| switch (err) {
        error.OutOfMemory => @panic("OOM in parseTestExpr"),
        error.UnexpectedToken, error.UnexpectedEOF, error.InvalidSyntax => @panic("parse error in parseTestExpr"),
    };
    const mod = try parser.parseModule();

    const decl = mod.declarations[0];
    if (decl != .FunBind) {
        @panic("parseTestExpr: Expected FunBind");
    }

    const rhs = decl.FunBind.equations[0].rhs;
    return rhs.UnGuarded;
}

test "infix: precedence — 1 + 2 * 3 parses as 1 + (2 * 3)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "x = 1 + 2 * 3");

    // Top level: InfixApp(1, +, InfixApp(2, *, 3))
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("+", top.InfixApp.op.name);

    // Left: literal 1
    try std.testing.expect(top.InfixApp.left.* == .Lit);

    // Right: InfixApp(2, *, 3)
    const right = top.InfixApp.right.*;
    try std.testing.expect(right == .InfixApp);
    try std.testing.expectEqualStrings("*", right.InfixApp.op.name);
}

test "infix: left associativity — 1 + 2 + 3 parses as (1 + 2) + 3" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "x = 1 + 2 + 3");

    // Top: InfixApp(InfixApp(1, +, 2), +, 3)
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("+", top.InfixApp.op.name);

    // Right: literal 3
    try std.testing.expect(top.InfixApp.right.* == .Lit);

    // Left: InfixApp(1, +, 2)
    const left = top.InfixApp.left.*;
    try std.testing.expect(left == .InfixApp);
    try std.testing.expectEqualStrings("+", left.InfixApp.op.name);
}

test "infix: right associativity — a ++ b ++ c parses as a ++ (b ++ c)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "x = a ++ b ++ c");

    // Top: InfixApp(a, ++, InfixApp(b, ++, c))
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("++", top.InfixApp.op.name);

    // Left: Var "a"
    try std.testing.expect(top.InfixApp.left.* == .Var);

    // Right: InfixApp(b, ++, c)
    const right = top.InfixApp.right.*;
    try std.testing.expect(right == .InfixApp);
    try std.testing.expectEqualStrings("++", right.InfixApp.op.name);
}

test "infix: mixed precedence — 1 + 2 * 3 + 4 parses as (1 + (2 * 3)) + 4" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "x = 1 + 2 * 3 + 4");

    // Top: InfixApp(InfixApp(1, +, InfixApp(2, *, 3)), +, 4)
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("+", top.InfixApp.op.name);

    // Right: literal 4
    try std.testing.expect(top.InfixApp.right.* == .Lit);

    // Left: InfixApp(1, +, InfixApp(2, *, 3))
    const left = top.InfixApp.left.*;
    try std.testing.expect(left == .InfixApp);
    try std.testing.expectEqualStrings("+", left.InfixApp.op.name);
    try std.testing.expect(left.InfixApp.right.* == .InfixApp);
    try std.testing.expectEqualStrings("*", left.InfixApp.right.InfixApp.op.name);
}

test "infix: function application binds tighter — f x + g y" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "z = f x + g y");

    // Top: InfixApp(App(f, x), +, App(g, y))
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("+", top.InfixApp.op.name);

    // Left: App(f, x)
    try std.testing.expect(top.InfixApp.left.* == .App);

    // Right: App(g, y)
    try std.testing.expect(top.InfixApp.right.* == .App);
}

test "infix: dollar has lowest precedence — f $ x + y" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "z = f $ x + y");

    // Top: InfixApp(f, $, InfixApp(x, +, y))
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("$", top.InfixApp.op.name);

    // Left: Var "f"
    try std.testing.expect(top.InfixApp.left.* == .Var);

    // Right: InfixApp(x, +, y)
    const right = top.InfixApp.right.*;
    try std.testing.expect(right == .InfixApp);
    try std.testing.expectEqualStrings("+", right.InfixApp.op.name);
}

test "infix: negation as prefix — -x binds as Negate" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "z = -x");

    // Top: Negate(Var "x")
    try std.testing.expect(top == .Negate);
    try std.testing.expect(top.Negate.* == .Var);
}

test "infix: unknown operator defaults to infixl 9" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "z = a <+> b");

    // Top: InfixApp(a, <+>, b)
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("<+>", top.InfixApp.op.name);
}

test "infix: parenthesized subexpression — (1 + 2) * 3" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "x = (1 + 2) * 3");

    // Top: InfixApp(Paren(InfixApp(1, +, 2)), *, 3)
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("*", top.InfixApp.op.name);

    // Left: Paren
    try std.testing.expect(top.InfixApp.left.* == .Paren);
    // Inside paren: InfixApp(1, +, 2)
    const inner = top.InfixApp.left.Paren.*;
    try std.testing.expect(inner == .InfixApp);
    try std.testing.expectEqualStrings("+", inner.InfixApp.op.name);
}

test "infix: exponentiation is right-assoc prec 8 — 2 ^ 3 ^ 4" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "x = 2 ^ 3 ^ 4");

    // Top: InfixApp(2, ^, InfixApp(3, ^, 4)) — right-assoc
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("^", top.InfixApp.op.name);
    try std.testing.expect(top.InfixApp.left.* == .Lit);
    const right = top.InfixApp.right.*;
    try std.testing.expect(right == .InfixApp);
    try std.testing.expectEqualStrings("^", right.InfixApp.op.name);
}

test "infix: exponentiation binds tighter than multiply — 2 * 3 ^ 4" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const top = try parseTestExpr(&arena, "x = 2 * 3 ^ 4");

    // Top: InfixApp(2, *, InfixApp(3, ^, 4))
    try std.testing.expect(top == .InfixApp);
    try std.testing.expectEqualStrings("*", top.InfixApp.op.name);
    try std.testing.expect(top.InfixApp.left.* == .Lit);
    const right = top.InfixApp.right.*;
    try std.testing.expect(right == .InfixApp);
    try std.testing.expectEqualStrings("^", right.InfixApp.op.name);
}

// ── Type expression tests (Issue #32) ───────────────────────────────────

/// Helper function to parse a type from a simple signature
fn parseTestType(allocator: std.mem.Allocator, signature: []const u8) !ast_mod.Type {
    var lexer: Lexer = undefined;
    var layout: LayoutProcessor = undefined;
    var diags: DiagnosticCollector = undefined;
    var parser = initTestParser(allocator, signature, &lexer, &layout, &diags);
    defer parser.deinit();
    defer layout.deinit();
    defer diags.deinit(allocator);

    const module = try parser.parseModule();
    if (module.declarations.len == 0)
        return error.UnexpectedToken;

    const decl = module.declarations[0];
    if (decl != .TypeSig)
        return error.UnexpectedToken;

    return decl.TypeSig.type;
}

test "type: type variable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: a");
    try std.testing.expect(ty == .Var);
    try std.testing.expectEqualStrings("a", ty.Var);
}

test "type: type constructor" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Int");
    try std.testing.expect(ty == .Con);
    try std.testing.expectEqualStrings("Int", ty.Con.name);
}

test "type: qualified type constructor" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Data.Map.Map");
    try std.testing.expect(ty == .Con);
    // For now, qualified names are stored as a single conid token (the full name)
    // Future work could split this into module_name and name components
    try std.testing.expectEqualStrings("Data.Map.Map", ty.Con.name);
}

test "type: type application" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Maybe Int");
    try std.testing.expect(ty == .App);
    try std.testing.expectEqual(2, ty.App.len);
    try std.testing.expect(ty.App[0].* == .Con);
    try std.testing.expectEqualStrings("Maybe", ty.App[0].Con.name);
    try std.testing.expect(ty.App[1].* == .Con);
    try std.testing.expectEqualStrings("Int", ty.App[1].Con.name);
}

test "type: type application with multiple args" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Either String Int");
    try std.testing.expect(ty == .App);
    try std.testing.expectEqual(3, ty.App.len);
}

test "type: nested type application" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Maybe [Int]");
    try std.testing.expect(ty == .App);
    try std.testing.expectEqual(2, ty.App.len);
    try std.testing.expect(ty.App[0].* == .Con);
    try std.testing.expectEqualStrings("Maybe", ty.App[0].Con.name);
    try std.testing.expect(ty.App[1].* == .List);
}

test "type: simple function type" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Int -> String");
    try std.testing.expect(ty == .Fun);
    try std.testing.expectEqual(2, ty.Fun.len);
    try std.testing.expect(ty.Fun[0].* == .Con);
    try std.testing.expectEqualStrings("Int", ty.Fun[0].Con.name);
    try std.testing.expect(ty.Fun[1].* == .Con);
    try std.testing.expectEqualStrings("String", ty.Fun[1].Con.name);
}

test "type: multi-argument function (right-associative)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Int -> Int -> Int");
    try std.testing.expect(ty == .Fun);
    // Int -> (Int -> Int) is right-associative, so 2 elements at top level
    try std.testing.expectEqual(2, ty.Fun.len);
    try std.testing.expect(ty.Fun[0].* == .Con);
    try std.testing.expectEqualStrings("Int", ty.Fun[0].Con.name);
    try std.testing.expect(ty.Fun[1].* == .Fun);
    try std.testing.expectEqual(2, ty.Fun[1].Fun.len);
}

test "type: unit type" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: ()");
    try std.testing.expect(ty == .Tuple);
    try std.testing.expectEqual(0, ty.Tuple.len);
}

test "type: tuple type" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: (Int, String)");
    try std.testing.expect(ty == .Tuple);
    try std.testing.expectEqual(2, ty.Tuple.len);
    try std.testing.expect(ty.Tuple[0].* == .Con);
    try std.testing.expectEqualStrings("Int", ty.Tuple[0].Con.name);
    try std.testing.expect(ty.Tuple[1].* == .Con);
    try std.testing.expectEqualStrings("String", ty.Tuple[1].Con.name);
}

test "type: triple tuple" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: (Int, String, Bool)");
    try std.testing.expect(ty == .Tuple);
    try std.testing.expectEqual(3, ty.Tuple.len);
}

test "type: list type" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: [Int]");
    try std.testing.expect(ty == .List);
    try std.testing.expect(ty.List.* == .Con);
    try std.testing.expectEqualStrings("Int", ty.List.Con.name);
}

test "type: nested list type" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: [[Int]]");
    try std.testing.expect(ty == .List);
    try std.testing.expect(ty.List.* == .List);
}

test "type: parenthesized type" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: (Maybe Int)");
    try std.testing.expect(ty == .Paren);
    try std.testing.expect(ty.Paren.* == .App);
}

test "type: forall quantification" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: forall a. a -> a");
    try std.testing.expect(ty == .Forall);
    try std.testing.expectEqual(1, ty.Forall.tyvars.len);
    try std.testing.expectEqualStrings("a", ty.Forall.tyvars[0]);
    try std.testing.expect(ty.Forall.type.* == .Fun);
}

test "type: forall with multiple type variables" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: forall a b. a -> b -> a");
    try std.testing.expect(ty == .Forall);
    try std.testing.expectEqual(2, ty.Forall.tyvars.len);
    try std.testing.expectEqualStrings("a", ty.Forall.tyvars[0]);
    try std.testing.expectEqualStrings("b", ty.Forall.tyvars[1]);
}

test "type: type context with single constraint" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Eq a => a -> a");
    try std.testing.expect(ty == .Forall);
    try std.testing.expect(ty.Forall.context != null);
    const ctx = ty.Forall.context.?;
    try std.testing.expectEqual(1, ctx.constraints.len);
    try std.testing.expectEqualStrings("Eq", ctx.constraints[0].class_name);
    try std.testing.expectEqual(1, ctx.constraints[0].types.len);
    try std.testing.expect(ctx.constraints[0].types[0] == .Var);
}

test "type: type context with multiple constraints" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: (Eq a, Show a) => a -> String");
    try std.testing.expect(ty == .Forall);
    try std.testing.expect(ty.Forall.context != null);
    const ctx = ty.Forall.context.?;
    try std.testing.expectEqual(2, ctx.constraints.len);
    try std.testing.expectEqualStrings("Eq", ctx.constraints[0].class_name);
    try std.testing.expectEqualStrings("Show", ctx.constraints[1].class_name);
}

test "type: type context with forall" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: forall a. Eq a => a -> a");
    try std.testing.expect(ty == .Forall);
    try std.testing.expectEqual(1, ty.Forall.tyvars.len);
    try std.testing.expect(ty.Forall.context != null);
}

test "type: complex type: forall with context and nested types" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: forall m a. (Monad m) => m a -> m a");
    try std.testing.expect(ty == .Forall);
    try std.testing.expectEqual(2, ty.Forall.tyvars.len);
    try std.testing.expect(ty.Forall.context != null);

    const ctx = ty.Forall.context.?;
    try std.testing.expectEqual(1, ctx.constraints.len);
    try std.testing.expectEqualStrings("Monad", ctx.constraints[0].class_name);

    // Inner type: m a -> m a
    const inner = ty.Forall.type.*;
    try std.testing.expect(inner == .Fun);
    try std.testing.expectEqual(2, inner.Fun.len);
}

test "type: constraint with type application" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const ty = try parseTestType(arena.allocator(), "foo :: Functor f => f a -> b");
    try std.testing.expect(ty == .Forall);
    try std.testing.expect(ty.Forall.context != null);
    const ctx = ty.Forall.context.?;
    try std.testing.expectEqual(1, ctx.constraints.len);
    try std.testing.expectEqualStrings("Functor", ctx.constraints[0].class_name);
    // Constraint is "Functor f", so types[0] is a type variable
    try std.testing.expect(ctx.constraints[0].types[0] == .Var);
    try std.testing.expectEqualStrings("f", ctx.constraints[0].types[0].Var);
    // The main type is a function type: f a -> b
    try std.testing.expect(ty.Forall.type.* == .Fun);
}

// ── Expression tests (Issue #30) ───────────────────────────────────────────

test "expr: lambda with single parameter" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = \\y -> y + 1");
    try std.testing.expect(expr == .Lambda);
    try std.testing.expectEqual(1, expr.Lambda.patterns.len);
    try std.testing.expectEqualStrings("y", expr.Lambda.patterns[0].Var.name);
    try std.testing.expect(expr.Lambda.body.* == .InfixApp);
}

test "expr: lambda with multiple parameters" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = \\a b c -> a + b + c");
    try std.testing.expect(expr == .Lambda);
    try std.testing.expectEqual(3, expr.Lambda.patterns.len);
    try std.testing.expectEqualStrings("a", expr.Lambda.patterns[0].Var.name);
    try std.testing.expectEqualStrings("b", expr.Lambda.patterns[1].Var.name);
    try std.testing.expectEqualStrings("c", expr.Lambda.patterns[2].Var.name);
}

test "expr: if then else" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = if True then 1 else 0");
    try std.testing.expect(expr == .If);
    try std.testing.expect(expr.If.condition.* == .Var);
    try std.testing.expect(expr.If.then_expr.* == .Lit);
    try std.testing.expect(expr.If.else_expr.* == .Lit);
}

test "expr: do notation with binding" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = do { y <- action; return y }");
    try std.testing.expect(expr == .Do);
    try std.testing.expectEqual(2, expr.Do.len);
    try std.testing.expect(expr.Do[0] == .Generator);
    const gen_pat = expr.Do[0].Generator.pat;
    try std.testing.expect(gen_pat == .Var);
    try std.testing.expectEqualStrings("y", gen_pat.Var.name);
}

test "expr: tuple expression" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = (1, 2, 3)");
    try std.testing.expect(expr == .Tuple);
    try std.testing.expectEqual(3, expr.Tuple.len);
}

test "expr: tuple with trailing comma" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = (1, 2, )");
    try std.testing.expect(expr == .Tuple);
    try std.testing.expectEqual(2, expr.Tuple.len);
}

test "expr: list literal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = [1, 2, 3]");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(3, expr.List.len);
}

test "expr: empty list" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = []");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(0, expr.List.len);
}

test "expr: list with trailing comma" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = [1, 2, 3, ]");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(3, expr.List.len);
}

test "expr: list single element" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = [42]");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(1, expr.List.len);
    try std.testing.expect(expr.List[0] == .Lit);
    try std.testing.expect(expr.List[0].Lit.Int.value == 42);
}

test "expr: list with string literals" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = [\"a\", \"b\", \"c\"]");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(3, expr.List.len);
    try std.testing.expect(expr.List[0] == .Lit);
    try std.testing.expectEqualStrings("a", expr.List[0].Lit.String.value);
}

test "expr: list with variables" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = [Just x, Nothing, Just y]");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(3, expr.List.len);
}

test "expr: nested lists" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = [[1, 2], [3, 4]]");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(2, expr.List.len);
    try std.testing.expect(expr.List[0] == .List);
    try std.testing.expectEqual(2, expr.List[0].List.len);
}

test "expr: nested lists with trailing commas" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const expr = try parseTestExpr(&arena, "x = [[1, 2, ], [3, 4, ]]");
    try std.testing.expect(expr == .List);
    try std.testing.expectEqual(2, expr.List.len);
    try std.testing.expect(expr.List[0] == .List);
    try std.testing.expectEqual(2, expr.List[0].List.len);
}

// ── Class, Instance, Deriving, GADT tests (Issue #33) ────────────────────

/// Helper: parse a module from source text
fn parseTestModule(allocator: std.mem.Allocator, source: []const u8) !ast_mod.Module {
    var lexer = Lexer.init(allocator, source, 1);
    var layout = LayoutProcessor.init(allocator, &lexer);
    var diags = DiagnosticCollector.init();
    var parser = Parser.init(allocator, &layout, &diags) catch |err| switch (err) {
        error.OutOfMemory => @panic("OOM in parseTestModule"),
        error.UnexpectedToken, error.UnexpectedEOF, error.InvalidSyntax => @panic("parse error in parseTestModule"),
    };
    return try parser.parseModule();
}

test "decl: class declaration without context" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mod = try parseTestModule(allocator,
        \\module M where
        \\class Eq a where
        \\  (==) :: a -> a -> Bool
    );
    try std.testing.expectEqual(1, mod.declarations.len);
    try std.testing.expect(mod.declarations[0] == .Class);

    const class_decl = mod.declarations[0].Class;
    try std.testing.expectEqualStrings("Eq", class_decl.class_name);
    try std.testing.expectEqual(1, class_decl.tyvars.len);
    try std.testing.expectEqualStrings("a", class_decl.tyvars[0]);
    try std.testing.expectEqual(1, class_decl.methods.len);
    try std.testing.expectEqualStrings("==", class_decl.methods[0].name);
    try std.testing.expect(class_decl.context == null);
}

test "decl: class declaration with context" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mod = try parseTestModule(allocator,
        \\module M where
        \\class (Eq a) => Ord a where
        \\  (<) :: a -> a -> Bool
    );
    try std.testing.expectEqual(1, mod.declarations.len);
    try std.testing.expect(mod.declarations[0] == .Class);

    const class_decl = mod.declarations[0].Class;
    try std.testing.expectEqualStrings("Ord", class_decl.class_name);
    try std.testing.expectEqual(1, class_decl.tyvars.len);
    try std.testing.expect(class_decl.context != null);

    const ctx = class_decl.context.?;
    try std.testing.expectEqual(1, ctx.constraints.len);
    try std.testing.expectEqualStrings("Eq", ctx.constraints[0].class_name);
    try std.testing.expectEqual(1, ctx.constraints[0].types.len);
}

test "decl: class with default implementation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Default implementations are separate equations in the class body,
    // not inlined after the type signature.
    const mod = try parseTestModule(allocator,
        \\module M where
        \\class Container f where
        \\  toList :: f a -> [a]
        \\  size :: f a -> Int
        \\  size c = length (toList c)
    );
    try std.testing.expectEqual(1, mod.declarations.len);

    const class_decl = mod.declarations[0].Class;
    try std.testing.expectEqual(2, class_decl.methods.len);
    try std.testing.expectEqualStrings("toList", class_decl.methods[0].name);
    try std.testing.expect(class_decl.methods[0].default_implementation == null);
    try std.testing.expectEqualStrings("size", class_decl.methods[1].name);
    try std.testing.expect(class_decl.methods[1].default_implementation != null);
    const impl = class_decl.methods[1].default_implementation.?;
    try std.testing.expectEqual(1, impl.patterns.len); // pattern: c
    try std.testing.expect(impl.rhs == .UnGuarded);
}

test "decl: instance declaration" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Note: Using a simple helper for now since operator LHS parsing (== patterns = expr)
    // is not yet implemented in parseValueDecl
    const mod = try parseTestModule(allocator,
        \\module M where
        \\instance Eq Bool where
        \\  eqTrue True = True
        \\  eqFalse False = True
        \\  eqFalse _ = False
    );
    try std.testing.expectEqual(1, mod.declarations.len);
    try std.testing.expect(mod.declarations[0] == .Instance);

    const inst_decl = mod.declarations[0].Instance;
    try std.testing.expect(inst_decl.context == null);
    try std.testing.expectEqual(3, inst_decl.bindings.len);
}

test "decl: instance with context" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mod = try parseTestModule(allocator,
        \\module M where
        \\instance (Eq a) => Eq [a] where
        \\  [] == [] = True
    );
    try std.testing.expectEqual(1, mod.declarations.len);

    const inst_decl = mod.declarations[0].Instance;
    try std.testing.expect(inst_decl.context != null);
    const ctx = inst_decl.context.?;
    try std.testing.expectEqual(1, ctx.constraints.len);
    try std.testing.expectEqualStrings("Eq", ctx.constraints[0].class_name);
}

test "decl: deriving clause with single class" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mod = try parseTestModule(allocator, "module M where data Maybe a = Nothing | Just a deriving Show");
    try std.testing.expectEqual(1, mod.declarations.len);
    try std.testing.expect(mod.declarations[0] == .Data);

    const data_decl = mod.declarations[0].Data;
    try std.testing.expectEqualStrings("Maybe", data_decl.name);
    try std.testing.expectEqual(1, data_decl.tyvars.len);
    try std.testing.expectEqual(2, data_decl.constructors.len);
    try std.testing.expectEqual(1, data_decl.deriving.len);
    try std.testing.expectEqualStrings("Show", data_decl.deriving[0]);
}

test "decl: deriving clause with multiple classes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mod = try parseTestModule(allocator, "module M where data X = X deriving (Eq, Show, Ord)");
    try std.testing.expectEqual(1, mod.declarations.len);

    const data_decl = mod.declarations[0].Data;
    try std.testing.expectEqual(3, data_decl.deriving.len);
    try std.testing.expectEqualStrings("Eq", data_decl.deriving[0]);
    try std.testing.expectEqualStrings("Show", data_decl.deriving[1]);
    try std.testing.expectEqualStrings("Ord", data_decl.deriving[2]);
}

test "decl: GADT-style data declaration" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mod = try parseTestModule(allocator,
        \\module M where
        \\data Expr a where
        \\  Lit :: Int -> Expr Int
        \\  Add :: Expr Int -> Expr Int -> Expr Int
    );
    try std.testing.expectEqual(1, mod.declarations.len);
    try std.testing.expect(mod.declarations[0] == .Data);

    const data_decl = mod.declarations[0].Data;
    try std.testing.expectEqualStrings("Expr", data_decl.name);
    try std.testing.expectEqual(1, data_decl.tyvars.len);
    try std.testing.expectEqualStrings("a", data_decl.tyvars[0]);
    try std.testing.expectEqual(2, data_decl.constructors.len);

    // Check GADT constructors
    try std.testing.expectEqualStrings("Lit", data_decl.constructors[0].name);
    try std.testing.expect(data_decl.constructors[0].gadt_type != null);
    try std.testing.expect(data_decl.constructors[1].gadt_type != null);
}

test "decl: newtype with deriving" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mod = try parseTestModule(allocator, "module M where newtype Age = Age Int deriving (Eq, Show)");
    try std.testing.expectEqual(1, mod.declarations.len);
    try std.testing.expect(mod.declarations[0] == .Newtype);

    const newtype_decl = mod.declarations[0].Newtype;
    try std.testing.expectEqualStrings("Age", newtype_decl.name);
    try std.testing.expectEqual(0, newtype_decl.tyvars.len);
    try std.testing.expect(newtype_decl.constructor.fields[0].Plain == .Con);
    try std.testing.expectEqualStrings("Int", newtype_decl.constructor.fields[0].Plain.Con.name);
    try std.testing.expectEqual(2, newtype_decl.deriving.len);
}

test "decl: multiple declarations in module" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    // Using single-line explicit-brace syntax to test multiple declarations
    const mod = try parseTestModule(allocator,
        \\module M where
        \\class Eq a where { (==) :: a -> a -> Bool }
        \\data Bool = True | False deriving Eq
        \\instance Eq Bool where { eqBool _ = False }
    );
    try std.testing.expectEqual(3, mod.declarations.len);
    try std.testing.expect(mod.declarations[0] == .Class);
    try std.testing.expect(mod.declarations[1] == .Data);
    try std.testing.expect(mod.declarations[2] == .Instance);
}

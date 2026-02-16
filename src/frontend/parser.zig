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
        if (try self.check(.dcolon)) {
            _ = try self.advance(); // consume ::
            const ty = try self.parseType();
            return .{ .TypeSig = .{
                .names = try self.allocSlice([]const u8, &.{name}),
                .type = ty,
                .span = self.spanFrom(start),
            } };
        }

        // Function binding: name [patterns] = expr [where ...]
        // or guarded: name [patterns] | guard = expr
        var patterns: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
        while (true) {
            const pat = try self.tryParseAtomicPattern() orelse break;
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

        // Constructors
        var constructors: std.ArrayListUnmanaged(ast_mod.ConDecl) = .empty;
        if (try self.match(.equals) != null) {
            const first = try self.parseConDecl();
            try constructors.append(self.allocator, first);
            while (try self.match(.pipe) != null) {
                const con = try self.parseConDecl();
                try constructors.append(self.allocator, con);
            }
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

    // ── Class declaration (minimal) ────────────────────────────────────

    fn parseClassDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_class)).span;

        const context: ?ast_mod.Context = null;
        // Try to detect context: Foo a => ...
        // Simplified: if we see ConId varid => then it's a context
        const saved_len = self.lookahead.items.len;
        _ = saved_len;
        // For now, no context parsing — just class name and tyvars
        const name_tok = try self.expect(.conid);

        var tyvars: std.ArrayListUnmanaged([]const u8) = .empty;
        while (try self.check(.varid)) {
            const tv = try self.advance();
            try tyvars.append(self.allocator, tv.token.varid);
        }

        var methods: std.ArrayListUnmanaged(ast_mod.ClassMethod) = .empty;
        if (try self.match(.kw_where) != null) {
            _ = try self.expectOpenBrace();
            while (true) {
                if (try self.checkCloseBrace()) break;
                if (try self.atEnd()) break;

                // Parse method signatures: name :: Type
                if (try self.check(.varid)) {
                    const method_name = try self.advance();
                    _ = try self.expect(.dcolon);
                    const ty = try self.parseType();
                    try methods.append(self.allocator, .{
                        .name = method_name.token.varid,
                        .type = ty,
                        .default_implementation = null,
                    });
                }
                while (try self.matchSemi()) {}
            }
            _ = try self.expectCloseBrace();
        }

        return .{ .Class = .{
            .context = context,
            .class_name = name_tok.token.conid,
            .tyvars = try tyvars.toOwnedSlice(self.allocator),
            .methods = try methods.toOwnedSlice(self.allocator),
            .span = self.spanFrom(start),
        } };
    }

    // ── Instance declaration (minimal) ─────────────────────────────────

    fn parseInstanceDecl(self: *Parser) ParseError!?ast_mod.Decl {
        const start = (try self.expect(.kw_instance)).span;
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
            .context = null,
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

        // Parse operator names
        var ops: std.ArrayListUnmanaged([]const u8) = .empty;
        while (true) {
            const tag = try self.peekTag();
            if (tag == .varsym) {
                const op = try self.advance();
                try ops.append(self.allocator, op.token.varsym);
            } else if (tag == .consym) {
                const op = try self.advance();
                try ops.append(self.allocator, op.token.consym);
            } else if (tag == .varid) {
                // backtick operator: `mod`
                const op = try self.advance();
                try ops.append(self.allocator, op.token.varid);
            } else {
                break;
            }
            if (try self.match(.comma) == null) break;
        }

        // FixityDecl is not a Decl variant, so skip for now
        // TODO: Add FixityDecl to Decl union or handle separately
        _ = start;
        _ = fixity;
        self.allocator.free(try ops.toOwnedSlice(self.allocator));
        return null;
    }

    // ── Minimal type parsing ───────────────────────────────────────────
    // (Full type parsing is issue #32; this is enough for declarations)

    fn parseType(self: *Parser) ParseError!ast_mod.Type {
        const ty = try self.parseTypeApp();

        // Function arrow: a -> b -> c
        if (try self.check(.arrow_right)) {
            var parts: std.ArrayListUnmanaged(*const ast_mod.Type) = .empty;
            const first = try self.allocNode(ast_mod.Type, ty);
            try parts.append(self.allocator, first);
            while (try self.match(.arrow_right) != null) {
                const next = try self.parseTypeApp();
                try parts.append(self.allocator, try self.allocNode(ast_mod.Type, next));
            }
            return .{ .Fun = try parts.toOwnedSlice(self.allocator) };
        }

        return ty;
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

    // ── Minimal expression parsing ─────────────────────────────────────
    // (Full expression parsing is issue #30; this is enough for bindings)

    fn parseExpr(self: *Parser) ParseError!ast_mod.Expr {
        return try self.parseExprApp();
    }

    fn parseExprApp(self: *Parser) ParseError!ast_mod.Expr {
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
                // Unit: ()
                if (try self.check(.close_paren)) {
                    _ = try self.advance();
                    return .{ .Tuple = &.{} };
                }
                const inner = try self.parseExpr();
                _ = try self.expect(.close_paren);
                return .{ .Paren = try self.allocNode(ast_mod.Expr, inner) };
            },
            .open_bracket => {
                _ = try self.advance();
                if (try self.check(.close_bracket)) {
                    _ = try self.advance();
                    return .{ .List = &.{} };
                }
                var items: std.ArrayListUnmanaged(ast_mod.Expr) = .empty;
                const first = try self.parseExpr();
                try items.append(self.allocator, first);
                while (try self.match(.comma) != null) {
                    const item = try self.parseExpr();
                    try items.append(self.allocator, item);
                }
                _ = try self.expect(.close_bracket);
                return .{ .List = try items.toOwnedSlice(self.allocator) };
            },
            .minus => {
                _ = try self.advance();
                const inner = try self.parseAtomicExpr();
                return .{ .Negate = try self.allocNode(ast_mod.Expr, inner) };
            },
            else => return null,
        }
    }

    // ── Pattern parsing ─────────────────────────────────────────────────

    /// Main entry point for pattern parsing.
    /// Handles: as-patterns, negation, infix constructors, and atomic patterns.
    pub fn parsePattern(self: *Parser) ParseError!ast_mod.Pattern {
        const start = try self.currentSpan();

        // Handle negated pattern: -x, -5, -Just 5
        if (try self.check(.minus)) {
            _ = try self.advance();
            const pat = try self.parsePattern();
            return .{ .Negate = try self.allocNode(ast_mod.Pattern, pat) };
        }

        const pat = try self.parseAtomicPattern();

        // Handle as-pattern: xs@(x:rest)
        if (try self.check(.at)) {
            _ = try self.advance();
            const right_pat = try self.parsePattern();
            // Get the variable name from the left pattern (must be a varid)
            const name = switch (pat) {
                .Var => |n| n,
                else => {
                    try self.emitErrorMsg(start, "as-pattern requires a variable name on the left of @");
                    return error.InvalidSyntax;
                },
            };
            return .{ .AsPar = .{
                .name = name,
                .pat = try self.allocNode(ast_mod.Pattern, right_pat),
            } };
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
            .varid,
            .conid,
            .underscore,
            .lit_integer,
            .lit_char,
            .lit_string,
            .minus,
            .open_paren,
            .open_bracket => true,
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
        return .{ .Var = tok.token.varid };
    }

    /// Parse constructor pattern: Just x, Nothing, True
    fn parseConPattern(self: *Parser) ParseError!ast_mod.Pattern {
        const tok = try self.expect(.conid);

        // Try to parse constructor arguments
        var args: std.ArrayListUnmanaged(ast_mod.Pattern) = .empty;
        defer args.deinit(self.allocator);

        while (try self.isPatternStart()) {
            // For atomic patterns after conid, parse directly
            // But we need to be careful not to parse infix constructors here
            // Since we're left-associative, parse atomic patterns only
            const arg = try self.parseAtomicPattern();
            try args.append(self.allocator, arg);
        }

        const args_slice = try self.allocSlice(ast_mod.Pattern, args.items);
        return .{ .Con = .{
            .name = .{ .name = tok.token.conid, .span = tok.span },
            .args = args_slice,
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
        _ = try self.expect(.open_paren);

        // Check for unit pattern: ()
        if (try self.check(.close_paren)) {
            _ = try self.advance();
            return .{ .Tuple = &.{} };
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

            _ = try self.expect(.close_paren);
            return .{ .Tuple = try self.allocSlice(ast_mod.Pattern, patterns.items) };
        }

        // Single parenthesized pattern: (Just x)
        _ = try self.expect(.close_paren);
        return .{ .Paren = try self.allocNode(ast_mod.Pattern, first) };
    }

    /// Parse list pattern: [], [x, y], [x:xs]
    fn parseListPattern(self: *Parser) ParseError!ast_mod.Pattern {
        _ = try self.expect(.open_bracket);

        // Check for empty list: []
        if (try self.check(.close_bracket)) {
            _ = try self.advance();
            return .{ .List = &.{} };
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

        _ = try self.expect(.close_bracket);
        return .{ .List = try self.allocSlice(ast_mod.Pattern, patterns.items) };
    }

    /// Legacy function for backward compatibility. Tries to parse an atomic pattern.
    /// Used for function arguments in value declarations.
    fn tryParseAtomicPattern(self: *Parser) ParseError!?ast_mod.Pattern {
        if (try self.isPatternStart()) {
            return try self.parseAtomicPattern();
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

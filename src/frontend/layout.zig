const std = @import("std");
const lexer_mod = @import("lexer.zig");
const span_mod = @import("../diagnostics/span.zig");
const Lexer = lexer_mod.Lexer;
const Token = lexer_mod.Token;
const LocatedToken = lexer_mod.LocatedToken;

/// The keyword that opened a layout context.
/// Used to correctly scope the `in` keyword: it closes exactly the innermost
/// `let` context and any implicit contexts nested inside it, but not outer
/// `where`, `do`, or `of` contexts.
///
/// Haskell 2010 §10.3 rule L5: L (in : ts) (m:ms) = } : L (in : ts) ms  if m /= 0
/// This rule closes implicit contexts one-by-one until a 0 (explicit) is found.
/// However, a well-formed program never has `in` inside `where`/`do`/`of` without
/// first having matched a `let`.  We track the opener so we stop closing at the
/// first non-`let` boundary, preventing `in` from consuming outer layout blocks.
pub const ContextKind = enum {
    /// Opened by `where`, `do`, or `of`.  Not closed by `in`.
    block,
    /// Opened by `let`.  Closed by `in`.
    let_binding,
    /// Explicit brace `{`.  Never auto-closed.
    explicit,
};

const Context = struct {
    column: usize,
    kind: ContextKind,
};

/// Implements the Haskell 2010 layout rule (Report section 2.7 and 10.3).
/// This component sits between the Lexer and the Parser.
pub const LayoutProcessor = struct {
    allocator: std.mem.Allocator,
    lexer: *Lexer,
    // Layout context stack.  Each entry records the column and the keyword that
    // opened the context.  column = 0 in an explicit context is redundant but
    // kept for clarity; use kind == .explicit to test.
    stack: std.ArrayListUnmanaged(Context),
    // Queue of tokens to be returned before pulling from the lexer.
    pending: std.ArrayListUnmanaged(LocatedToken),
    // Flag set when a layout-triggering keyword (where, let, do, of) is encountered.
    layout_pending: bool,
    // The keyword that triggered the pending layout context (so we know its kind).
    pending_kind: ContextKind,
    // Buffer for a token that needs to be re-processed.
    peeked_token: ?LocatedToken,
    // The very first token of the module.
    first_token: bool,
    // Set to true when a new context is pushed, to avoid a semicolon before the first token.
    context_just_opened: bool,

    pub fn init(allocator: std.mem.Allocator, lexer: *Lexer) LayoutProcessor {
        return .{
            .allocator = allocator,
            .lexer = lexer,
            .stack = .empty,
            .pending = .empty,
            .peeked_token = null,
            .layout_pending = false,
            .pending_kind = .block,
            .first_token = true,
            .context_just_opened = false,
        };
    }

    pub fn deinit(self: *LayoutProcessor) void {
        for (self.pending.items) |tok| {
            tok.token.deinit(self.allocator);
        }
        if (self.peeked_token) |tok| {
            tok.token.deinit(self.allocator);
        }
        self.stack.deinit(self.allocator);
        self.pending.deinit(self.allocator);
    }

    pub fn nextToken(self: *LayoutProcessor) !LocatedToken {
        if (self.pending.items.len > 0) {
            const p = self.pending.orderedRemove(0);
            // Layout-triggering keywords in the pending queue still need to
            // set `layout_pending` so the next token opens a new context.
            if (self.isLayoutKeyword(p.token)) {
                self.layout_pending = true;
                self.pending_kind = if (p.token == .kw_let) .let_binding else .block;
            }
            return p;
        }

        const tok = if (self.peeked_token) |t| t: {
            self.peeked_token = null;
            break :t t;
        } else self.lexer.nextToken();

        // 3. Handle EOF.
        if (tok.token == .eof) {
            return self.handleEOF(tok);
        }

        // 4. Handle Module-level layout.
        if (self.first_token) {
            self.first_token = false;
            if (tok.token != .kw_module and tok.token != .open_brace) {
                try self.pushContext(.{ .column = tok.span.start.column, .kind = .block });
                self.peeked_token = tok;
                return LocatedToken.init(.v_open_brace, tok.span);
            }
        }

        // 5. Explicit braces (Section 10.3, case 2 & 3).
        if (tok.token == .open_brace) {
            self.layout_pending = false;
            try self.pushContext(.{ .column = 0, .kind = .explicit });
            return tok;
        }
        if (tok.token == .close_brace) {
            if (self.peekContext()) |ctx| {
                if (ctx.kind == .explicit) {
                    _ = self.popContext();
                    return tok;
                }
            }
            // If we see '}' but the top of stack is not explicit, it might be a parse error
            // or an implicit context closure handled via the '<' rule of Section 10.3.
            // But usually, an explicit '}' must match an explicit '{'.
            return tok;
        }

        // 6. Handle the 'm' rule (new layout context) (Section 10.3, case 4).
        if (self.layout_pending) {
            const kind = self.pending_kind;
            self.layout_pending = false;
            if (tok.token != .open_brace) {
                const n = tok.span.start.column;
                const m = if (self.peekContext()) |ctx| ctx.column else 0;
                if (n > m) {
                    try self.pushContext(.{ .column = n, .kind = kind });
                    self.peeked_token = tok;
                    return LocatedToken.init(.v_open_brace, tok.span);
                } else {
                    // Empty layout block: {n} } then process tok again.
                    // Case 4: L (t : ts) (m : ms) = { : } : L (t : ts) ms  if n <= m
                    try self.pending.append(self.allocator, LocatedToken.init(.v_close_brace, tok.span));
                    self.peeked_token = tok;
                    return LocatedToken.init(.v_open_brace, tok.span);
                }
            }
        }

        // 7. Handle existing layout context BEFORE dispatching keywords
        //    (Haskell 2010 Report §10.3, cases 5 & 6).
        //
        //    This must precede the layout-keyword check (step 8) so that a
        //    layout-triggering keyword at a *lower* indentation level correctly
        //    closes the enclosing implicit context before being returned.
        //    Example:
        //      do          -- opens do-context at col 5
        //        let x = 1 -- opens let-context at col 9
        //        let y = 2  -- 'let' at col 5: must close let-context (v_}) first
        //
        //    `kw_in` is handled specially: it closes contexts eagerly via the
        //    pending queue, so we skip the ordinary column comparison for it.
        if (tok.token != .kw_in) {
            const n = tok.span.start.column;
            while (self.peekContext()) |ctx| {
                if (ctx.kind == .explicit) break; // Explicit context — never auto-closed here
                if (n == ctx.column) {
                    // Same column: insert a virtual semicolon (case 5).
                    if (self.context_just_opened) {
                        // Suppress the semicolon for the very first token in a
                        // freshly-opened context (already handled by push).
                        self.context_just_opened = false;
                        break;
                    }
                    try self.pending.append(self.allocator, tok);
                    return LocatedToken.init(.v_semi, tok.span);
                } else if (n < ctx.column) {
                    // Less indentation: close this context (case 6).
                    _ = self.popContext();
                    self.peeked_token = tok;
                    return LocatedToken.init(.v_close_brace, tok.span);
                } else {
                    break; // n > ctx.column — token is further right; nothing to close
                }
            }

            // Clear the just_opened flag once we are safely past the first token.
            if (self.peekContext()) |ctx| {
                if (n > ctx.column or ctx.kind == .explicit) {
                    self.context_just_opened = false;
                }
            }
        }

        // 8. Handle layout-triggering keywords (§10.3, case 4).
        //    Reached only after any necessary context closures above.
        if (self.isLayoutKeyword(tok.token)) {
            self.layout_pending = true;
            // Record which keyword triggered this context so we can track kind.
            self.pending_kind = if (tok.token == .kw_let) .let_binding else .block;
            return tok;
        }

        // 9. Special case: 'in' keyword closes the innermost implicit `let` context.
        //    Per Haskell 2010 §10.3 rule L5: L (in:ts) (m:ms) = } : L (in:ts) ms  if m /= 0
        //
        //    We scan the stack to find the innermost `let_binding` context and close it
        //    along with any implicit `block` contexts nested inside it.  If no `let_binding`
        //    exists (e.g. explicit `let { } in`), `in` is emitted as-is.
        //
        //    Crucially, we do NOT close outer `block` contexts (from `where`/`do`/`of`) that
        //    are not nested inside the matching `let`.
        if (tok.token == .kw_in) {
            // Find if there's a let_binding context anywhere on the stack.
            const has_let_context = blk: {
                for (self.stack.items) |ctx| {
                    if (ctx.kind == .let_binding) break :blk true;
                }
                break :blk false;
            };
            if (has_let_context) {
                // Close block contexts nested inside the let, then close the let itself.
                while (self.peekContext()) |ctx| {
                    if (ctx.kind == .explicit) break; // explicit { }: stop (shouldn't happen inside let)
                    if (ctx.kind == .let_binding) {
                        // Matching let context — close it and stop.
                        _ = self.popContext();
                        try self.pending.append(self.allocator, LocatedToken.init(.v_close_brace, tok.span));
                        break;
                    }
                    // A block (where/do/of) context nested inside the let bindings: close it.
                    _ = self.popContext();
                    try self.pending.append(self.allocator, LocatedToken.init(.v_close_brace, tok.span));
                }
            }
            if (self.pending.items.len > 0) {
                try self.pending.append(self.allocator, tok);
                return self.pending.orderedRemove(0);
            }
            return tok;
        }

        return tok;
    }

    fn pushContext(self: *LayoutProcessor, ctx: Context) !void {
        try self.stack.append(self.allocator, ctx);
        if (ctx.kind != .explicit) {
            self.context_just_opened = true;
        }
    }

    fn popContext(self: *LayoutProcessor) ?Context {
        if (self.stack.items.len == 0) return null;
        const ctx = self.stack.items[self.stack.items.len - 1];
        self.stack.items.len -= 1;
        return ctx;
    }

    fn peekContext(self: *LayoutProcessor) ?Context {
        if (self.stack.items.len == 0) return null;
        return self.stack.items[self.stack.items.len - 1];
    }

    fn isLayoutKeyword(self: LayoutProcessor, t: Token) bool {
        _ = self;
        return switch (t) {
            .kw_where, .kw_let, .kw_do, .kw_of => true,
            else => false,
        };
    }

    fn handleEOF(self: *LayoutProcessor, eof_tok: LocatedToken) !LocatedToken {
        // Close all implicit contexts upon EOF.
        while (self.peekContext()) |ctx| {
            if (ctx.kind != .explicit) {
                _ = self.popContext();
                try self.pending.append(self.allocator, LocatedToken.init(.v_close_brace, eof_tok.span));
            } else break;
        }

        if (self.pending.items.len > 0) {
            try self.pending.append(self.allocator, eof_tok);
            return self.pending.orderedRemove(0);
        }
        return eof_tok;
    }
};

// ── Tests ─────────────────────────────────────────────────────────────

test "Layout: module-level" {
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator, "main = putStrLn \"hi\"", 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    // L (<m>:ts) (ms) = {n} : L (ts) (n:ms)
    try expectToken(&layout, .v_open_brace);
    try expectToken(&layout, Token{ .varid = "main" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .varid = "putStrLn" });
    try expectToken(&layout, Token{ .lit_string = "hi" });
    try expectToken(&layout, .v_close_brace);
    try expectToken(&layout, .eof);
}

test "Layout: let-in semicolon and closing" {
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator,
        \\main = let x = 1
        \\           y = 2
        \\       in x + y
    , 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace); // Module
    try expectToken(&layout, Token{ .varid = "main" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, .kw_let);
    try expectToken(&layout, .v_open_brace); // Let context
    try expectToken(&layout, Token{ .varid = "x" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 1 });
    try expectToken(&layout, .v_semi);
    try expectToken(&layout, Token{ .varid = "y" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 2 });
    try expectToken(&layout, .v_close_brace);
    try expectToken(&layout, .kw_in);
    try expectToken(&layout, Token{ .varid = "x" });
    try expectToken(&layout, Token{ .varsym = "+" });
    try expectToken(&layout, Token{ .varid = "y" });
    try expectToken(&layout, .v_close_brace);
    try expectToken(&layout, .eof);
}

test "Layout: nested blocks" {
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator,
        \\main = do
        \\  let x = 1
        \\  print x
    , 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace); // Module
    try expectToken(&layout, Token{ .varid = "main" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, .kw_do);
    try expectToken(&layout, .v_open_brace); // do context
    try expectToken(&layout, .kw_let);
    try expectToken(&layout, .v_open_brace); // let context
    try expectToken(&layout, Token{ .varid = "x" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 1 });
    try expectToken(&layout, .v_close_brace); // let closes because 'print' is at col 3 (same as 'let')
    try expectToken(&layout, .v_semi); // 'print' is in 'do' context, same col as 'let'
    try expectToken(&layout, Token{ .varid = "print" });
    try expectToken(&layout, Token{ .varid = "x" });
    try expectToken(&layout, .v_close_brace); // Close do
    try expectToken(&layout, .v_close_brace); // Close module
    try expectToken(&layout, .eof);
}

test "Layout: actual empty block" {
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator,
        \\f = where
        \\x = 1
    , 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace); // Module
    try expectToken(&layout, Token{ .varid = "f" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, .kw_where);
    try expectToken(&layout, .v_open_brace); // where starting
    try expectToken(&layout, .v_close_brace); // 'x' is at col 1, where was at col 5. 1 <= 5, so empty block.
    try expectToken(&layout, .v_semi); // 'x' starts new decl in module context
    try expectToken(&layout, Token{ .varid = "x" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 1 });
    try expectToken(&layout, .v_close_brace); // module
    try expectToken(&layout, .eof);
}

test "Layout: explicit overrides" {
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator, "main = let { x = 1; y = 2 } in x", 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace); // Module
    try expectToken(&layout, Token{ .varid = "main" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, .kw_let);
    try expectToken(&layout, .open_brace);
    try expectToken(&layout, Token{ .varid = "x" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 1 });
    try expectToken(&layout, .semi);
    try expectToken(&layout, Token{ .varid = "y" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 2 });
    try expectToken(&layout, .close_brace);
    try expectToken(&layout, .kw_in);
    try expectToken(&layout, Token{ .varid = "x" });
    try expectToken(&layout, .v_close_brace);
    try expectToken(&layout, .eof);
}

test "Layout: let-in inside where — in does not close where context" {
    // Regression test for the bug where `in` was consuming outer `where`/`do` contexts.
    // Stack during parsing: [module(1), where(5), let(18)]
    // When `in` fires at col 14, it should close ONLY the let(18) context, not where(5).
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator,
        \\w = result
        \\  where
        \\    result = let a = 1
        \\                 b = 2
        \\             in a + b
    , 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace); // Module context
    try expectToken(&layout, Token{ .varid = "w" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .varid = "result" });
    try expectToken(&layout, .kw_where);
    try expectToken(&layout, .v_open_brace); // where context at col 5
    try expectToken(&layout, Token{ .varid = "result" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, .kw_let);
    try expectToken(&layout, .v_open_brace); // let context at col 18
    try expectToken(&layout, Token{ .varid = "a" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 1 });
    try expectToken(&layout, .v_semi); // b at same col 18
    try expectToken(&layout, Token{ .varid = "b" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, Token{ .lit_integer = 2 });
    // 'in' at col 14 < 18: closes let context only (NOT where context)
    try expectToken(&layout, .v_close_brace); // close let context
    try expectToken(&layout, .kw_in);
    try expectToken(&layout, Token{ .varid = "a" });
    try expectToken(&layout, Token{ .varsym = "+" });
    try expectToken(&layout, Token{ .varid = "b" });
    // EOF closes where and module contexts
    try expectToken(&layout, .v_close_brace); // close where context
    try expectToken(&layout, .v_close_brace); // close module context
    try expectToken(&layout, .eof);
}

fn expectToken(layout: *LayoutProcessor, expected: anytype) !void {
    const tok = try layout.nextToken();
    defer tok.token.deinit(layout.allocator);
    const T = @TypeOf(expected);
    if (T == Token) {
        try std.testing.expectEqualDeep(expected, tok.token);
    } else if (T == @TypeOf(.foo)) {
        const tag: std.meta.Tag(Token) = tok.token;
        if (tag != expected) {
            std.debug.print("Expected tag {s}, got {s}\n", .{ @tagName(expected), @tagName(tag) });
            return error.TestExpectedEqual;
        }
    } else {
        const expected_token: Token = expected;
        try std.testing.expectEqualDeep(expected_token, tok.token);
    }
}

const std = @import("std");
const lexer_mod = @import("lexer.zig");
const span_mod = @import("../diagnostics/span.zig");
const Lexer = lexer_mod.Lexer;
const Token = lexer_mod.Token;
const LocatedToken = lexer_mod.LocatedToken;

/// Implements the Haskell 2010 layout rule (Report section 2.7 and 10.3).
/// This component sits between the Lexer and the Parser.
pub const LayoutProcessor = struct {
    allocator: std.mem.Allocator,
    lexer: *Lexer,
    // Indentation stack. Each value is the column of a layout context.
    // 0 represents an explicit context (user-supplied { }).
    stack: std.ArrayListUnmanaged(usize),
    // Queue of tokens to be returned before pulling from the lexer.
    pending: std.ArrayListUnmanaged(LocatedToken),
    // Flag set when a layout-triggering keyword (where, let, do, of) is encountered.
    layout_pending: bool,
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
                try self.push(tok.span.start.column);
                self.peeked_token = tok;
                return LocatedToken.init(.v_open_brace, tok.span);
            }
        }

        // 5. Explicit braces (Section 10.3, case 2 & 3).
        if (tok.token == .open_brace) {
            self.layout_pending = false;
            try self.push(0); // 0 identifies an explicit context
            return tok;
        }
        if (tok.token == .close_brace) {
            if (self.peek()) |col| {
                if (col == 0) {
                    _ = self.pop();
                    return tok;
                }
            }
            // If we see '}' but the top of stack is not 0, it might be a parse error
            // or an implicit context closure handled via the '<' rule of Section 10.3.
            // But usually, an explicit '}' must match an explicit '{'.
            return tok;
        }

        // 6. Handle the 'm' rule (new layout context) (Section 10.3, case 4).
        if (self.layout_pending) {
            self.layout_pending = false;
            if (tok.token != .open_brace) {
                const n = tok.span.start.column;
                const m = self.peek() orelse 0;
                if (n > m) {
                    try self.push(n);
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

        // 7. Handle layout-triggering keywords (Section 10.3, case 4).
        if (self.isLayoutKeyword(tok.token)) {
            self.layout_pending = true;
            return tok;
        }

        // 8. Special case: 'in' keyword.
        if (tok.token == .kw_in) {
            // Pop as long as we have more than one implicit context.
            // This ensures we close contexts started after 'let' but don't close the module context.
            while (self.stack.items.len > 1) {
                if (self.peek() == 0) break; // Explicit context
                _ = self.pop();
                try self.pending.append(self.allocator, LocatedToken.init(.v_close_brace, tok.span));
            }
            if (self.pending.items.len > 0) {
                try self.pending.append(self.allocator, tok);
                return self.pending.orderedRemove(0);
            }
            return tok;
        }

        // 9. Handle existing layout context (Section 10.3, case 5 & 6).
        const n = tok.span.start.column;
        while (self.peek()) |m| {
            if (m == 0) break; // Explicit context
            if (n == m) {
                // Same column: semicolon insertion (Case 5).
                if (self.context_just_opened) {
                    self.context_just_opened = false;
                    break;
                }
                try self.pending.append(self.allocator, tok);
                return LocatedToken.init(.v_semi, tok.span);
            } else if (n < m) {
                // Less indentation: close context (Case 6).
                _ = self.pop();
                self.peeked_token = tok;
                return LocatedToken.init(.v_close_brace, tok.span);
            } else {
                break; // n > m, nothing to do
            }
        }

        // If we reached here without returning, we are returning the original token.
        // Make sure to clear the just_opened flag if we are at the same level.
        if (self.peek()) |m| {
            if (n > m or m == 0) {
                self.context_just_opened = false;
            }
        }

        return tok;
    }

    fn push(self: *LayoutProcessor, col: usize) !void {
        try self.stack.append(self.allocator, col);
        if (col > 0) {
            self.context_just_opened = true;
        }
    }

    fn pop(self: *LayoutProcessor) ?usize {
        if (self.stack.items.len == 0) return null;
        const col = self.stack.items[self.stack.items.len - 1];
        self.stack.items.len -= 1;
        return col;
    }

    fn peek(self: *LayoutProcessor) ?usize {
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
        while (self.peek()) |col| {
            if (col > 0) {
                _ = self.pop();
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

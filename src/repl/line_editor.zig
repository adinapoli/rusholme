//! REPL Line Editor
//!
//! Wraps the replxx C library to provide feature-rich line editing
//! for the native `rhc repl` command:
//!   - Tab completion (REPL commands, in-scope names, filesystem paths)
//!   - Inline hints (ghost text for the first matching candidate)
//!   - Live syntax highlighting of the input line
//!   - Persistent history saved to ~/.rhc/repl_history
//!
//! Native-only: imported exclusively by cli.zig, never compiled into
//! the WASM build target.

const std = @import("std");
const Allocator = std.mem.Allocator;
const Session = @import("session.zig").Session;

const c = @cImport({
    @cInclude("replxx.h");
});

// ── Constants ─────────────────────────────────────────────────────────

const max_history_entries: c_int = 1000;

const repl_commands = [_][]const u8{
    ":quit", ":q",   ":type", ":t",
    ":load", ":l",   ":help", ":h",
    ":?",    ":{",   ":}",
};

const haskell_keywords = [_][]const u8{
    "let",      "in",       "where",    "data",
    "case",     "of",       "if",       "then",
    "else",     "do",       "type",     "newtype",
    "class",    "instance", "module",   "import",
    "deriving",
};

// ── Completion type ───────────────────────────────────────────────────

const Completion = struct {
    text: [:0]u8,
    color: c.ReplxxColor,
};

// ── Pure helpers ──────────────────────────────────────────────────────

/// Extract the token being completed from the current input line.
///
/// - If the line starts with ':', and has no space yet, returns the
///   whole ':...' prefix (command completion).
/// - If the line is ':cmd <arg>', returns the argument portion after
///   the last space (file/path completion for :load).
/// - Otherwise, returns the last word after any word-break character.
fn currentToken(line: []const u8) []const u8 {
    if (line.len == 0) return line;

    if (line[0] == ':') {
        const sp = std.mem.indexOfScalar(u8, line, ' ') orelse return line;
        // After the command, complete the argument.
        const rest = line[sp + 1 ..];
        const last_sp = std.mem.lastIndexOfScalar(u8, rest, ' ') orelse return rest;
        return rest[last_sp + 1 ..];
    }

    // Walk backward to find the last word-break character.
    var i = line.len;
    while (i > 0) {
        i -= 1;
        switch (line[i]) {
            ' ', '\t', '(', ')', ',', '[', ']', '.' => return line[i + 1 ..],
            else => {},
        }
    }
    return line;
}

fn isFileCompletionContext(line: []const u8) bool {
    return std.mem.startsWith(u8, line, ":load ") or
        std.mem.startsWith(u8, line, ":l ");
}

/// Build completions for REPL commands matching `prefix`.
fn commandCompletions(
    alloc: Allocator,
    prefix: []const u8,
    out: *std.ArrayListUnmanaged(Completion),
) !void {
    for (repl_commands) |cmd| {
        if (std.mem.startsWith(u8, cmd, prefix)) {
            const text = try alloc.dupeZ(u8, cmd);
            try out.append(alloc, .{ .text = text, .color = c.REPLXX_COLOR_CYAN });
        }
    }
}

/// Build completions for filesystem paths matching `prefix`.
fn fileCompletions(
    alloc: Allocator,
    prefix: []const u8,
    out: *std.ArrayListUnmanaged(Completion),
) !void {
    const dir_end = if (std.mem.lastIndexOfScalar(u8, prefix, '/')) |i| i + 1 else 0;
    const dir_part = if (dir_end > 0) prefix[0..dir_end] else ".";
    const file_part = prefix[dir_end..];

    var dir = std.fs.cwd().openDir(dir_part, .{ .iterate = true }) catch return;
    defer dir.close();

    var it = dir.iterate();
    while (it.next() catch null) |entry| {
        if (!std.mem.startsWith(u8, entry.name, file_part)) continue;
        const text: [:0]u8 = if (dir_end > 0)
            try std.fmt.allocPrintZ(alloc, "{s}{s}", .{ prefix[0..dir_end], entry.name })
        else
            try alloc.dupeZ(u8, entry.name);
        try out.append(alloc, .{ .text = text, .color = c.REPLXX_COLOR_WHITE });
    }
}

/// Build completions for in-scope identifiers matching `prefix`.
fn nameCompletions(
    session: *Session,
    alloc: Allocator,
    prefix: []const u8,
    out: *std.ArrayListUnmanaged(Completion),
) !void {
    var names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer names.deinit(alloc);
    try session.rename_env.scope.collectNames(alloc, &names);

    for (names.items) |name| {
        if (!std.mem.startsWith(u8, name, prefix)) continue;
        const text = try alloc.dupeZ(u8, name);
        const color: c.ReplxxColor = if (name.len > 0 and std.ascii.isUpper(name[0]))
            c.REPLXX_COLOR_BRIGHTGREEN
        else
            c.REPLXX_COLOR_WHITE;
        try out.append(alloc, .{ .text = text, .color = color });
    }
}

/// Dispatch completion candidates based on input context.
pub fn completionsFor(
    session: *Session,
    alloc: Allocator,
    prefix: []const u8,
    line: []const u8,
    out: *std.ArrayListUnmanaged(Completion),
) !void {
    if (line.len > 0 and line[0] == ':') {
        if (isFileCompletionContext(line)) {
            try fileCompletions(alloc, prefix, out);
        } else {
            try commandCompletions(alloc, prefix, out);
        }
    } else {
        try nameCompletions(session, alloc, prefix, out);
    }
}

/// Return the hint suffix (ghost text) for the current input, or null.
/// The returned slice is allocated from `alloc` and null-terminated.
pub fn hintsFor(
    session: *Session,
    alloc: Allocator,
    prefix: []const u8,
    line: []const u8,
) ?[:0]u8 {
    if (prefix.len == 0) return null;

    if (line.len > 0 and line[0] == ':' and !isFileCompletionContext(line)) {
        for (repl_commands) |cmd| {
            if (std.mem.startsWith(u8, cmd, prefix) and cmd.len > prefix.len) {
                return alloc.dupeZ(u8, cmd[prefix.len..]) catch null;
            }
        }
        return null;
    }

    var names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer names.deinit(alloc);
    session.rename_env.scope.collectNames(alloc, &names) catch return null;

    for (names.items) |name| {
        if (std.mem.startsWith(u8, name, prefix) and name.len > prefix.len) {
            return alloc.dupeZ(u8, name[prefix.len..]) catch null;
        }
    }
    return null;
}

/// Colorize `input` by writing a `ReplxxColor` per character into `colors`.
///
/// Uses token-level recognition (no parser):
///   `:command`   → cyan
///   keywords     → blue
///   Constructors → bright green
///   numbers      → yellow
///   strings      → yellow
///   operators    → magenta
///   other        → default
pub fn highlightLine(input: []const u8, colors: []c.ReplxxColor) void {
    @memset(colors, c.REPLXX_COLOR_DEFAULT);
    if (input.len == 0) return;
    const n = @min(input.len, colors.len);

    var i: usize = 0;

    // REPL command: starts with ':'
    if (n > 0 and input[0] == ':') {
        while (i < n and input[i] != ' ') : (i += 1) {
            colors[i] = c.REPLXX_COLOR_CYAN;
        }
    }

    while (i < n) {
        const ch = input[i];

        if (ch == ' ' or ch == '\t') {
            i += 1;
            continue;
        }

        // String literal "..."
        if (ch == '"') {
            const start = i;
            i += 1;
            while (i < n and input[i] != '"') {
                if (input[i] == '\\') i += 1;
                if (i < n) i += 1;
            }
            if (i < n) i += 1; // closing '"'
            @memset(colors[start..i], c.REPLXX_COLOR_YELLOW);
            continue;
        }

        // Number literal
        if (std.ascii.isDigit(ch)) {
            const start = i;
            while (i < n and (std.ascii.isDigit(input[i]) or input[i] == '.')) {
                i += 1;
            }
            @memset(colors[start..i], c.REPLXX_COLOR_YELLOW);
            continue;
        }

        // Identifier or keyword
        if (std.ascii.isAlphabetic(ch) or ch == '_') {
            const start = i;
            while (i < n) : (i += 1) {
                const c2 = input[i];
                if (!std.ascii.isAlphanumeric(c2) and c2 != '_' and c2 != '\'') break;
            }
            const word = input[start..i];
            const color: c.ReplxxColor = if (std.ascii.isUpper(word[0]))
                c.REPLXX_COLOR_BRIGHTGREEN
            else if (isKeyword(word))
                c.REPLXX_COLOR_BLUE
            else
                c.REPLXX_COLOR_DEFAULT;
            @memset(colors[start..i], color);
            continue;
        }

        // Operator characters
        if (isOperatorChar(ch)) {
            const start = i;
            while (i < n and isOperatorChar(input[i])) {
                i += 1;
            }
            @memset(colors[start..i], c.REPLXX_COLOR_MAGENTA);
            continue;
        }

        i += 1;
    }
}

fn isKeyword(word: []const u8) bool {
    for (haskell_keywords) |kw| {
        if (std.mem.eql(u8, word, kw)) return true;
    }
    return false;
}

fn isOperatorChar(ch: u8) bool {
    return switch (ch) {
        '+', '-', '*', '/', '=', '<', '>', '!', '@', '#',
        '$', '%', '^', '&', '|', '~', '?', '\\', ':',
        => true,
        else => false,
    };
}

// ── Callback context ──────────────────────────────────────────────────

/// Passed to all replxx callbacks via the `userData` void pointer.
const CallbackCtx = struct {
    session: *Session,
    allocator: Allocator,
};

// ── C callbacks ───────────────────────────────────────────────────────

fn completionCallback(
    input: [*:0]const u8,
    completions: *c.replxx_completions,
    context_len: *c_int,
    user_data: ?*anyopaque,
) callconv(.C) void {
    const ctx: *CallbackCtx = @ptrCast(@alignCast(user_data orelse return));
    var arena = std.heap.ArenaAllocator.init(ctx.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const line = std.mem.sliceTo(input, 0);
    const prefix = currentToken(line);
    context_len.* = @intCast(prefix.len);

    var candidates: std.ArrayListUnmanaged(Completion) = .empty;
    completionsFor(ctx.session, alloc, prefix, line, &candidates) catch return;

    for (candidates.items) |cand| {
        c.replxx_add_color_completion(completions, @ptrCast(cand.text.ptr), cand.color);
    }
}

fn hintCallback(
    input: [*:0]const u8,
    hints: *c.replxx_hints,
    context_len: *c_int,
    color: *c.ReplxxColor,
    user_data: ?*anyopaque,
) callconv(.C) void {
    const ctx: *CallbackCtx = @ptrCast(@alignCast(user_data orelse return));
    var arena = std.heap.ArenaAllocator.init(ctx.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const line = std.mem.sliceTo(input, 0);
    const prefix = currentToken(line);
    context_len.* = @intCast(prefix.len);
    color.* = c.REPLXX_COLOR_GRAY;

    const hint = hintsFor(ctx.session, alloc, prefix, line) orelse return;
    c.replxx_add_hint(hints, @ptrCast(hint.ptr));
}

fn highlightCallback(
    input: [*:0]const u8,
    colors: [*]c.ReplxxColor,
    size: c_int,
    user_data: ?*anyopaque,
) callconv(.C) void {
    _ = user_data;
    const line = std.mem.sliceTo(input, 0);
    const n: usize = @intCast(size);
    highlightLine(line, colors[0..n]);
}

// ── LineEditor ────────────────────────────────────────────────────────

pub const LineEditor = struct {
    rx: *c.Replxx,
    allocator: Allocator,
    ctx: *CallbackCtx,
    history_path: [:0]u8,

    /// Initialise a line editor.
    ///
    /// Registers completion, hint, and highlighting callbacks.
    /// Loads history from `history_path` if the file exists.
    pub fn init(
        allocator: Allocator,
        session: *Session,
        history_path: []const u8,
    ) !LineEditor {
        const rx = c.replxx_init() orelse return error.ReplxxInitFailed;
        errdefer c.replxx_end(rx);

        const ctx = try allocator.create(CallbackCtx);
        errdefer allocator.destroy(ctx);
        ctx.* = .{ .session = session, .allocator = allocator };

        c.replxx_set_max_history_size(rx, max_history_entries);
        c.replxx_set_unique_history(rx, 1);

        c.replxx_set_completion_callback(rx, completionCallback, ctx);
        c.replxx_set_hint_callback(rx, hintCallback, ctx);
        c.replxx_set_highlighter_callback(rx, highlightCallback, ctx);

        const path_z = try allocator.dupeZ(u8, history_path);
        errdefer allocator.free(path_z);

        // Ignore load errors — file may not exist on first run.
        _ = c.replxx_history_load(rx, path_z);

        return .{
            .rx = rx,
            .allocator = allocator,
            .ctx = ctx,
            .history_path = path_z,
        };
    }

    /// Save history to disk and free resources.
    pub fn deinit(self: *LineEditor) void {
        _ = c.replxx_history_save(self.rx, self.history_path);
        c.replxx_end(self.rx);
        self.allocator.free(self.history_path);
        self.allocator.destroy(self.ctx);
    }

    /// Read the next line from the terminal with full line editing.
    ///
    /// Returns the line as a slice (valid until the next call to `readLine`).
    /// Returns `null` on EOF (Ctrl+D) or read error.
    /// Non-empty lines are automatically added to history.
    pub fn readLine(self: *LineEditor, prompt: []const u8) !?[]const u8 {
        const prompt_z = try self.allocator.dupeZ(u8, prompt);
        defer self.allocator.free(prompt_z);

        const result = c.replxx_input(self.rx, prompt_z);
        if (result == null) return null;

        const line = std.mem.sliceTo(result, 0);
        if (line.len > 0) {
            c.replxx_history_add(self.rx, result);
        }
        return line;
    }
};

// ── Tests ─────────────────────────────────────────────────────────────

test "currentToken: bare identifier extracts last token" {
    try std.testing.expectEqualStrings("fo", currentToken("let fo"));
    try std.testing.expectEqualStrings("x", currentToken("x"));
    try std.testing.expectEqualStrings("", currentToken(""));
}

test "currentToken: colon command returns whole line" {
    try std.testing.expectEqualStrings(":t", currentToken(":t"));
    try std.testing.expectEqualStrings(":quit", currentToken(":quit"));
}

test "currentToken: command argument extracts path prefix" {
    try std.testing.expectEqualStrings("Foo", currentToken(":load Foo"));
    try std.testing.expectEqualStrings("src/", currentToken(":l src/"));
}

test "commandCompletions: prefix ':t' matches ':type' and ':t'" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var out: std.ArrayListUnmanaged(Completion) = .empty;
    try commandCompletions(arena.allocator(), ":t", &out);
    try std.testing.expect(out.items.len == 2);
}

test "commandCompletions: full prefix ':quit' matches only ':quit'" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var out: std.ArrayListUnmanaged(Completion) = .empty;
    try commandCompletions(arena.allocator(), ":quit", &out);
    try std.testing.expect(out.items.len == 1);
    try std.testing.expectEqualStrings(":quit", out.items[0].text);
}

test "highlightLine: keyword 'let' is blue" {
    const input = "let x = 42";
    var colors: [input.len]c.ReplxxColor = undefined;
    highlightLine(input, &colors);
    try std.testing.expectEqual(c.REPLXX_COLOR_BLUE, colors[0]);
    try std.testing.expectEqual(c.REPLXX_COLOR_BLUE, colors[1]);
    try std.testing.expectEqual(c.REPLXX_COLOR_BLUE, colors[2]);
}

test "highlightLine: number literal is yellow" {
    const input = "42";
    var colors: [input.len]c.ReplxxColor = undefined;
    highlightLine(input, &colors);
    try std.testing.expectEqual(c.REPLXX_COLOR_YELLOW, colors[0]);
    try std.testing.expectEqual(c.REPLXX_COLOR_YELLOW, colors[1]);
}

test "highlightLine: constructor is bright green" {
    const input = "Just";
    var colors: [input.len]c.ReplxxColor = undefined;
    highlightLine(input, &colors);
    try std.testing.expectEqual(c.REPLXX_COLOR_BRIGHTGREEN, colors[0]);
}

test "highlightLine: repl command is cyan" {
    const input = ":type";
    var colors: [input.len]c.ReplxxColor = undefined;
    highlightLine(input, &colors);
    try std.testing.expectEqual(c.REPLXX_COLOR_CYAN, colors[0]);
}

test "highlightLine: operator '->' is magenta" {
    const input = "->";
    var colors: [input.len]c.ReplxxColor = undefined;
    highlightLine(input, &colors);
    try std.testing.expectEqual(c.REPLXX_COLOR_MAGENTA, colors[0]);
    try std.testing.expectEqual(c.REPLXX_COLOR_MAGENTA, colors[1]);
}

test "highlightLine: string literal is yellow" {
    const input = "\"hello\"";
    var colors: [input.len]c.ReplxxColor = undefined;
    highlightLine(input, &colors);
    for (colors) |col| {
        try std.testing.expectEqual(c.REPLXX_COLOR_YELLOW, col);
    }
}

//! REPL CLI — interactive read-eval-print loop.
//!
//! Provides the `rhc repl` command: a line-oriented REPL that reads
//! Haskell expressions from stdin, compiles them through the full
//! Rusholme pipeline, executes via LLVM JIT, and prints the result.
//!
//! Line editing is provided by the replxx C library (via LineEditor),
//! offering tab completion, inline hints, syntax highlighting, and
//! persistent history at ~/.rhc/repl_history (issue #76).
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");
const Allocator = std.mem.Allocator;
const Io = std.Io;
const Dir = Io.Dir;
const File = Io.File;
const FileId = @import("../diagnostics/span.zig").FileId;

const Session = @import("session.zig").Session;
const typequery = @import("typequery.zig");
const Diagnostic = @import("../diagnostics/diagnostic.zig").Diagnostic;
const protocol_mod = @import("protocol.zig");
const Status = protocol_mod.Status;
const server_mod = @import("server.zig");
const ReplServer = server_mod.ReplServer;
const evaluate = protocol_mod.evaluate;
const TerminalRenderer = @import("../diagnostics/terminal.zig").TerminalRenderer;
const pipeline_mod = @import("pipeline.zig");
const translateSpan = pipeline_mod.translateSpan;
const LineEditor = @import("line_editor.zig").LineEditor;

const InputMode = enum {
    normal,
    multiline,
};

// ── History path ──────────────────────────────────────────────────────

/// Return the absolute path to the REPL history file: ~/.rhc/repl_history.
///
/// Creates ~/.rhc/ if it does not exist.
/// The caller owns the returned slice (allocated with `allocator`).
fn historyFilePath(io: Io, allocator: Allocator) ![]const u8 {
    const home_ptr = std.c.getenv("HOME") orelse return error.NoHomeDir;
    const home = std.mem.sliceTo(home_ptr, 0);
    const dir_path = try std.fs.path.join(allocator, &.{ home, ".rhc" });
    defer allocator.free(dir_path);

    try Dir.cwd().createDirPath(io, dir_path);

    return std.fs.path.join(allocator, &.{ home, ".rhc", "repl_history" });
}

// ── Server Mode ─────────────────────────────────────────────────────

/// Run the REPL in server mode (JSON-RPC protocol).
///
/// Reads JSON-RPC requests from stdin one line at a time,
/// processes them via a Session, and writes responses to stdout.
pub fn runServer(allocator: Allocator, io: Io) !void {
    var server = try ReplServer.init(allocator, io);
    defer server.deinit();

    try server.run();
}

// ── REPL loop ─────────────────────────────────────────────────────────

/// Run the interactive REPL.
///
/// Attempts to initialise a LineEditor (replxx) for tab completion,
/// inline hints, syntax highlighting, and persistent history.
/// Falls back to `runSimple` when not on a TTY or replxx fails to init.
pub fn run(allocator: Allocator, io: Io) !void {
    // Use an arena allocator for the session lifetime. The typechecker's
    // initBuiltins allocates type structures that outlive the session's
    // deinit — an arena ensures bulk cleanup on exit.
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, io) catch {
        try writeStderr(io, "Failed to initialise REPL session.\n");
        return;
    };
    defer session.deinit();

    try printBanner(io);

    // Obtain the history file path, then try to initialise the line editor.
    // Both steps are allowed to fail (no TTY, no HOME, etc.) — fall back
    // to plain stdin reading if either does.
    const hist_path = historyFilePath(io, alloc) catch null;
    var editor: ?LineEditor = if (hist_path) |hp|
        LineEditor.init(alloc, io, &session, hp) catch null
    else
        null;
    defer if (editor) |*ed| ed.deinit();

    if (editor == null) {
        return runSimple(alloc, io, &session);
    }
    const ed = &editor.?;

    // Main loop: read a line via replxx, evaluate, print result.
    var mode: InputMode = .normal;
    var multiline_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer multiline_buf.deinit(alloc);

    while (true) {
        const prompt = switch (mode) {
            .normal => "rusholme> ",
            .multiline => "rusholme| ",
        };

        // readLine passes the prompt to replxx; null means EOF (Ctrl+D).
        const line = (ed.readLine(prompt) catch null) orelse {
            if (mode == .multiline) {
                multiline_buf.clearRetainingCapacity();
                mode = .normal;
            }
            try writeStdout(io, "\n");
            break;
        };

        if (line.len == 0) continue;

        // ── Multiline mode handling ───────────────────────────────
        if (mode == .multiline) {
            const trimmed = std.mem.trim(u8, line, " \t\r");

            // :} closes the block and evaluates.
            if (std.mem.eql(u8, trimmed, ":}")) {
                const input = multiline_buf.items;
                defer multiline_buf.clearRetainingCapacity();
                mode = .normal;

                if (input.len == 0) continue;

                const result = evaluate(alloc, &session, input) catch |err| {
                    try printError(io, err);
                    continue;
                };
                if (result.status == .success) {
                    try writeStdout(io, result.value);
                    try writeStdout(io, "\n");
                } else if (result.status == .failed) {
                    renderDiagnostics(io, alloc, &session, result.diagnostics);
                }
                continue;
            }

            // :quit / :q exits even from multiline mode.
            if (std.mem.eql(u8, trimmed, ":quit") or std.mem.eql(u8, trimmed, ":q")) {
                multiline_buf.clearRetainingCapacity();
                mode = .normal;
                break;
            }

            // Otherwise, accumulate the line.
            try multiline_buf.appendSlice(alloc, line);
            try multiline_buf.append(alloc, '\n');
            continue;
        }

        // ── Normal mode ───────────────────────────────────────────

        // Check for REPL commands (leading ':').
        if (line[0] == ':') {
            const cmd = std.mem.trim(u8, line[1..], " \t\r");

            // :{ enters multiline mode.
            if (std.mem.eql(u8, cmd, "{")) {
                mode = .multiline;
                continue;
            }

            const should_continue = handleCommand(io, line, alloc, &session);
            if (!should_continue) break;
            continue;
        }

        // Evaluate the input using Protocol.
        const result = evaluate(alloc, &session, line) catch |err| {
            try printError(io, err);
            continue;
        };

        if (result.status == .success) {
            try writeStdout(io, result.value);
            try writeStdout(io, "\n");
        } else if (result.status == .failed) {
            renderDiagnostics(io, alloc, &session, result.diagnostics);
        }
        // .silent: no output for declarations
    }
}

/// Fallback REPL loop used when LineEditor cannot be initialised.
///
/// Reads lines from raw stdin with no editing, completion, or history.
/// Shares the same session and multiline-block logic as `run`.
fn runSimple(alloc: Allocator, io: Io, session: *Session) !void {
    var line_buf: [4096]u8 = undefined;
    var mode: InputMode = .normal;
    var multiline_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer multiline_buf.deinit(alloc);

    while (true) {
        const prompt = switch (mode) {
            .normal => "rusholme> ",
            .multiline => "rusholme| ",
        };
        try writeStdout(io, prompt);

        const line = readLineRaw(io, &line_buf) catch {
            if (mode == .multiline) {
                multiline_buf.clearRetainingCapacity();
                mode = .normal;
            }
            try writeStdout(io, "\n");
            break;
        };

        if (line.len == 0) continue;

        // ── Multiline mode handling ───────────────────────────────
        if (mode == .multiline) {
            const trimmed = std.mem.trim(u8, line, " \t\r");

            if (std.mem.eql(u8, trimmed, ":}")) {
                const input = multiline_buf.items;
                defer multiline_buf.clearRetainingCapacity();
                mode = .normal;

                if (input.len == 0) continue;

                const result = evaluate(alloc, session, input) catch |err| {
                    try printError(io, err);
                    continue;
                };
                if (result.status == .success) {
                    try writeStdout(io, result.value);
                    try writeStdout(io, "\n");
                } else if (result.status == .failed) {
                    renderDiagnostics(io, alloc, session, result.diagnostics);
                }
                continue;
            }

            if (std.mem.eql(u8, trimmed, ":quit") or std.mem.eql(u8, trimmed, ":q")) {
                multiline_buf.clearRetainingCapacity();
                mode = .normal;
                break;
            }

            try multiline_buf.appendSlice(alloc, line);
            try multiline_buf.append(alloc, '\n');
            continue;
        }

        // ── Normal mode ───────────────────────────────────────────

        if (line[0] == ':') {
            const cmd = std.mem.trim(u8, line[1..], " \t\r");

            if (std.mem.eql(u8, cmd, "{")) {
                mode = .multiline;
                continue;
            }

            const should_continue = handleCommand(io, line, alloc, session);
            if (!should_continue) break;
            continue;
        }

        const result = evaluate(alloc, session, line) catch |err| {
            try printError(io, err);
            continue;
        };

        if (result.status == .success) {
            try writeStdout(io, result.value);
            try writeStdout(io, "\n");
        } else if (result.status == .failed) {
            renderDiagnostics(io, alloc, session, result.diagnostics);
        }
    }
}

// ── Line reading ──────────────────────────────────────────────────────

/// Read a line from stdin into the provided buffer.
/// Returns the line contents without the trailing newline.
/// Returns error on EOF or read failure.
fn readLineRaw(io: Io, buf: []u8) ![]const u8 {
    var pos: usize = 0;
    var stdin_buf: [1]u8 = undefined;
    var stdin_rdr = File.stdin().reader(io, &stdin_buf);
    const rdr = &stdin_rdr.interface;

    while (pos < buf.len) {
        var byte_buf: [1]u8 = undefined;
        rdr.readSliceAll(&byte_buf) catch |err| {
            if (pos > 0) return buf[0..pos];
            return err;
        };
        const byte = byte_buf[0];
        if (byte == '\n') return buf[0..pos];
        buf[pos] = byte;
        pos += 1;
    }
    // Line too long — return what we have.
    return buf[0..pos];
}

// ── Command handling ──────────────────────────────────────────────────

/// Handle a REPL command (line starting with ':').
/// Returns true if the REPL should continue, false to exit.
fn handleCommand(io: Io, line: []const u8, allocator: Allocator, session: *Session) bool {
    const cmd = std.mem.trim(u8, line[1..], " \t\r");

    // Parse the command: first word is the command, rest is arguments
    var words = std.mem.splitScalar(u8, cmd, ' ');
    const command = words.first();

    // quit / q
    if (std.mem.eql(u8, command, "quit") or std.mem.eql(u8, command, "q")) {
        return false;
    }

    // type <expr> / t <expr>
    if (std.mem.eql(u8, command, "type") or std.mem.eql(u8, command, "t")) {
        const expr = std.mem.trim(u8, words.rest(), " \t");

        if (expr.len == 0) {
            writeStdout(io, "Usage: :type <expr> or :t <expr>\n") catch {};
            return true;
        }

        const result = typequery.typeOf(allocator, session, expr) catch |err| {
            // Diagnostics have been saved to session.last_diagnostics by typeOf.
            // Render them if any exist.
            if (session.last_diagnostics.items.len > 0) {
                renderDiagnostics(io, allocator, session, session.last_diagnostics.items);
            } else {
                // No diagnostics - show a generic error message
                switch (err) {
                    error.OutOfMemory => {
                        writeStdout(io, "Error: Out of memory during type query\n") catch {};
                    },
                    error.CompilationFailed => {
                        writeStdout(io, "Error: Failed to compile expression for type query\n") catch {};
                    },
                    else => {
                        var buf: [256]u8 = undefined;
                        const msg = std.fmt.bufPrint(&buf, "Error: Type query failed ({s})\n", .{@errorName(err)}) catch "Error: Type query failed\n";
                        writeStdout(io, msg) catch {};
                    },
                }
            }
            return true;
        };
        defer allocator.free(result.display);

        if (result.diags.len > 0) {
            renderDiagnostics(io, allocator, session, result.diags);
        } else {
            writeStdout(io, result.display) catch {};
            writeStdout(io, "\n") catch {};
        }
        return true;
    }

    // load <file> / l <file>
    if (std.mem.eql(u8, command, "load") or std.mem.eql(u8, command, "l")) {
        const raw_path = std.mem.trim(u8, words.rest(), " \t");

        if (raw_path.len == 0) {
            writeStdout(io, "Usage: :load <path> or :l <path>\n") catch {};
            return true;
        }

        const path = expandTilde(raw_path, allocator) orelse raw_path;
        defer if (path.ptr != raw_path.ptr) allocator.free(path);
        loadFile(io, path, allocator, session);
        return true;
    }

    // help / h / ?
    if (std.mem.eql(u8, command, "help") or std.mem.eql(u8, command, "h") or std.mem.eql(u8, command, "?")) {
        printHelp(io) catch {};
        return true;
    }

    writeStdout(io, "Unknown command. Type :help for available commands.\n") catch {};
    return true;
}

// ── File loading ──────────────────────────────────────────────────────

/// Load a Haskell source file from disk and evaluate its contents
/// within the current REPL session.
fn loadFile(io: Io, path: []const u8, allocator: Allocator, session: *Session) void {
    const file = Dir.openFile(.cwd(), io, path, .{}) catch |err| {
        writeStderr(io, "Cannot open file '") catch {};
        writeStderr(io, path) catch {};
        writeStderr(io, "': ") catch {};
        var err_buf: [128]u8 = undefined;
        const err_msg = std.fmt.bufPrint(&err_buf, "{}\n", .{err}) catch "unknown error\n";
        writeStderr(io, err_msg) catch {};
        return;
    };
    defer file.close(io);

    var read_buf: [8192]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    const contents = rdr.interface.allocRemaining(allocator, .limited(1024 * 1024)) catch |err| {
        writeStderr(io, "Failed to read file '") catch {};
        writeStderr(io, path) catch {};
        writeStderr(io, "': ") catch {};
        var err_buf: [128]u8 = undefined;
        const err_msg = std.fmt.bufPrint(&err_buf, "{}\n", .{err}) catch "unknown error\n";
        writeStderr(io, err_msg) catch {};
        return;
    };

    // Strip `module ... where` header if present, since evaluate()
    // wraps input in its own `module ReplInput where` wrapper.
    const body = stripModuleHeader(contents);

    const result = evaluate(allocator, session, body) catch {
        writeStderr(io, "Error loading file\n") catch {};
        return;
    };

    switch (result.status) {
        .success, .silent => {
            writeStdout(io, "Loaded: ") catch {};
            writeStdout(io, path) catch {};
            writeStdout(io, "\n") catch {};
        },
        .failed => {
            renderDiagnostics(io, allocator, session, result.diagnostics);
        },
    }
}

// ── File loading helpers ──────────────────────────────────────────────

/// Expand a leading `~/` to the user's home directory.
/// Returns an allocated string on success, or null if the path doesn't
/// start with `~/` or the HOME environment variable is not set.
fn expandTilde(path: []const u8, allocator: Allocator) ?[]const u8 {
    if (path.len >= 2 and path[0] == '~' and path[1] == '/') {
        const home_ptr = std.c.getenv("HOME") orelse return null;
        const home = std.mem.sliceTo(home_ptr, 0);
        return std.fmt.allocPrint(allocator, "{s}{s}", .{ home, path[1..] }) catch return null;
    }
    return null;
}

/// Strip a `module <Name> where` header line from file contents.
///
/// Haskell source files typically start with `module Foo where` but
/// the REPL wraps input in its own `module ReplInput where`, so we
/// need to remove the file's header to avoid a nested module error.
/// Returns the contents starting after the `where` keyword and its
/// following newline, or the original contents if no header is found.
fn stripModuleHeader(contents: []const u8) []const u8 {
    // Find the first non-whitespace, non-empty line that might contain `module`
    var i: usize = 0;
    while (i < contents.len) {
        // Skip past the current line
        const line_start = i;
        while (i < contents.len and contents[i] != '\n' and contents[i] != '\r') {
            i += 1;
        }

        // Extract the line (without newline)
        const line_end = i;
        const line = contents[line_start..line_end];

        // Trim whitespace from line
        var j: usize = 0;
        while (j < line.len and (line[j] == ' ' or line[j] == '\t')) {
            j += 1;
        }
        const trimmed_line = line[j..];

        // Skip empty lines and comments, check for module keyword
        if (trimmed_line.len > 0 and trimmed_line[0] != '-' and std.mem.startsWith(u8, trimmed_line, "module ")) {
            // Found module line, check for where after it
            const where_keyword = "where";
            if (std.mem.indexOf(u8, trimmed_line, where_keyword)) |where_offset| {
                const after_where = line_start + where_offset + where_keyword.len;
                // Skip past the newline after `where`
                var k = after_where;
                while (k < contents.len and (contents[k] == '\n' or contents[k] == '\r')) {
                    k += 1;
                }
                if (k < contents.len) {
                    return contents[k..];
                }
                return contents[after_where..];
            }
            // Has module but no where - not a valid module header line, return original
            return contents;
        }

        // Skip past newline(s) to next line
        while (i < contents.len and (contents[i] == '\n' or contents[i] == '\r')) {
            i += 1;
        }
    }

    // No module declaration found, return original
    return contents;
}

// ── Output helpers ────────────────────────────────────────────────────

fn printBanner(io: Io) !void {
    try writeStdout(io,
        \\Rusholme REPL v0.1.0
        \\Type :help for available commands, :quit to exit.
        \\
    );
}

fn printHelp(io: Io) !void {
    try writeStdout(io,
        \\Available commands:
        \\  :quit, :q           Exit the REPL
        \\  :type <expr>, :t    Show the type of an expression
        \\  :load <file>, :l    Load a Haskell file into the session
        \\  :{                  Begin multi-line input block
        \\  :}                  End multi-line input block and evaluate
        \\  :help, :h, :?       Show this help message
        \\
    );
}

fn printError(io: Io, err: anytype) !void {
    var buf: [256]u8 = undefined;
    const msg = std.fmt.bufPrint(&buf, "Error: {}\n", .{err}) catch "Error: <formatting failed>\n";
    try writeStderr(io, msg);
}

/// Write to stdout.
fn writeStdout(io: Io, msg: []const u8) !void {
    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    try fw.interface.writeAll(msg);
    try fw.interface.flush();
}

/// Write to stderr.
fn writeStderr(io: Io, msg: []const u8) !void {
    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stderr(), io, &buf);
    try fw.interface.writeAll(msg);
    try fw.interface.flush();
}

/// Render diagnostics to stderr using the TerminalRenderer.
///
/// Translates wrapper-relative spans to user-input-relative coordinates
/// so the rendered output shows the user's code (not the internal module
/// wrapper) with correct caret positioning.
fn renderDiagnostics(io: Io, alloc: Allocator, session: *Session, diagnostics: []const Diagnostic) void {
    var path_lookup = std.AutoHashMap(FileId, []const u8).init(alloc);
    defer path_lookup.deinit();
    path_lookup.put(0, "<repl>") catch return;

    var file_contents = std.AutoHashMap(FileId, []const u8).init(alloc);
    defer file_contents.deinit();
    // Use the raw user input, not the module wrapper source.
    file_contents.put(0, session.last_input) catch return;

    const renderer = TerminalRenderer.init(&path_lookup, &file_contents);

    // Render each diagnostic with translated spans.
    for (diagnostics) |diag| {
        // Translate the span from wrapper-relative to user-input-relative.
        const translated_span = translateSpan(diag.span, session.last_input_kind) orelse diag.span;

        const translated_diag = Diagnostic{
            .severity = diag.severity,
            .code = diag.code,
            .span = translated_span,
            .message = diag.message,
            .notes = diag.notes,
            .payload = diag.payload,
        };

        var out: std.Io.Writer.Allocating = .init(alloc);
        defer out.deinit();

        renderer.render(&out.writer, translated_diag) catch {
            writeStderr(io, "Error: ") catch {};
            writeStderr(io, diag.message) catch {};
            writeStderr(io, "\n") catch {};
            continue;
        };

        const rendered = out.toOwnedSlice() catch {
            writeStderr(io, "Error: ") catch {};
            writeStderr(io, diag.message) catch {};
            writeStderr(io, "\n") catch {};
            continue;
        };
        defer alloc.free(rendered);
        writeStderr(io, rendered) catch {};
    }
}

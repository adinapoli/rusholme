//! REPL CLI — interactive read-eval-print loop.
//!
//! Provides the `rhc repl` command: a line-oriented REPL that reads
//! Haskell expressions from stdin, compiles them through the full
//! Rusholme pipeline, executes via LLVM JIT, and prints the result.
//!
//! Line editing is basic (no history or completion). A proper line
//! editor (e.g. linenoise) is deferred to issue #75.
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");
const Allocator = std.mem.Allocator;
const Io = std.Io;
const Dir = Io.Dir;
const File = Io.File;
const FileId = @import("../diagnostics/span.zig").FileId;

const Session = @import("session.zig").Session;
const Diagnostic = @import("../diagnostics/diagnostic.zig").Diagnostic;
const protocol_mod = @import("protocol.zig");
const Status = protocol_mod.Status;
const evaluate = protocol_mod.evaluate;
const TerminalRenderer = @import("../diagnostics/terminal.zig").TerminalRenderer;
const pipeline_mod = @import("pipeline.zig");
const translateSpan = pipeline_mod.translateSpan;

const InputMode = enum {
    normal,
    multiline,
};

// ── REPL loop ─────────────────────────────────────────────────────────

/// Run the interactive REPL.
///
/// Reads lines from stdin, evaluates each via a Session backed by the
/// LLVM JIT engine, and prints results or diagnostics to stdout/stderr.
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

    // Main loop: read a line, evaluate, print result.
    var line_buf: [4096]u8 = undefined;
    var mode: InputMode = .normal;
    var multiline_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer multiline_buf.deinit(allocator);

    while (true) {
        const prompt = switch (mode) {
            .normal => "rusholme> ",
            .multiline => "rusholme| ",
        };
        try writeStdout(io, prompt);

        const line = readLine(io, &line_buf) catch {
            // EOF or read error — cancel any multiline block and exit.
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
            try multiline_buf.appendSlice(allocator, line);
            try multiline_buf.append(allocator, '\n');
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
            // Fallback error handling (shouldn't be reached if Protocol returns errors)
            try printError(io, err);
            continue;
        };

        // Handle status
        if (result.status == .success) {
            try writeStdout(io, result.value);
            try writeStdout(io, "\n");
        } else if (result.status == .failed) {
            renderDiagnostics(io, alloc, &session, result.diagnostics);
        }
        // .silent: no output for declarations
    }
}

// ── Line reading ──────────────────────────────────────────────────────

/// Read a line from stdin into the provided buffer.
/// Returns the line contents without the trailing newline.
/// Returns error on EOF or read failure.
fn readLine(io: Io, buf: []u8) ![]const u8 {
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

    if (std.mem.eql(u8, cmd, "quit") or std.mem.eql(u8, cmd, "q")) {
        return false;
    }

    if (std.mem.startsWith(u8, cmd, "type ") or std.mem.startsWith(u8, cmd, "t ")) {
        // :type is not yet implemented — tracked in the REPL design doc.
        writeStdout(io, ":type is not yet implemented\n") catch {};
        return true;
    }

    if (std.mem.startsWith(u8, cmd, "load ") or std.mem.startsWith(u8, cmd, "l ")) {
        const path_start: usize = if (std.mem.startsWith(u8, cmd, "load ")) 5 else 2;
        const path = std.mem.trim(u8, cmd[path_start..], " \t");
        loadFile(io, path, allocator, session);
        return true;
    }

    if (std.mem.eql(u8, cmd, "help") or std.mem.eql(u8, cmd, "h") or std.mem.eql(u8, cmd, "?")) {
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

/// Strip a `module <Name> where` header line from file contents.
///
/// Haskell source files typically start with `module Foo where` but
/// the REPL wraps input in its own `module ReplInput where`, so we
/// need to remove the file's header to avoid a nested module error.
/// Returns the contents starting after the `where` keyword and its
/// following newline, or the original contents if no header is found.
fn stripModuleHeader(contents: []const u8) []const u8 {
    // Skip leading whitespace/blank lines.
    var i: usize = 0;
    while (i < contents.len and (contents[i] == ' ' or contents[i] == '\t' or contents[i] == '\n' or contents[i] == '\r')) {
        i += 1;
    }

    // Check for `module` keyword.
    if (!std.mem.startsWith(u8, contents[i..], "module ")) return contents;

    // Find `where` followed by end-of-line or end-of-file.
    if (std.mem.indexOf(u8, contents[i..], "where")) |where_offset| {
        const after_where = i + where_offset + "where".len;
        // Skip past the newline after `where`.
        if (after_where < contents.len and contents[after_where] == '\n') {
            return contents[after_where + 1 ..];
        } else if (after_where < contents.len and contents[after_where] == '\r') {
            const skip = if (after_where + 1 < contents.len and contents[after_where + 1] == '\n')
                after_where + 2
            else
                after_where + 1;
            return contents[skip..];
        }
        return contents[after_where..];
    }

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
        \\  :quit, :q       Exit the REPL
        \\  :type <expr>    Show the type of an expression (not yet implemented)
        \\  :load <file>, :l  Load a Haskell file into the session
        \\  :{              Begin multi-line input block
        \\  :}              End multi-line input block and evaluate
        \\  :help, :h, :?   Show this help message
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

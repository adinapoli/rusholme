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
const File = Io.File;

const Session = @import("session.zig").Session;
const JitEngine = @import("jit_engine.zig").JitEngine;

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
    while (true) {
        try writeStdout(io, "rusholme> ");

        const line = readLine(io, &line_buf) catch {
            // EOF or read error — exit gracefully.
            try writeStdout(io, "\n");
            break;
        };

        if (line.len == 0) continue;

        // Check for REPL commands (leading ':').
        if (line[0] == ':') {
            const should_continue = handleCommand(io, line);
            if (!should_continue) break;
            continue;
        }

        // Evaluate the input.
        const result = session.eval(line) catch |err| {
            try printError(io, err);
            continue;
        };

        try writeStdout(io, result.value);
        try writeStdout(io, "\n");
    }
}

// ── Line reading ──────────────────────────────────────────────────────

/// Read a line from stdin into the provided buffer.
/// Returns the line contents without the trailing newline.
/// Returns error on EOF or read failure.
fn readLine(io: Io, buf: []u8) ![]const u8 {
    var stdin_buf: [1]u8 = undefined;
    var stdin_rdr = File.stdin().reader(io, &stdin_buf);
    const rdr = &stdin_rdr.interface;

    var pos: usize = 0;
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
fn handleCommand(io: Io, line: []const u8) bool {
    const cmd = std.mem.trim(u8, line[1..], " \t\r");

    if (std.mem.eql(u8, cmd, "quit") or std.mem.eql(u8, cmd, "q")) {
        return false;
    }

    if (std.mem.startsWith(u8, cmd, "type ") or std.mem.startsWith(u8, cmd, "t ")) {
        // :type is not yet implemented — tracked in the REPL design doc.
        writeStdout(io, ":type is not yet implemented\n") catch {};
        return true;
    }

    if (std.mem.eql(u8, cmd, "help") or std.mem.eql(u8, cmd, "h") or std.mem.eql(u8, cmd, "?")) {
        printHelp(io) catch {};
        return true;
    }

    writeStdout(io, "Unknown command. Type :help for available commands.\n") catch {};
    return true;
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
        \\  :help, :h, :?   Show this help message
        \\
    );
}

fn printError(io: Io, err: anytype) !void {
    var buf: [256]u8 = undefined;
    const msg = std.fmt.bufPrint(&buf, "Error: {}\n", .{err}) catch "Error: <formatting failed>\n";
    try writeStderr(io, msg);
}

fn writeStdout(io: Io, msg: []const u8) !void {
    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    try fw.interface.writeAll(msg);
    try fw.interface.flush();
}

fn writeStderr(io: Io, msg: []const u8) !void {
    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stderr(), io, &buf);
    try fw.interface.writeAll(msg);
    try fw.interface.flush();
}

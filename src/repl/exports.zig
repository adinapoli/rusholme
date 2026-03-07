//! WebAssembly bridge exports
//!
//! Exports functions that JavaScript can call to interact with the REPL.
//! The session owns the compiler state and evaluates inputs through the
//! full Rusholme pipeline + GRIN tree-walking evaluator.
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");

pub const buffer = @import("buffer.zig");
pub const eval_mod = @import("eval.zig");
const Session = @import("session.zig").Session;
const protocol = @import("protocol.zig");

// ── Global state ──────────────────────────────────────────────────────

/// Page allocator — the only allocator available in WASM without libc.
var page_alloc = std.heap.page_allocator;

/// Long-lived arena for session state that persists across evaluations.
var session_arena: ?std.heap.ArenaAllocator = null;

/// The active REPL session.
var session: ?Session = null;

/// Single-threaded IO backend for WASM. The WASM binary is built as a
/// WASI reactor (no std.process.Init), so we construct our own `std.Io`
/// from a single-threaded `Io.Threaded` instance. IO primops (fd_write
/// etc.) route through WASI syscalls, which the browser's JS shim handles.
var io_backend: std.Io.Threaded = std.Io.Threaded.init_single_threaded;

pub fn main() void {
    // No-op entry point for WASM.
}

// ── Exports ───────────────────────────────────────────────────────────

/// Initialise the REPL session.
///
/// Must be called once before any calls to `repl_evaluate`. Safe to
/// call multiple times (idempotent).
pub export fn repl_init() void {
    if (session != null) return;

    session_arena = std.heap.ArenaAllocator.init(page_alloc);
    const alloc = session_arena.?.allocator();

    session = Session.init(alloc, io_backend.io()) catch {
        _ = writeError("Failed to initialise REPL session");
        return;
    };
}

/// Get the input buffer pointer for JavaScript to write into.
pub export fn repl_get_input_buffer() [*]u8 {
    return buffer.getInputBuffer();
}

/// Get the output buffer pointer for JavaScript to read from.
pub export fn repl_get_output_buffer() [*]u8 {
    return buffer.getOutputBuffer();
}

/// Evaluate a REPL input.
///
/// JavaScript writes the input into the input buffer, then calls this
/// function with the input length. The result (JSON) is written to the
/// output buffer and the result length is returned.
///
/// JSON format:
///   Success:     {"status":"success","value":"<result>"}
///   Declaration: {"status":"success","value":""}
///   Error:       {"status":"error","message":"<description>"}
pub export fn repl_evaluate(length: usize) usize {
    const input_buf = buffer.getInputBuffer();
    if (length > buffer.INPUT_BUFFER_SIZE) return writeError("Input too long");

    const raw_input = input_buf[0..length];

    // Strip multi-line delimiters (:{ ... :}) if present
    const input = eval_mod.stripMultilineDelimiters(raw_input);

    const s = &(session orelse return writeError("Session not initialised — call repl_init() first"));

    const alloc = session_arena.?.allocator();
    const result = protocol.evaluate(alloc, s, input) catch {
        return writeError("Internal error during evaluation");
    };

    return switch (result.status) {
        .success => writeSuccess(result.value),
        .silent => writeSuccess(""),
        .failed => writeError(result.value),
    };
}

// ── Output formatting ─────────────────────────────────────────────────

fn writeSuccess(value: []const u8) usize {
    const output = buffer.getOutputBuffer()[0..buffer.OUTPUT_BUFFER_SIZE];
    const json = std.fmt.bufPrint(output, "{{\"status\":\"success\",\"value\":\"{s}\"}}", .{value}) catch
        return writeError("Output too long");
    return json.len;
}

fn writeError(message: []const u8) usize {
    const output = buffer.getOutputBuffer()[0..buffer.OUTPUT_BUFFER_SIZE];
    const json = std.fmt.bufPrint(output, "{{\"status\":\"error\",\"message\":\"{s}\"}}", .{message}) catch
        return 0;
    return json.len;
}

//! WebAssembly bridge exports
//!
//! Exports functions that JavaScript can call to interact with the REPL.
//! The session owns the compiler state and evaluates inputs through the
//! full Rusholme pipeline + GRIN tree-walking evaluator.
//!
//! Two communication paths share the same ReplServer core:
//!
//!   1. **Shared buffers** (`repl_process_jsonrpc`): JavaScript writes a
//!      JSON-RPC request into the input buffer, calls the export, and
//!      reads the response from the output buffer. Non-blocking — one
//!      request per call. Used by the website.
//!
//!   2. **stdin/stdout** (`repl_server_run`): Blocking loop that reads
//!      JSON-RPC requests from stdin and writes responses to stdout.
//!      Used by `wasmtime run --invoke repl_server_run repl.wasm` for
//!      headless testing.
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");

pub const buffer = @import("buffer.zig");
pub const eval_mod = @import("eval.zig");
const Session = @import("session.zig").Session;
const protocol = @import("protocol.zig");
const JsonRenderer = @import("../diagnostics/json.zig").JsonRenderer;
const FileId = @import("../diagnostics/span.zig").FileId;
const Diagnostic = @import("../diagnostics/diagnostic.zig").Diagnostic;
const pipeline_mod = @import("pipeline.zig");
const translateSpan = pipeline_mod.translateSpan;
const ReplServer = @import("server.zig").ReplServer;

// ── Global state ──────────────────────────────────────────────────────

/// Page allocator — the only allocator available in WASM without libc.
var page_alloc = std.heap.page_allocator;

/// Long-lived arena for session state that persists across evaluations.
var session_arena: ?std.heap.ArenaAllocator = null;

/// The active REPL session (used by the legacy `repl_evaluate` path).
var session: ?Session = null;

/// Single-threaded IO backend for WASM. The WASM binary is built as a
/// WASI reactor (no std.process.Init), so we construct our own `std.Io`
/// from a single-threaded `Io.Threaded` instance. IO primops (fd_write
/// etc.) route through WASI syscalls, which the browser's JS shim handles.
var io_backend: std.Io.Threaded = std.Io.Threaded.init_single_threaded;

/// Server instance shared by `repl_process_jsonrpc` and `repl_server_run`.
var server: ?ReplServer = null;

pub fn main() void {
    // No-op entry point for WASM.
}

// ── Helpers ───────────────────────────────────────────────────────────

/// Lazily initialise the shared `ReplServer` instance.
fn ensureServer() !*ReplServer {
    if (server == null) {
        server = try ReplServer.init(page_alloc, io_backend.io());
    }
    return &server.?;
}

// ── JSON-RPC exports ──────────────────────────────────────────────────

/// Process a single JSON-RPC request through the shared-buffer bridge.
///
/// JavaScript writes a JSON-RPC request into the input buffer, calls
/// this function with the byte length, then reads the response from
/// the output buffer. The return value is the response byte length.
///
/// This is the primary communication path for the website.
pub export fn repl_process_jsonrpc(length: usize) usize {
    const input_buf = buffer.getInputBuffer();
    if (length > buffer.INPUT_BUFFER_SIZE) {
        return writeJsonRpcError(0, -32600, "Request too long");
    }
    const input = input_buf[0..length];

    const s = ensureServer() catch {
        return writeJsonRpcError(0, -32603, "Server initialization failed");
    };

    const response_str = s.processRequestToString(input) catch {
        return writeJsonRpcError(0, -32603, "Internal error");
    };

    const output = buffer.getOutputBuffer()[0..buffer.OUTPUT_BUFFER_SIZE];
    if (response_str.len > output.len) {
        page_alloc.free(response_str);
        return writeJsonRpcError(0, -32603, "Response too long");
    }
    @memcpy(output[0..response_str.len], response_str);
    const len = response_str.len;
    page_alloc.free(response_str);
    return len;
}

/// Run the JSON-RPC server loop on stdin/stdout.
///
/// Blocks until stdin closes or a "shutdown" request is received.
/// Auto-initialises the server on first call.
///
/// Usage: `wasmtime run --invoke repl_server_run repl.wasm`
pub export fn repl_server_run() void {
    const s = ensureServer() catch return;

    s.run() catch {};

    // Clean up after the loop exits.
    s.deinit();
    server = null;
}

// ── Legacy exports (buffer protocol) ──────────────────────────────────
//
// These exports use a custom JSON protocol (`{"status":"success",...}`)
// and are retained for backward compatibility. New code should use
// `repl_process_jsonrpc` instead.

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

/// Evaluate a REPL input (legacy buffer protocol).
///
/// JavaScript writes the input into the input buffer, then calls this
/// function with the input length. The result (JSON) is written to the
/// output buffer and the result length is returned.
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
        .failed => writeErrorWithDiagnostics(alloc, s, result.diagnostics, result.value),
    };
}

// ── Output formatting (legacy protocol) ───────────────────────────────

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

fn writeErrorWithDiagnostics(alloc: std.mem.Allocator, s: *Session, diagnostics: []const Diagnostic, fallback_message: []const u8) usize {
    var path_lookup = std.AutoHashMap(FileId, []const u8).init(alloc);
    defer path_lookup.deinit();
    path_lookup.put(0, "<repl>") catch return writeError(fallback_message);

    const translated = alloc.alloc(Diagnostic, diagnostics.len) catch return writeError(fallback_message);
    for (diagnostics, 0..) |diag, i| {
        translated[i] = .{
            .severity = diag.severity,
            .code = diag.code,
            .span = translateSpan(diag.span, s.last_input_kind) orelse diag.span,
            .message = diag.message,
            .notes = diag.notes,
            .payload = diag.payload,
        };
    }

    const renderer = JsonRenderer.init(alloc, &path_lookup);

    const diag_json = renderer.renderAll(translated) catch
        return writeError(fallback_message);

    const output = buffer.getOutputBuffer()[0..buffer.OUTPUT_BUFFER_SIZE];
    const json = std.fmt.bufPrint(output, "{{\"status\":\"error\",\"message\":\"{s}\",\"diagnostics\":{s}}}", .{ fallback_message, diag_json }) catch
        return writeError(fallback_message);
    return json.len;
}

// ── JSON-RPC error helper ─────────────────────────────────────────────

/// Write a JSON-RPC error response directly to the output buffer.
/// Used by `repl_process_jsonrpc` for early-exit error paths where
/// the ReplServer is not yet available.
fn writeJsonRpcError(id: u32, code: i32, message: []const u8) usize {
    const output = buffer.getOutputBuffer()[0..buffer.OUTPUT_BUFFER_SIZE];
    const json = std.fmt.bufPrint(
        output,
        "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"error\":{{\"code\":{d},\"message\":\"{s}\"}}}}",
        .{ id, code, message },
    ) catch return 0;
    return json.len;
}

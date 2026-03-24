//! REPL Server Mode
//!
//! Provides JSON-RPC 2.0 server interface for the REPL.
//! Read requests line-by-line from stdin, parse as JSON-RPC,
//! handle via Session, and write responses to stdout.
//!
//! The core dispatch logic lives in `processRequestToString`, which
//! is a pure function (input → output string, no IO side effects).
//! This allows the same logic to be used from both the stdin/stdout
//! server loop (`run`) and the WASM shared-buffer bridge
//! (`repl_process_jsonrpc` in exports.zig).
//!
//! Usage: rhc repl --server

const std = @import("std");
const Allocator = std.mem.Allocator;
const log = std.log;
const Io = std.Io;
const File = Io.File;

const Session = @import("session.zig").Session;
const jsonrpc_mod = @import("jsonrpc.zig");
const protocol_mod = @import("protocol.zig");
const ProtocolResult = protocol_mod.ProtocolResult;
const Status = protocol_mod.Status;
const Diagnostic = @import("../diagnostics/diagnostic.zig").Diagnostic;
const JsonRenderer = @import("../diagnostics/json.zig").JsonRenderer;
const FileId = @import("../diagnostics/span.zig").FileId;

// ── ReplServer ────────────────────────────────────────────────────────

/// JSON-RPC server for REPL protocol.
///
/// Reads JSON-RPC requests from stdin one line at a time,
/// processes them via a Session, and writes responses to stdout.
/// Supports graceful shutdown when stdin closes.
pub const ReplServer = struct {
    allocator: Allocator,
    session: Session,
    io: Io,

    /// Set to true when a "shutdown" request has been processed.
    /// The `run()` loop checks this after writing each response.
    should_shutdown: bool = false,

    /// Initialize the server with a Session.
    ///
    /// Creates a new Session instance and prepares the server
    /// for processing JSON-RPC requests from stdin.
    pub fn init(allocator: Allocator, io: Io) !ReplServer {
        var session = try Session.init(allocator, io);
        errdefer session.deinit();

        // Disable show-wrapping: triggers infinite recursion for polymorphic
        // expressions (e.g. `42`) during the fallback-to-bare-expression path.
        // Monomorphic expressions like `True` work fine with show-wrapping.
        // Root cause: likely deepForceVal creating circular references during
        // WASM server's accumulated-defs merging, or pipeline retry logic issue.
        // tracked in: https://github.com/adinapoli/rusholme/issues/627
        session.pipeline.enable_show_wrapping = false;

        return .{
            .allocator = allocator,
            .session = session,
            .io = io,
        };
    }

    /// Clean up the session and release resources.
    pub fn deinit(self: *ReplServer) void {
        self.session.deinit();
    }

    // ── Pure request dispatch ─────────────────────────────────────

    /// Process a single JSON-RPC request and return the response as
    /// an allocated string.  No IO side effects — the caller is
    /// responsible for routing the response to stdout, a shared
    /// buffer, etc.
    ///
    /// The caller must free the returned slice with `self.allocator`.
    pub fn processRequestToString(self: *ReplServer, input: []const u8) ![]const u8 {
        var request = jsonrpc_mod.parseRequest(self.allocator, input) catch {
            return try self.formatErrorStr(0, -32700, "Parse error");
        };
        defer request.deinit();

        const method = request.method;
        const id = request.id;

        if (std.mem.eql(u8, method, "init")) {
            return try self.formatSuccessStr(id, "ok");
        } else if (std.mem.eql(u8, method, "eval")) {
            return try self.dispatchEval(id, request.params);
        } else if (std.mem.eql(u8, method, "type")) {
            return try self.dispatchType(id, request.params);
        } else if (std.mem.eql(u8, method, "shutdown")) {
            self.should_shutdown = true;
            return try self.formatSuccessStr(id, "ok");
        } else {
            return try self.formatErrorStr(id, -32601, "Method not found");
        }
    }

    /// Dispatch an "eval" request, returning the JSON-RPC response string.
    fn dispatchEval(self: *ReplServer, id: u32, params: ?std.json.Value) ![]const u8 {
        const input = try self.extractParamString(params) orelse {
            return try self.formatErrorStr(id, -32602, "Invalid params: expected string expression");
        };
        defer self.allocator.free(input);

        const result = protocol_mod.evaluate(self.allocator, &self.session, input) catch |err| {
            const msg = try std.fmt.allocPrint(self.allocator, "Evaluation failed: {s}", .{@errorName(err)});
            defer self.allocator.free(msg);
            return try self.formatErrorStr(id, -32603, msg);
        };

        return switch (result.status) {
            .success => try self.formatSuccessStr(id, result.value),
            .silent => try self.formatSuccessStr(id, ""),
            .failed => try self.formatErrorWithDiagnosticsStr(id, -32603, result.value, result.diagnostics),
        };
    }

    /// Dispatch a "type" request, returning the JSON-RPC response string.
    fn dispatchType(self: *ReplServer, id: u32, params: ?std.json.Value) ![]const u8 {
        const input = try self.extractParamString(params) orelse {
            return try self.formatErrorStr(id, -32602, "Invalid params: expected string expression");
        };
        defer self.allocator.free(input);

        const result = protocol_mod.typeOf(self.allocator, &self.session, input) catch |err| {
            const msg = try std.fmt.allocPrint(self.allocator, "Type checking failed: {s}", .{@errorName(err)});
            defer self.allocator.free(msg);
            return try self.formatErrorStr(id, -32603, msg);
        };

        return switch (result.status) {
            .success => try self.formatSuccessStr(id, result.value),
            .failed => try self.formatErrorWithDiagnosticsStr(id, -32603, result.value, result.diagnostics),
            // .silent case not applicable for type queries - type always returns a result or error
            .silent => try self.formatErrorStr(id, -32603, "Internal error: silent status from type query"),
        };
    }

    // ── Response formatting (pure, no IO) ─────────────────────────

    /// Format a success JSON-RPC response as an allocated string.
    fn formatSuccessStr(self: *ReplServer, id: u32, value: []const u8) ![]const u8 {
        const response = jsonrpc_mod.Response{
            .jsonrpc = "2.0",
            .id = id,
            .result = std.json.Value{ .string = value },
            .@"error" = null,
            .allocator = self.allocator,
        };
        return try jsonrpc_mod.formatResponse(self.allocator, response);
    }

    /// Format an error JSON-RPC response as an allocated string.
    fn formatErrorStr(self: *ReplServer, id: u32, code: i32, message: []const u8) ![]const u8 {
        const response = jsonrpc_mod.Response{
            .jsonrpc = "2.0",
            .id = id,
            .result = null,
            .@"error" = .{ .code = code, .message = message, .data = null },
            .allocator = self.allocator,
        };
        return try jsonrpc_mod.formatResponse(self.allocator, response);
    }

    /// Format an error JSON-RPC response with structured diagnostics.
    ///
    /// When diagnostics are available, they are rendered as JSON and
    /// included in the error's `data` field so that clients (e.g. the
    /// browser REPL) can display rich, structured error information.
    fn formatErrorWithDiagnosticsStr(
        self: *ReplServer,
        id: u32,
        code: i32,
        message: []const u8,
        diagnostics: []const Diagnostic,
    ) ![]const u8 {
        if (diagnostics.len == 0) {
            return try self.formatErrorStr(id, code, message);
        }

        // Build a path lookup for the JSON renderer.
        var path_lookup = std.AutoHashMap(FileId, []const u8).init(self.allocator);
        defer path_lookup.deinit();
        try path_lookup.put(0, "<repl>");

        const renderer = JsonRenderer.init(self.allocator, &path_lookup);
        const diag_json_str = try renderer.renderAll(diagnostics);
        defer self.allocator.free(diag_json_str);

        // Parse the rendered JSON string into a std.json.Value so it
        // is embedded as structured data, not a double-encoded string.
        var parsed = try std.json.parseFromSlice(
            std.json.Value,
            self.allocator,
            diag_json_str,
            .{},
        );
        defer parsed.deinit();

        // Build a data object: {"diagnostics": [...]}
        var data_obj = std.json.ObjectMap.init(self.allocator);
        try data_obj.put("diagnostics", parsed.value);

        const response = jsonrpc_mod.Response{
            .jsonrpc = "2.0",
            .id = id,
            .result = null,
            .@"error" = .{
                .code = code,
                .message = message,
                .data = .{ .object = data_obj },
            },
            .allocator = self.allocator,
        };
        return try jsonrpc_mod.formatResponse(self.allocator, response);
    }

    // ── IO wrappers ───────────────────────────────────────────────

    /// Process a JSON-RPC request and write the response to stdout.
    ///
    /// Thin IO wrapper around `processRequestToString`.
    pub fn processRequest(self: *ReplServer, input: []const u8) !void {
        const response_str = try self.processRequestToString(input);
        defer self.allocator.free(response_str);

        var stdout_buf: [4096]u8 = undefined;
        var stdout_fw: File.Writer = .init(.stdout(), self.io, &stdout_buf);
        const stdout = &stdout_fw.interface;

        try stdout.writeAll(response_str);
        try stdout.writeAll("\n");
        try stdout.flush();
    }

    /// Main loop: read JSON-RPC requests line by line from stdin.
    ///
    /// Continues processing until stdin closes, a "shutdown" request
    /// is received, or an unrecoverable error occurs.
    /// Each line is expected to be a valid JSON-RPC 2.0 request object.
    pub fn run(self: *ReplServer) !void {
        var line_buffer: [8192]u8 = undefined;
        var stdin_buf: [1]u8 = undefined;
        var stdin_rdr = File.stdin().reader(self.io, &stdin_buf);
        const stdin = &stdin_rdr.interface;

        while (true) {
            const line = readLine(stdin, &line_buffer) catch |err| {
                switch (err) {
                    error.EndOfStream => return,
                    else => {
                        log.err("Failed to read from stdin: {}", .{err});
                        return err;
                    },
                }
            };

            if (line.len == 0) continue;

            self.processRequest(line) catch {
                continue;
            };

            if (self.should_shutdown) return;
        }
    }

    // ── Helpers ───────────────────────────────────────────────────

    /// Extract a string parameter from JSON-RPC params.
    /// Supports both array form `["expr"]` and direct string form `"expr"`.
    fn extractParamString(self: *const ReplServer, params: ?std.json.Value) error{OutOfMemory}!?[]const u8 {
        if (params) |p| {
            switch (p) {
                .array => |arr| {
                    if (arr.items.len > 0) {
                        switch (arr.items[0]) {
                            .string => |s| return try self.allocator.dupe(u8, s),
                            else => return null,
                        }
                    }
                },
                .string => |s| return try self.allocator.dupe(u8, s),
                else => {},
            }
        }
        return null;
    }
};

/// Read a line from stdin into the provided buffer.
/// Returns the line contents without the trailing newline.
/// Returns error on EOF or read failure.
fn readLine(stdin: anytype, buf: []u8) ![]const u8 {
    var pos: usize = 0;
    var byte_buf: [1]u8 = undefined;

    while (pos < buf.len) {
        stdin.readSliceAll(&byte_buf) catch |err| {
            if (pos > 0) return buf[0..pos];
            return err;
        };
        const byte = byte_buf[0];
        if (byte == '\n') return buf[0..pos];
        buf[pos] = byte;
        pos += 1;
    }
    return buf[0..pos];
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "server: ReplServer has expected fields" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const io = testing.io;

    var server = try ReplServer.init(allocator, io);
    defer server.deinit();

    _ = server.allocator;
    _ = server.io;
}

test "server: init and deinit work correctly" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const io = testing.io;

    var server = try ReplServer.init(allocator, io);
    server.deinit();
}

test "server: processRequestToString handles init" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const io = testing.io;

    var server = try ReplServer.init(allocator, io);
    defer server.deinit();

    const response = try server.processRequestToString(
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
    );
    defer allocator.free(response);

    try testing.expect(std.mem.indexOf(u8, response, "\"result\":\"ok\"") != null);
}

test "server: processRequestToString handles eval" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const io = testing.io;

    var server = try ReplServer.init(allocator, io);
    defer server.deinit();

    // Disable show-wrapping: IPC mode can't handle JIT fd 1 writes.
    server.session.pipeline.enable_show_wrapping = false;

    const response = try server.processRequestToString(
        \\{"jsonrpc":"2.0","id":1,"method":"eval","params":["42"]}
    );
    defer allocator.free(response);

    try testing.expect(std.mem.indexOf(u8, response, "\"result\":\"42\"") != null);
}

test "server: processRequestToString handles shutdown" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const io = testing.io;

    var server = try ReplServer.init(allocator, io);
    defer server.deinit();

    try testing.expect(!server.should_shutdown);

    const response = try server.processRequestToString(
        \\{"jsonrpc":"2.0","id":1,"method":"shutdown"}
    );
    defer allocator.free(response);

    try testing.expect(server.should_shutdown);
    try testing.expect(std.mem.indexOf(u8, response, "\"result\":\"ok\"") != null);
}

test "server: processRequestToString handles parse error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const io = testing.io;

    var server = try ReplServer.init(allocator, io);
    defer server.deinit();

    const response = try server.processRequestToString("not json");
    defer allocator.free(response);

    try testing.expect(std.mem.indexOf(u8, response, "\"error\"") != null);
    try testing.expect(std.mem.indexOf(u8, response, "Parse error") != null);
}

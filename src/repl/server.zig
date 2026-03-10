//! REPL Server Mode
//!
//! Provides JSON-RPC 2.0 server interface for the REPL.
//! Read requests line-by-line from stdin, parse as JSON-RPC,
//! handle via Session, and write responses to stdout.
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

    /// Initialize the server with a Session.
    ///
    /// Creates a new Session instance and prepares the server
    /// for processing JSON-RPC requests from stdin.
    pub fn init(allocator: Allocator, io: Io) !ReplServer {
        var session = try Session.init(allocator, io);
        errdefer session.deinit();

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

    /// Handle the init protocol request.
    /// Returns success status indicating the REPL session is ready.
    fn handleInit(self: *ReplServer, id: u32) !void {
        try self.sendSuccessResponseJson(id, std.json.Value{ .string = "ok" });
    }

    /// Handle the eval protocol request.
    /// Evaluates a Haskell expression and returns the result.
    fn handleEval(self: *ReplServer, id: u32, params: ?std.json.Value) !void {
        const input = try self.extractParamString(params) orelse {
            try self.sendErrorResponse(id, -32602, "Invalid params: expected string expression");
            return;
        };
        defer self.allocator.free(input);

        const result = protocol_mod.evaluate(self.allocator, &self.session, input) catch |err| {
            // Error during evaluation - return error with diagnostics
            const msg = try std.fmt.allocPrint(self.allocator, "Evaluation failed: {s}", .{@errorName(err)});
            defer self.allocator.free(msg);
            try self.sendErrorResponse(id, -32603, msg);
            return;
        };

        switch (result.status) {
            .success => {
                try self.sendSuccessResponseJson(id, std.json.Value{ .string = result.value });
            },
            .silent => {
                try self.sendSuccessResponseJson(id, std.json.Value{ .string = "" });
            },
            .failed => {
                // Error result with diagnostics — forward the actual message
                try self.sendErrorResponse(id, -32603, result.value);
            },
        }
    }

    /// Handle the type protocol request.
    /// Type-checks an expression and returns its type.
    /// Note: Type inference is not yet implemented in Session, so this
    /// returns a placeholder for now.
    fn handleType(self: *ReplServer, id: u32, params: ?std.json.Value) !void {
        const input = try self.extractParamString(params) orelse {
            try self.sendErrorResponse(id, -32602, "Invalid params: expected string expression");
            return;
        };
        defer self.allocator.free(input);

        // TODO: Implement type inference in Session and Pipeline
        // For now, return a placeholder indicating type checking is not yet available
        try self.sendErrorResponse(id, -32601, "Type checking not yet implemented - requires type inference support in Session");
    }

    /// Handle the shutdown protocol request.
    /// Sends an OK response and shuts down the server gracefully.
    fn handleShutdown(self: *ReplServer, id: u32) !void {
        try self.sendSuccessResponseJson(id, std.json.Value{ .string = "ok" });
        std.process.exit(0);
    }

    /// Extract a string parameter from JSON-RPC params.
    /// Returns null if params is null, not an array, or the first element is not a string.
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

    /// Send a success JSON-RPC response with a JSON value to stdout.
    fn sendSuccessResponseJson(self: *ReplServer, id: u32, result: std.json.Value) !void {
        var stdout_buf: [4096]u8 = undefined;
        var stdout_fw: File.Writer = .init(.stdout(), self.io, &stdout_buf);
        const stdout = &stdout_fw.interface;

        const response = jsonrpc_mod.Response{
            .jsonrpc = "2.0",
            .id = id,
            .result = result,
            .@"error" = null,
            .allocator = self.allocator,
        };

        const json_str = try jsonrpc_mod.formatResponse(self.allocator, response);
        defer self.allocator.free(json_str);

        try stdout.writeAll(json_str);
        try stdout.writeAll("\n");
        try stdout.flush();
    }

    /// Send an error JSON-RPC response to stdout.
    fn sendErrorResponse(self: *ReplServer, id: ?u32, code: i32, message: []const u8) !void {
        var stdout_buf: [4096]u8 = undefined;
        var stdout_fw: File.Writer = .init(.stdout(), self.io, &stdout_buf);
        const stdout = &stdout_fw.interface;

        const response = jsonrpc_mod.Response{
            .jsonrpc = "2.0",
            .id = id orelse 0,
            .result = null,
            .@"error" = .{ .code = code, .message = message, .data = null },
            .allocator = self.allocator,
        };

        const json_str = try jsonrpc_mod.formatResponse(self.allocator, response);
        defer self.allocator.free(json_str);

        try stdout.writeAll(json_str);
        try stdout.writeAll("\n");
        try stdout.flush();
    }

    /// Main loop: read JSON-RPC requests line by line from stdin.
    ///
    /// Continues processing until stdin closes or an unrecoverable error occurs.
    /// Each line is expected to be a valid JSON-RPC 2.0 request object.
    pub fn run(self: *ReplServer) !void {
        var line_buffer: [8192]u8 = undefined;
        var stdin_buf: [1]u8 = undefined;
        var stdin_rdr = File.stdin().reader(self.io, &stdin_buf);
        const stdin = &stdin_rdr.interface;

        while (true) {
            // Read a line from stdin
            const line = readLine(stdin, &line_buffer) catch |err| {
                switch (err) {
                    error.EndOfStream => {
                        // Graceful shutdown when stdin closes
                        return;
                    },
                    else => {
                        log.err("Failed to read from stdin: {}", .{err});
                        return err;
                    },
                }
            };

            // Skip empty lines
            if (line.len == 0) continue;

            // Process the JSON-RPC request
            self.processRequest(line) catch {
                // Continue processing other requests even if one fails
                continue;
            };
        }
    }

    /// Process a JSON-RPC request input.
    ///
    /// Parses the request into a Request struct, dispatches to the
    /// appropriate handler based on method name, and writes the response
    /// to stdout as a JSON-RPC response.
    pub fn processRequest(self: *ReplServer, input: []const u8) !void {
        // Parse the JSON-RPC request
        var request = jsonrpc_mod.parseRequest(self.allocator, input) catch {
            // Invalid request - send error response
            try self.sendErrorResponse(null, -32700, "Parse error");
            return;
        };
        defer request.deinit();

        // Dispatch based on method
        const method = request.method;
        const id = request.id;

        // Dispatch to appropriate handler
        if (std.mem.eql(u8, method, "init")) {
            try self.handleInit(id);
        } else if (std.mem.eql(u8, method, "eval")) {
            try self.handleEval(id, request.params);
        } else if (std.mem.eql(u8, method, "type")) {
            try self.handleType(id, request.params);
        } else if (std.mem.eql(u8, method, "shutdown")) {
            try self.handleShutdown(id);
        } else {
            // Method not found
            try self.sendErrorResponse(id, -32601, "Method not found");
        }
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
    // Line too long — return what we have.
    return buf[0..pos];
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "server: ReplServer has expected fields" {
    // Session.init → initBuiltins allocates HType trees that TyEnv.deinit
    // does not yet deep-free (tracked pre-existing issue). Use an arena so
    // the leak-detecting allocator sees a clean exit.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const io = testing.io;

    var server = try ReplServer.init(allocator, io);
    defer server.deinit();

    // Verify server has expected allocator and io
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

    // If we got here without panicking, init/deinit worked
}

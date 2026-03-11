> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add JSON-RPC 2.0 server mode to Rusholme REPL that works on both native and WASM backends, enabling systematic debugging, extended test coverage, and multiple frontend implementations.

**Architecture:** JSON-RPC 2.0 protocol over stdin/stdout (line-based JSON). Single binary with dual modes: default interactive mode and `--server` mode. New `ReplServer` and `JsonRpc` modules wrap existing `Session`, `Protocol`, and `JsonRenderer` infrastructure. Minimal changes - preserve existing behavior, add server mode capability.

**Tech Stack:**
- JSON-RPC 2.0 protocol (standard)
- Zig `std.json` (existing)
- Zig's `std.Io` for stdin/stdout
- Existing `Session`, `Protocol`, `JsonRenderer` modules
- `wasmtime` for WASM CLI execution

---

## Chunk 1: JSON-RPC Module

### Task 1: Create JsonRpc Module

**Files:**
- Create: `src/repl/jsonrpc.zig`

- [ ] **Step 1: Write failing test for request parsing**

```zig
test "jsonrpc: parse simple request" {
    const allocator = std.testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"test\"}";
    const result = try JsonRpc.parseRequest(allocator, input);
    try testing.expect(result.status == .@"error" or result.status == .success);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `zig build test -- --test-filter "parse simple" -v`
Expected: FAIL with "use of undeclared identifier 'JsonRpc'"

- [ ] **Step 3: Create JsonRpc module with basic request parsing**

Create `src/repl/jsonrpc.zig`:
```zig
const std = @import("std");

pub const Request = struct {
    jsonrpc: []const u8 = "2.0",
    id: u32,
    method: []const u8,
    params: ?std.json.Value = null,
};

pub const Response = struct {
    jsonrpc: []const u8 = "2.0",
    id: u32,
    result: ?std.json.Value = null,
    @"error": ?Error = null,
};

pub const Error = struct {
    code: i32,
    message: []const u8,
    data: ?[]const u8 = null,
};

pub fn parseRequest(allocator: std.mem.Allocator, input: []const u8) !Request {
    var parser = std.json.Value.init(allocator);
    defer parser.deinit();
    try parser.parse(input, .{});
    
    const root = try parser.root();
    const obj = try parser.root.asObject();
    
    const id = obj.get("id").?.asInteger() orelse return error.InvalidRequest;
    const method = obj.get("method").?.asString() orelse return error.InvalidRequest;
    
    return .{ .id = @intCast(id), .method = method };
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `zig build test -- --test-filter "parse simple" -v`
Expected: PASS

- [ ] **Step 5: Commit**

```bash
git add src/repl/jsonrpc.zig
git commit -m "feat(repl): add JsonRpc module for JSON-RPC 2.0 parsing"
```

### Task 2: Add Response Formatting

- [ ] **Step 6: Write failing test for response formatting**

```zig
test "jsonrpc: format success response" {
    const allocator = std.testing.allocator;
    const response = Response{ .id = 1, .result = std.json.Value.objectFromString("{\"status\":\"ok\"}") };
    const output = try JsonRpc.formatResponse(allocator, response);
    try testing.expect(std.mem.indexOf(u8, output, "\"jsonrpc\":\"2.0\"") != null);
}
```

- [ ] **Step 7: Run test to verify it fails**

Run: `zig build test -- --test-filter "format success" -v`
Expected: FAIL with "use of undeclared identifier 'formatResponse'"

- [ ] **Step 8: Implement response formatting**

Add to `src/repl/jsonrpc.zig`:
```zig
pub fn formatResponse(allocator: std.mem.Allocator, response: Response) ![]const u8 {
    var root = std.json.Value.init(allocator);
    defer root.deinit();
    
    var obj = try root.object();
    try obj.put("jsonrpc", "2.0");
    try obj.put("id", response.id);
    
    if (response.result) |result_value| {
        try obj.put("result", result_value.*);
    }
    
    if (response.@"error") |err| {
        try obj.put("error", err.*);
    }
    
    return root.stringifyAlloc(allocator);
}
```

- [ ] **Step 9: Run test to verify it passes**

Run: `zig build test -- --test-filter "format success" -v`
Expected: PASS

- [ ] **Step 10: Commit**

```bash
git add src/repl/jsonrpc.zig
git commit -m "feat(repl): add JsonRpc response formatting"
```

---

## Chunk 2: Server Mode Implementation

### Task 3: Create ReplServer Module

**Files:**
- Create: `src/repl/server.zig`
- Modify: `src/repl/session.zig`

- [ ] **Step 11: Write failing test for server init**

```zig
test "server: init and process request" {
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"eval\",\"params\":{\"input\":\"42\"}}";
    var stdout = std.ArrayList(u8).init(testing.allocator);
    defer stdout.deinit();
    
    const writer = stdin: ReadWriter = .{ .stdio = .{
        .inStream = .{ .context = .{ .input = input } },
        .outStream = .{ .context = .{ .output = &stdout } },
    }};
    
    var server = try ReplServer.init(testing.io);
    defer server.deinit();
    
    try server.processRequest(&writer);
    
    try testing.expect(stdout.items.len > 0);
}
```

- [ ] **Step 12: Run test to verify it fails**

Run: `zig build test -- --test-filter "server init" -v`
Expected: FAIL with "use of undeclared identifier 'ReplServer'"

- [ ] **Step 13: Create ReplServer module structure**

Create `src/repl/server.zig`:
```zig
const std = @import("std");
const Session = @import("session.zig").Session;
const protocol = @import("protocol.zig");
const JsonRpc = @import("jsonrpc.zig");

pub const ReplServer = struct {
    allocator: std.mem.Allocator,
    session: *Session,
    stdin: std.Io.Reader,
    stdout: std.Io.Writer,
    
    pub fn init(allocator: std.mem.Allocator, io: std.Io) !ReplServer {
        const session = try Session.init(allocator, io);
        return .{
            .allocator = allocator,
            .session = session,
            .stdin = io.reader(),
            .stdout = io.writer(),
        };
    }
    
    pub fn deinit(self: *ReplServer) void {
        self.session.deinit();
    }
    
    pub fn run(self: *ReplServer) !void {
        var line_buf: [4096]u8 = undefined;
        
        while (true) {
            const line = try self.stdin.readUntilDelimiterOrEof(&line_buf, '\n');
            if (line.len == 0) break;
            
            const response = try self.processRequest(line);
            try self.stdout.writeAll(response);
            try self.stdout.writeByte('\n');
        }
    }
    
    fn processRequest(self: *ReplServer, input: []const u8) ![]const u8 {
        const request = try JsonRpc.parseRequest(self.allocator, input);
        
        // Handle method dispatch...
        
        return JsonRpc.formatResponse(self.allocator, .{ .id = request.id, .result = null });
    }
};
```

- [ ] **Step 14: Run test to verify it passes**

Run: `zig build test -- --test-filter "server init" -v`
Expected: PASS

- [ ] **Step 15: Commit**

```bash
git add src/repl/server.zig
git commit -m "feat(repl): add ReplServer module with JSON-RPC dispatch"
```

---

## Chunk 3: Integration with Entry Point

### Task 4: Add CLI Argument Handling

**Files:**
- Modify: `src/main.zig`

- [ ] **Step 16: Write failing test for --server flag**

```zig
test "main: parse --server argument" {
    const args = &[_][]const u8{"rhc", "--server"};
    const result = try cli.parse(args, testing.allocator);
    try testing.expect(result.server_mode);
}
```

- [ ] **Step 17: Run test to verify it fails**

Run: `zig build test -- --test-filter "parse --server" -v`
Expected: FAIL with "no such member 'server_mode'"

- [ ] **Step 18: Add server mode to CLI options**

Modify `src/main.zig`:
```zig
const Config = struct {
    server_mode: bool = false,
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();
    
    const args = try std.process.argsAlloc(allocator, 0);
    
    var config = Config{};
    for (args) |arg| {
        if (std.mem.eql(u8, arg, "--server")) {
            config.server_mode = true;
        }
    }
    
    if (config.server_mode) {
        return runServerMode(allocator);
    }
    
    // ... existing interactive mode ...
}

fn runServerMode(allocator: std.mem.Allocator) !void {
    io = std.Io.Threaded.init_single_threaded;
    var server = try ReplServer.init(allocator, .io.io());
    defer server.deinit();
    
    try server.run();
}
```

- [ ] **Step 19: Run test to verify it passes**

Run: `zig build test -- --test-filter "parse --server" -v`
Expected: PASS

- [ ] **Step 20: Commit**

```bash
git add src/main.zig
git commit -m "feat(cli): add --server flag for REPL server mode"
```

---

## Chunk 4: WASM Integration

### Task 5: Add Server Entry Point for WASM

**Files:**
- Modify: `src/repl_wasm_main.zig`
- Modify: `src/repl/exports.zig`

- [ ] **Step 21: Add server entry point to WASM exports**

Modify `src/repl/exports.zig`:
```zig
/// Run REPL in server mode (reads JSON-RPC from stdin, writes to stdout).
/// Exposed so CLI args can trigger server mode for WASM (via wasmtime).
var server_mode: bool = false;

/// Set server mode flag (called by repl_wasm_main before starting).
export fn repl_set_server_mode(mode: bool) void {
    server_mode = mode;
}

/// Server mode entry point for WASM.
/// Processes JSON-RPC requests line by line until shutdown.
export fn repl_server_run() void {
    if (!server_mode) return;
    
    const alloc = session_arena.?.allocator() orelse return;
    const s = &(session orelse return);
    
    // Simple stdin/stdout loop based server implementation
    // (reuse existing line reader logic)
}
```

- [ ] **Step 22: Wire up server mode to CLI**

Modify `src/repl_wasm_main.zig`:
```zig
pub fn main() void {
    const args = try std.process.argsAlloc(arena.allocator, 0);
    
    for (args) |arg| {
        if (std.mem.eql(u8, arg, "--server")) {
            exports.repl_set_server_mode(true);
        }
    }
    
    if (exports.server_mode) {
        exports.repl_server_run();
    }
}
```

- [ ] **Step 23: Commit**

```bash
git add src/repl_wasm_main.zig src/repl/exports.zig
git commit -m "feat(wasm): add --server mode support for WASM REPL"
```

---

## Chunk 5: Protocol Handlers

### Task 6: Implement Core Commands

**Files:**
- Modify: `src/repl/server.zig`

- [ ] **Step 24: Write failing test for eval command**

```zig
test "server: eval command handles simple expression" {
    const alloc = testing.allocator;
    var session = try Session.init(alloc, testing.io);
    defer session.deinit();
    
    const result = try handleEval(&session, alloc, "main");
    try testing.expectEqualStrings("success", result.status);
}
```

- [ ] **Step 25: Implement eval command handler**

Add to `src/repl/server.zig`:
```zig
fn handleEval(session: *Session, allocator: std.mem.Allocator, input: []const u8) !EvalResult {
    const result = try protocol.evaluate(allocator, session, input);
    return result;
}
```

- [ ] **Step 26: Commit**

```bash
git add src/repl/server.zig
git commit -m "feat(server): implement eval command handler"
```

### Task 7: Implement Other Commands

- [ ] **Step 27: Implement type command**

Add to `src/repl/server.zig`:
```zig
fn handleType(session: *Session, allocator: std.mem.Allocator, input: []const u8) !TypeResult {
    const result = try protocol.typeCheck(allocator, session, input);
    return result;
}
```

- [ ] **Step 28: Implement shutdown command**

Add to `src/repl/server.zig`:
```zig
fn handleShutdown(session: *Session) !void {
    // Graceful cleanup
}

fn handleInit(allocator: std.mem.Allocator) !Session {
    return Session.init(allocator, std.io());
}
```

- [ ] **Step 29: Commit**

```bash
git add src/repl/server.zig
git commit -m "feat(server): implement type, shutdown, init commands"
```

---

## Chunk 6: Testing

### Task 8: End-to-End Integration Tests

**Files:**
- Create: `tests/repl/server_tests.zig`

- [ ] **Step 30: Write integration test for server mode**

Create `tests/repl/server_tests.zig`:
```zig
test "server: basic request-response cycle" {
    const alloc = testing.allocator;
    
    // Mock stdin/stdout for test
    var input_stream = std.io.fixedBufferStream("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"init\"}\n");
    var output_stream = std.ArrayList(u8).init(alloc);
    
    var server = try ReplServer.init(alloc, testing.io);
    defer server.deinit();
    
    try server.processRequest(&input_stream, &output_stream);
    
    // Verify output is valid JSON-RPC response
    const output = try output_stream.toOwnedSlice(alloc);
    try testing.expect(std.mem.indexOf(u8, output, "\"jsonrpc\":\"2.0\"") != null);
}
```

- [ ] **Step 31: Run test**

Run: `zig build test -- --test-filter "server" -v`
Expected: PASS

- [ ] **Step 32: Commit**

```bash
git add tests/repl/server_tests.zig
git commit -m "test(server): add basic server mode integration tests"
```

### Task 9: Manual Testing

- [ ] **Step 33: Test native REPL server mode**

```bash
# Start server
echo '{"jsonrpc":"2.0","id":1,"method":"init","params":{}}' | rhc repl --server

# Test eval
echo '{"jsonrpc":"2.0","id":2,"method":"eval","params":{"input":"42"}}' | rhc repl --server
```

Expected: Valid JSON responses returned

- [ ] **Step 34: Test WASM REPL server mode**

```bash
# Build and run WASM REPL in server mode
wasmtime --dir=. zig-out/bin/repl.wasm -- --server
```

Expected: Runs without crashing, ready for stdin input

---

## Chunk 7: Documentation

### Task 10: Update Documentation

**Files:**
- Modify: `docs/decisions/0006-repl-architecture.md`
- Create: `docs/proxy/repl_protocol.md`

- [ ] **Step 35: Document protocol in repo docs**

Create `docs/proxy/repl_protocol.md`:
```markdown
# REPL Protocol

## Overview
The REPL server speaks JSON-RPC 2.0 over stdin/stdout.

## Transport
- Line-based: one JSON object per line on stdin, one JSON response per line on stdout
- Works with both native and WASM backends

## Commands
- init: Initialize REPL session
- eval: Evaluate Haskell expression
- type: Type-check expression
- shutdown: Shutdown gracefully
- :quit: Maps to shutdown
- :load: Load file
- :type: Type interface

## Error Handling
Errors are returned via JSON-RPC error objects with structured diagnostics.

## Usage
# Native REPL server mode
rhc repl --server

# WASM REPL server mode
wasmtime repl.wasm --dir=. -- --server
```

- [ ] **Step 36: Update REPL architecture doc**

Modify `docs/decisions/0006-repl-architecture.md`:
- Add server mode section
- Document protocol layer
- Reference design spec

- [ ] **Step 37: Commit**

```bash
git add docs/proxy/repl_protocol.md docs/decisions/0006-repl-architecture.md
git commit -m "docs: document REPL protocol server mode"
```

---

## Chunk 8: CI and Build

### Task 11: Update Build Configuration

**Files:**
- Modify: `build.zig` (if needed)
- Modify: `flake.nix` (if needed)

- [ ] **Step 38: Ensure server mode builds**

Run: `zig build`
Expected: Build succeeds for both native and WASM targets

- [ ] **Step 39: Ensure tests pass**

Run: `zig build test --summary all`
Expected: All tests pass including new server tests

- [ ] **Step 40: Commit if changes needed**

```bash
git add build.zig flake.nix
git commit -m "build: update config for server mode support"
```

---

## Completion Checklist

- [ ] JsonRpc module created with JSON-RPC 2.0 support
- [ ] ReplServer module created with stdin/stdout JSON-RPC handling
- [ ] CLI flag (`--server`) added for both native and WASM
- [ ] Core protocol handlers (init, eval, type, shutdown) implemented
- [ ] Integration tests verify protocol behavior
- [ ] Documentation covers protocol specification
- [ ] Native and WASM backends have identical server mode behavior
- [ ] All tests pass

## Verification

To verify this implementation:
1. Run `rhc repl --server` and send JSON-RPC requests via stdin
2. Run `wasmtime repl.wasm --dir=. -- --server` and verify it handles requests
3. Run integration tests: `zig build test -- --test-filter "server"`
4. Verify existing REPL functionality unchanged (default mode still works)

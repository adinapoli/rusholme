# REPL `:type` Command Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement `:type <expr>` / `:t <expr>` commands for native and WASM REPLs to display inferred types without modifying session state or evaluating expressions.

**Architecture:** Core `typeOf()` function wraps existing pipeline for type inference, using transactional scope rollback for read-only semantics. Protocol and server layers handle error diagnostics, CLI/web UI route JSON-RPC calls.

**Tech Stack:** Zig (Rusholme compiler), JavaScript (browser REPL), JSON-RPC 2.0 protocol

---

## File Structure

**New files:**
- `src/repl/typequery.zig` - Core type query API (`typeOf()`, `TypeQueryResult`)
- `tests/repl/wasm_e2e_type_tests.zig` - E2E tests for WASM type queries via JSON-RPC

**Modified files:**
- `src/repl/protocol.zig` - Add `typeOf()` wrapper function
- `src/repl/server.zig` - Implement `dispatchType()` for JSON-RPC
- `src/repl/cli.zig` - Handle `:type` / `:t` commands
- `website/template.html` - Route `:type` to JSON-RPC

---

## Chunk 1: Core Type Query API (`typequery.zig`)

### Task 1: Create module stub with result type

**Files:**
- Create: `src/repl/typequery.zig`

- [ ] **Step 1: Create module with TypeQueryResult struct and function stub**

```zig
const std = @import("std");
const Allocator = std.mem.Allocator;

const Session = @import("session.zig").Session;
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");

pub const TypeQueryResult = struct {
    /// The inferred type scheme (polymorphic or monomorphic).
    /// Note: The HType body is arena-allocated from the session's allocator.
    /// The result is valid only for the lifetime of the session arena.
    scheme: env_mod.TyScheme,
    /// Formatted display string: "<expr> :: <type>"
    /// Allocated by the caller's allocator; caller must free.
    display: []const u8,
    /// Diagnostics from type-checking (empty on success).
    /// These are owned by session.last_diagnostics and persist across queries.
    diags: []const @import("../diagnostics/diagnostic.zig").Diagnostic,
};

/// Type-check an expression and return its inferred type.
/// Does NOT modify session state, does NOT evaluate, does NOT execute IO.
pub fn typeOf(
    alloc: std.mem.Allocator,
    session: *Session,
    expr: []const u8,
) !TypeQueryResult {
    _ = alloc;
    _ = session;
    _ = expr;
    @panic("Not implemented");
}
```

- [ ] **Step 2: Run build to verify module compiles**

Run: `zig build`
Expected: SUCCESS

- [ ] **Step 3: Commit**

```bash
git add src/repl/typequery.zig
git commit -m "type: add typeOf stub with TypeQueryResult struct"
```

### Task 2: Implement typeOf() to compile and infer types

**Files:**
- Modify: `src/repl/typequery.zig`

- [ ] **Step 1: Add pipeline imports**

```zig
const std = @import("std");
const Allocator = std.mem.Allocator;

const Session = @import("session.zig").Session;
const pipeline = @import("pipeline.zig").Pipeline;
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");
```

- [ ] **Step 2: Implement typeOf() to call pipeline and extract type**

Update the `typeOf` function:

```zig
pub fn typeOf(
    alloc: std.mem.Allocator,
    session: *Session,
    expr: []const u8,
) !TypeQueryResult {
    _ = alloc;

    // 1. Compile the expression through the pipeline
    const compile = try session.pipeline.compileInput(
        expr,
        &session.u_supply,
        &session.rename_env,
        &session.ty_env,
        &session.mv_supply,
        null, // diags not needed here
        &session.accumulated_arities,
        &session.accumulated_con_map,
    );

    // 2. Transactional rollback: pop scope frames to restore state
    session.ty_env.pop();
    session.rename_env.scope.pop();

    // 3. Look up the type via the synthesized name
    const def = compile.program.defs[0];
    const scheme = session.ty_env.lookupScheme(def.name.unique) orelse {
        return error.TypeCheckFailed;
    };

    // 4. Format the display: "<expr> :: <type>"
    const type_str = try htype_mod.prettyScheme(scheme, session.allocator);
    defer session.allocator.free(type_str);
    const display = try std.fmt.allocPrint(session.allocator, "{s} :: {s}", .{ expr, type_str });

    return TypeQueryResult{
        .scheme = scheme,
        .display = display,
        .diags = &.{},
    };
}
```

- [ ] **Step 3: Verify build passes**

Run: `zig build`
Expected: SUCCESS

- [ ] **Step 4: Add unit test for simple literal**

```zig
const testing = std.testing;
const testing_io = testing.io;

test "typequery: simple literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing_io);
    defer session.deinit();

    const result = try typeOf(alloc, &session, "42");
    defer alloc.free(result.display);

    try testing.expectEqualStrings("42 :: Int", result.display);
}
```

- [ ] **Step 5: Run test to verify it passes**

Run: `zig build test`
Expected: All tests pass

- [ ] **Step 6: Commit**

```bash
git add src/repl/typequery.zig
git commit -m "type: implement typeOf() to compile and infer types"
```

### Task 3: Add test for session state preservation

**Files:**
- Modify: `src/repl/typequery.zig`

- [ ] **Step 1: Add test for session state unchanged**

```zig
test "typequery: session state unchanged after query" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing_io);
    defer session.deinit();

    // Define something first
    _ = try session.processInput("id x = x");

    const arities_before = session.accumulated_arities.count();
    const con_map_before = session.accumulated_con_map.count();

    // Query a type - should not modify accumulated state
    _ = try typeOf(alloc, &session, "42");

    // Session state should not be modified
    try testing.expectEqual(arities_before, session.accumulated_arities.count());
    try testing.expectEqual(con_map_before, session.accumulated_con_map.count());
}
```

- [ ] **Step 2: Run test to verify it passes**

Run: `zig build test`
Expected: All tests pass

- [ ] **Step 3: Commit**

```bash
git add src/repl/typequery.zig
git commit -m "type: add test for session state preservation"
```

---

## Chunk 2: Protocol Layer Integration

### Task 4: Add typeOf() to protocol.zig

**Files:**
- Modify: `src/repl/protocol.zig`

- [ ] **Step 1: Import typequery module**

```zig
const std = @import("std");
const Allocator = std.mem.Allocator;

const Session = @import("session.zig").Session;
const typequery = @import("typequery.zig");
const Diagnostic = @import("../diagnostics/diagnostic.zig").Diagnostic;
```

- [ ] **Step 2: Add typeOf() function to protocol.zig**

```zig
/// Get the type of a REPL expression through the protocol.
pub fn typeOf(allocator: Allocator, session: *Session, input: []const u8) !ProtocolResult {
    const query_result = typequery.typeOf(allocator, session, input) catch |err| {
        // On error, return error status with diagnostics
        var diags = session.getDiagnosticsForInput(allocator, input) catch &.{};

        // Get the first diagnostic's error message (or fall back to error name)
        if (diags.len > 0) {
            return ProtocolResult{
                .status = .failed,
                .value = diags[0].message,
                .diagnostics = diags,
            };
        }

        const msg = std.fmt.allocPrint(allocator, "Type checking failed: {s}", .{@errorName(err)});
        return ProtocolResult{
            .status = .failed,
            .value = msg,
            .diagnostics = diags,
        };
    };

    // Success case: type query succeeded
    // Caller must free result.value (allocated by type.typeOf) and any diagnostic notes
    return ProtocolResult{
        .status = .success,
        .value = query_result.display,  // Full "<expr> :: <type>" string
        .diagnostics = &.{},
    };
}
```

- [ ] **Step 3: Verify build and tests pass**

Run: `zig build test`
Expected: All tests pass

- [ ] **Step 4: Commit**

```bash
git add src/repl/protocol.zig
git commit -m "protocol: add typeOf() wrapper for type queries"
```

---

## Chunk 3: Server Integration

### Task 5: Implement dispatchType() in server.zig

**Files:**
- Modify: `src/repl/server.zig`

- [ ] **Step 1: Update dispatch loop to handle "type" method**

Replace the existing stub in `processRequestToString`:

```zig
if (std.mem.eql(u8, method, "type")) {
    return try self.dispatchType(id, request.params);
}
```

- [ ] **Step 2: Implement dispatchType() function**

Replace the existing stub:

```zig
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
```

- [ ] **Step 3: Remove the old stub comment**

Delete the old comment that said " tracked in: https://github.com/adinapoli/rusholme/issues/494 "

- [ ] **Step 4: Verify build passes**

Run: `zig build`
Expected: SUCCESS

- [ ] **Step 5: Commit**

```bash
git add src/repl/server.zig
git commit -m "server: implement dispatchType() for JSON-RPC type queries"
```

---

## Chunk 4: E2E Tests

### Task 6: Create WASM e2e tests for type queries

**Files:**
- Create: `tests/repl/wasm_e2e_type_tests.zig`

- [ ] **Step 1: Create test file with helper functions**

```zig
const std = @import("std");
const testing = std.testing;

const process = std.process;
const Io = std.Io;

// Helpers from wasm_e2e_tests.zig
const runServer = @import("wasm_e2e_tests.zig").runServer;
const extractResult = @import("wasm_e2e_tests.zig").extractResult;
const splitLines = @import("wasm_e2e_tests.zig").splitLines;
```

- [ ] **Step 2: Add test for type request on literal**

```zig
test "type e2e: jsonrpc type request for literal" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"type","params":["42"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    const r = try extractResult(testing.allocator, lines[1]);
    defer if (r) |s| testing.allocator.free(s);

    try testing.expect(std.mem.indexOf(u8, r.?, "42") != null);
    try testing.expect(std.mem.indexOf(u8, r.?, "::") != null);
}
```

- [ ] **Step 3: Add test for type request on unbound name**

```zig
test "type e2e: jsonrpc type request returns diagnostics on error" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"type","params":["undefinedVar"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    // Should contain error response
    try testing.expect(std.mem.indexOf(u8, result.stdout, "\"error\"") != null);
}
```

- [ ] **Step 4: Add test for session-defined function type**

```zig
test "type e2e: session-defined function type" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["id x = x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"type","params":["id"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    const r = try extractResult(testing.allocator, lines[2]);
    defer if (r) |s| testing.allocator.free(s);

    try testing.expect(std.mem.indexOf(u8, r.?, "forall") != null);
    try testing.expect(std.mem.indexOf(u8, r.?, "a -> a") != null);
}
```

- [ ] **Step 5: Run all tests to verify**

Run: `zig build test --summary all`
Expected: All 840+ tests pass

- [ ] **Step 6: Commit**

```bash
git add tests/repl/wasm_e2e_type_tests.zig
git commit -m "tests: add E2E tests for type queries"
```

---

## Chunk 5: Native CLI Integration

### Task 7: Add :type / :t command handling to CLI

**Files:**
- Modify: `src/repl/cli.zig`

- [ ] **Step 1: Import typequery module**

```zig
const std = @import("std");
const typequery = @import("typequery.zig");
```

- [ ] **Step 2: Add command handling in the appropriate location**

Find the command processing section (around line 200 in cli.zig) and add:

```zig
if (std.mem.eql(u8, cmd, "type") or std.mem.eql(u8, cmd, "t")) {
    const result = try typequery.typeOf(allocator, &session, rest_of_line);
    defer allocator.free(result.display);
    try stdout.writer.writeAll(result.display);
    try stdout.writer.writeAll("\n");
    return;
}
```

- [ ] **Step 3: Verify build passes**

Run: `zig build`
Expected: SUCCESS

- [ ] **Step 4: Test manually**

Run: `zig build repl && ./zig-out/bin/repl`
Input:
```
> :type 42
42 :: Int
```
Expected: Displays correct type

- [ ] **Step 5: Commit**

```bash
git add src/repl/cli.zig
git commit -m "cli: add :type / :t command handling"
```

---

## Chunk 6: WASM Browser REPL Integration

### Task 8: Route :type to JSON-RPC in browser REPL

**Files:**
- Modify: `website/template.html`

- [ ] **Step 1: Find the command processing section**

Look for the section around line 1698 where commands are parsed (`if (cmd.startsWith('load '))`).

- [ ] **Step 2: Add :type / :t handling**

Replace/stub with:

```javascript
if (cmd.startsWith('type ') || cmd.startsWith('t ')) {
    const expr = cmd.substring(cmd.startsWith('type ') ? 5 : 2).trim();
    // Use JSON-RPC 'type' method
    replBridge.sendRequest('type', [expr]).then(response => {
        if (response.error) {
            term.writeln(response.error.message);
        } else {
            term.writeln(response.result);
        }
    });
    return;
}
```

- [ ] **Step 3: Test in browser**

1. Open the local website
2. In the REPL, type: `:t 42`
3. Expected: Displays `42 :: Int`

- [ ] **Step 4: Commit**

```bash
git add website/template.html
git commit -m "wasm: route :type command to JSON-RPC"
```

---

## Completion

### Task 9: Final verification

- [ ] **Step 1: Run all tests**

Run: `zig build test --summary all`
Expected: All tests pass

- [ ] **Step 2: Verify the feature works end-to-end**

Native CLI:
```bash
zig build repl
./zig-out/bin/repl
> id x = x
> :type id
> :t 42
```

WASM Browser:
1. Open website
2. Test `:type`, `:t`, and error cases

- [ ] **Step 3: Write a summary comment to close the issue**

GitHub issue #500 resolved.

---

**Execution complete.**

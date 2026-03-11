# REPL `:type` Command Design

## Issue

GitHub #500: REPL: Implement `:type` command to show expression types

## Overview

Implement a `:type <expr>` / `:t <expr>` command for both native CLI and WASM REPLs that displays the inferred type of an expression. The behavior should match GHCi's `:type` command — type inference runs in a read-only mode without modifying session state, evaluating, or executing side-effects.

## Requirements

1. **Type display** - Show the inferred type in human-readable format
   - Simple types: `42 :: Int`, `"hello" :: [Char]`
   - Polymorphic types: `forall a. a -> a`
   - Constructor types: `forall a. List a`

2. **Session context** - Support expressions that reference bindings from the REPL session
   - Prelude functions (when Prelude is implemented)
   - User-defined functions: `id x = x` → `:t id` shows `forall a. a -> a`
   - User-defined ADTs: `data List a = Nil ...` → `:t Nil` shows `forall a. List a`

3. **No side-effects** - Must NOT:
   - Modify session state
   - Evaluate expressions
   - Execute IO
   - Create bindings

4. **Error handling** - Return structured diagnostics on type errors, same format as `eval`

## Architecture

### Core API: `typeOf()` function

**New file:** `src/repl/typequery.zig`

```zig
pub const TypeQueryResult = struct {
    /// The inferred type scheme (polymorphic or monomorphic).
    /// Note: The HType body is arena-allocated from the session's allocator.
    /// The result is valid only for the lifetime of the session arena.
    scheme: typechecker.TyScheme,
    /// Formatted display string: "<expr> :: <type>"
    /// Allocated by the caller's allocator; caller must free.
    display: []const u8,
    /// Diagnostics from type-checking (empty on success).
    /// These are owned by session.last_diagnostics and persist across queries.
    diags: []const Diagnostic,
};

/// Type-check an expression and return its inferred type.
///
/// This is a READ-ONLY operation:
/// - Does NOT modify session state (renamer or type environment)
/// - Does NOT evaluate expressions or execute IO
/// - Does NOT create bindings in the session
///
/// Type inference uses a transactional scope pattern:
/// - Pushes scope frames on rename_env and ty_env before inference
/// - On success: looks up type, then pops scope frames (rollback)
/// - On failure: pops scope frames (rollback, then returns error)
pub fn typeOf(
    alloc: std.mem.Allocator,
    session: *Session,
    expr: []const u8,
) !TypeQueryResult {
    // Implementation...
}
```

**Component diagram:**

```
                ┌─────────────┐
                │   Session   │
                │ (ty_env,    │
                │  mv_supply, │
                │  ...)       │
                └──────┬──────┘
                       │
                ┌──────▼──────┐
                │  typeOf()   │  ◄── Uses existing ty_env state
                │              │      Transactional rollback
                └──────┬──────┘      on failure/success
                       │
         ┌────────────┴────────────┐
         │                          │
         ▼                          ▼
┌────────────────────┐    ┌─────────────────┐
│  Pipeline.compile  │    │  Type Inference │
│  (reuse)           │    │  (reused)       │
│  - Parse           │    │  - inferModule  │
│  - Rename          │    │  - lookup       │
│  - Type-check      │    │  - prettyScheme│
└────────────────────┘    └─────────────────┘
```

### Implementation Approach

The `typeOf` function extracts type information from the existing compilation pipeline **without** running the full eval step:

1. Call `pipeline.compileInput()` with `kind == .expression`
2. This runs through: Parser → Desugarer → Renamer → Type-checker
3. The pipeline wraps the expression as `replExpr__ = <expr>` in a module
4. The type-checker populates `session.ty_env` with the expression's type under the synthesized name
5. Look up the type via `session.ty_env.lookupScheme(compile.program.defs[0].name.unique)` to get the TyScheme
6. Format via `HType.prettyScheme()` to get the type string
7. Construct display format: combine original expr + " :: " + type string
8. **Immediately rollback** by popping scope frames on rename_env and ty_env

Key point: The existing `CompileResult` already contains type information. We're just extracting it and discarding the GRIN program.

**Note on "read-only":** Type inference requires modifying environments (pushing/pulling frames) during execution. The "read-only" requirement means **no persistent state changes that affect subsequent REPL interactions**. The transactional scope pattern (push before, pop after) achieves this by rolling back all changes.

### Server Integration: JSON-RPC

**Modify `src/repl/server.zig`:**

```zig
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

### Protocol Layer

**Modify `src/repl/protocol.zig` (add new function):**

```zig
/// Get the type of a REPL expression through the protocol.
pub fn typeOf(allocator: Allocator, session: *Session, input: []const u8) !ProtocolResult {
    const query_result = type.typeOf(allocator, session, input) catch |err| {
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

**Note:** The existing `evaluate()` function in `protocol.zig` already handles error diagnostics correctly and does not need modification. Only the new `typeOf()` function needs to be added.

### Native CLI

**Modify `src/repl/cli.zig`:**

```zig
if (std.mem.eql(u8, cmd, "type") or std.mem.eql(u8, cmd, "t")) {
    const result = try typequery.typeOf(allocator, &session, rest_of_line);
    defer allocator.free(result.display);
    try io.stdout.writer.writeAll(result.display);
    return;
}
```

### WASM TUI

**Modify `website/template.html`:**

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

## Testing Strategy

### Unit Tests (`src/repl/typequery.zig`)

```zig
test "typequery: simple literal" {
    var session = try Session.init(alloc, io);
    defer session.deinit();

    const result = try typeOf(alloc, &session, "42");
    defer alloc.free(result.display);

    try testing.expectEqualStrings("42 :: Int", result.display);
}

test "typequery: function with polymorphism" {
    var session = try Session.init(alloc, io);
    defer session.deinit();

    // First: define id
    _ = try session.processInput("id x = x");

    // Then: query its type
    const result = try typeOf(alloc, &session, "id");
    defer alloc.free(result.display);

    try testing.expect(std.mem.indexOf(u8, result.display, "forall") != null);
    try testing.expect(std.mem.indexOf(u8, result.display, "a -> a") != null);
}

test "typequery: unbound name returns error with diagnostics" {
    var session = try Session.init(alloc, io);
    defer session.deinit();

    try testing.expectError(error.TypeCheckFailed, typeOf(alloc, &session, "undefinedVar"));
}

test "typequery: session state unchanged after query" {
    var session = try Session.init(alloc, io);
    defer session.deinit();

    const arities_before = session.accumulated_arities.count();
    const con_map_before = session.accumulated_con_map.count();

    _ = try typeOf(alloc, &session, "42");

    // Session state should not be modified
    try testing.expectEqual(arities_before, session.accumulated_arities.count());
    try testing.expectEqual(con_map_before, session.accumulated_con_map.count());
}
```

### E2E Tests (`tests/repl/type_e2e_tests.zig`) - New file

```zig
// Tests JSON-RPC `type` method
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

    try testing.expect(std.mem.indexOf(u8, r.?, "42 :: Int") != null);
}

test "type e2e: jsonrpc type request returns diagnostics on error" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"type","params":["undefined"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    // Should contain error response with structured diagnostics
    try testing.expect(try hasError(testing.allocator, result.stdout));
}

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

### Manual Test Cases

| Input | Expected Output |
|-------|-----------------|
| `:type 42` | `42 :: Int` |
| `:t "hello"` | `"hello" :: [Char]` |
| `:t undefined` | Error with diagnostic: "Unbound variable" |
| After `id x = x`, `:t id` | `forall a. a -> a` |
| After `const x _ = x`, `:t const` | `forall a b. a -> b -> a` |

## Implementation Order

1. Core infrastructure (`src/repl/typequery.zig`)
2. Protocol layer (`src/repl/protocol.zig`) - `typeOf()` wrapper
3. Server integration (`src/repl/server.zig`) - JSON-RPC `dispatchType()`
4. Native CLI (`src/repl/cli.zig`) - Command handling
5. WASM TUI (`website/template.html`) - JSON-RPC call routing
6. Tests (unit + e2e)

## References

- `src/typechecker/infer.zig` - Type inference algorithm
- `src/typechecker/htype.zig` - Type representation and display (`pretty()`, `prettyScheme()`)
- `src/typechecker/env.zig` - Type environment lookup (`lookupScheme`, `lookup`)
- `src/repl/server.zig` - JSON-RPC `dispatchType()` stub
- `src/repl/protocol.zig` - REPL protocol and error handling
- `website/template.html` - Browser REPL UI

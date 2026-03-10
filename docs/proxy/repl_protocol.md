# REPL Protocol Reference

This document describes the Rusholme REPL protocol, which provides a structured interface for interacting with the Haskell REPL programmatically. The protocol has two primary usage modes:

1. **Server Mode** - JSON-RPC 2.0 over stdin/stdout for external clients
2. **WASM Mode** - Direct function calls from JavaScript via WebAssembly exports

---

## Overview

The REPL protocol separates the REPL's core functionality from its presentation layer. This allows multiple user interfaces to interact with the same backend:

- **Native CLI** - Interactive terminal REPL with colors and line editing
- **Browser REPL** - Web-based REPL via xterm.js and WASM
- **Server Mode** - JSON-RPC server for integration testing and custom frontends
- **Test Clients** - Automated test harnesses for end-to-end validation

All modes share the same core implementation through the `repl.protocol` module (`src/repl/protocol.zig`), which provides:

- `evaluate()` - Evaluate a Haskell expression or declaration
- `getDiagnostics()` - Retrieve diagnostics from the last evaluation
- `Status` enum - Success, failed, or silent operation states
- `ProtocolResult` struct - Structured result with status, value, and diagnostics

---

## Transport Specification

### Server Mode: Line-based JSON over stdin/stdout

Server mode uses JSON-RPC 2.0 over line-based framing:

- **Requests**: One JSON object per line on stdin
- **Responses**: One JSON object per line on stdout
- **Encoding**: UTF-8
- **Framing**: newline-terminated lines (no length prefix)

#### Example Session

```bash
# Client sends request
echo '{"jsonrpc":"2.0","id":1,"method":"eval","params":["2 + 2"]}' | rhc repl --server

# Server responds
{"jsonrpc":"2.0","id":1,"result":"4"}
```

### WASM Mode: Direct Function Calls

WASM mode uses direct function calls with shared linear memory buffers:

- **Input buffer**: 4096 bytes (writes JavaScript -> WASM)
- **Output buffer**: 16384 bytes (reads WASM -> JavaScript)

See the "WASM Exports" section for details.

---

## Server Mode Commands

### init

Initialize a new REPL session. Must be called before any other commands.

**Request:**
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "init",
  "params": {}
}
```

**Response (success):**
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": "ok"
}
```

**Notes:**
- The session is implicitly created when the server starts
- Calling `init` multiple times is safe (idempotent)

### eval

Evaluate a Haskell expression or declaration.

**Request:**
```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "method": "eval",
  "params": ["2 + 2"]
}
```

**Response (expression evaluation):**
```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "result": "4"
}
```

**Response (declaration):**
```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "result": ""
}
```

**Response (error):**
```json
{
  "jsonrpc": "2.0",
  "id": -1,
  "error": {
    "code": -32603,
    "message": "Evaluation failed"
  }
}
```

**Behavior:**
- **Expressions**: Compiled, executed, and the result is returned
- **Declarations**: Compiled and added to the session state; empty string returned
- **Errors**: Failed status with diagnostic information

**Example expressions:**
- `"42"` - Integer literal
- `"2 + 2"` - Arithmetic
- `"[1, 2, 3]"` - List literal
- `"map (*2) [1,2,3]"` - Function application
- `'"hello"'` - String literal with escaped quotes

**Example declarations:**
- `"data Color = Red | Green | Blue"` - Data type declaration
- `"id x = x"` - Function declaration
- `"let x = 5"` - Let binding (automatically stripped)

### type

Type-check a Haskell expression. Returns the inferred type.

**Request:**
```json
{
  "jsonrpc": "2.0",
  "id": 3,
  "method": "type",
  "params": ["\\x -> x"]
}
```

**Response (not yet implemented):**
```json
{
  "jsonrpc": "2.0",
  "id": -1,
  "error": {
    "code": -32601,
    "message": "Type checking not yet implemented - requires type inference support in Session"
  }
}
```

**Status:** The `type` command is currently not implemented. Type inference support is tracked as a future enhancement.

### shutdown

Gracefully shut down the REPL server.

**Request:**
```json
{
  "jsonrpc": "2.0",
  "id": 4,
  "method": "shutdown",
  "params": {}
}
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": 4,
  "result": "ok"
}
```

**Notes:**
- The server exits with code 0 after this response
- If stdin closes, the server also exits gracefully

---

## Error Handling

Server mode follows JSON-RPC 2.0 error conventions:

### JSON-RPC Standard Codes

| Code | Message | Description |
|------|---------|-------------|
| -32700 | Parse error | Invalid JSON was received |
| -32600 | Invalid request | The JSON sent is not a valid Request object |
| -32601 | Method not found | The method does not exist / is not available |
| -32602 | Invalid params | Invalid method parameter(s) |
| -32603 | Internal error | Internal JSON-RPC error (e.g., evaluation failed) |

### Error Response Examples

**Parse error:**
```json
{
  "jsonrpc": "2.0",
  "id": null,
  "error": {
    "code": -32700,
    "message": "Parse error"
  }
}
```

**Method not found:**
```json
{
  "jsonrpc": "2.0",
  "id": 3,
  "error": {
    "code": -32601,
    "message": "Method not found"
  }
}
```

**Invalid params:**
```json
{
  "jsonrpc": "2.0",
  "id": 4,
  "error": {
    "code": -32602,
    "message": "Invalid params: expected string expression"
  }
}
```

**Evaluation failed:**
```json
{
  "jsonrpc": "2.0",
  "id": 5,
  "error": {
    "code": -32603,
    "message": "Evaluation failed"
  }
}
```

---

## WASM Exports

WASM mode exports functions that can be called directly from JavaScript. The session state persists across calls.

### Memory Buffers

- **Input buffer**: 4096 bytes at `repl_get_input_buffer()`
- **Output buffer**: 16384 bytes at `repl_get_output_buffer()`

### Functions

#### repl_init()

Initialize the REPL session. Must be called once before `repl_evaluate`.

```javascript
// JavaScript
repl_init();
```

**Behavior:**
- Creates a new Session instance
- Initializes compiler state (unique supply, rename env, type env, etc.)
- Safe to call multiple times (idempotent)

#### repl_evaluate(length)

Evaluate a REPL input. JS writes input to the input buffer, then calls this.

```javascript
// JavaScript
const encoder = new TextEncoder();
const input = "2 + 2";

// Copy input to WASM buffer
const inputBuffer = new Uint8Array(wasm.exports.memory.buffer, wasm.exports.repl_get_input_buffer());
encoder.encodeInto(input, inputBuffer.subarray(0, 4096));

// Evaluate
const outputLength = wasm.exports.repl_evaluate(input.length);

// Read output from WASM buffer
const outputBuffer = new Uint8Array(wasm.exports.memory.buffer, wasm.exports.repl_get_output_buffer());
const decoder = new TextDecoder();
const result = decoder.decode(outputBuffer.subarray(0, outputLength));
console.log(result); // {"status":"success","value":"4"}
```

**Response format:**

Success:
```json
{"status":"success","value":"4"}
```

Declaration (silent):
```json
{"status":"success","value":""}
```

Error:
```json
{"status":"error","message":"<description>","diagnostics":[...]}
```

#### repl_get_input_buffer()

Get a pointer to the input buffer (4096 bytes) for writing.

#### repl_get_output_buffer()

Get a pointer to the output buffer (16384 bytes) for reading.

---

## Usage Examples

### Native REPL (Interactive Mode)

```bash
# Start the interactive REPL
rhc repl

rusholme> 2 + 2
4
rusholme> let f x = x + 1
rusholme> f 5
6
rusholme> :quit
```

### Native REPL (Server Mode)

```bash
# Start server mode
rhc repl --server

# In another terminal, send requests
echo '{"jsonrpc":"2.0","id":1,"method":"init","params":{}}' | rhc repl --server
echo '{"jsonrpc":"2.0","id":2,"method":"eval","params":["2 + 2"]}' | rhc repl --server
```

### WASM Server Mode (via wasmtime)

```bash
# Build the WASM REPL
zig build repl.wasm

# Run in server mode via wasmtime
wasmtime repl.wasm --dir=. -- --server

# Send requests
echo '{"jsonrpc":"2.0","id":1,"method":"init","params":{}}' | wasmtime repl.wasm --dir=. -- --server
```

### Browser JavaScript Client

```javascript
// Load the WASM module
const response = await fetch('repl.wasm');
const bytes = await response.arrayBuffer();
const module = await WebAssembly.compile(bytes);
const instance = await WebAssembly.instantiate(module);
const exports = instance.exports;

// Initialize
exports.repl_init();

// Evaluate an expression
const encoder = new TextEncoder();
const inputBuffer = new Uint8Array(exports.memory.buffer, exports.repl_get_input_buffer());
encoder.encodeInto("2 + 2", inputBuffer.subarray(0, 4096));
const outputLength = exports.repl_evaluate(4);

// Parse result
const decoder = new TextDecoder();
const outputBuffer = new Uint8Array(exports.memory.buffer, exports.repl_get_output_buffer());
const resultText = decoder.decode(outputBuffer.subarray(0, outputLength));
const result = JSON.parse(resultText);

console.log(result.status); // "success"
console.log(result.value);  // "4"
```

### Python Test Client

```python
import subprocess
import json

def repl_eval(expr):
    proc = subprocess.Popen(
        ["rhc", "repl", "--server"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True
    )
    
    request = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "eval",
        "params": [expr]
    }
    
    proc.stdin.write(json.dumps(request) + "\n")
    proc.stdin.flush()
    
    response = json.loads(proc.stdout.readline())
    proc.terminate()
    
    return response

print(repl_eval("2 + 2"))  # {"jsonrpc": "2.0", "id": 1, "result": "4"}
```

---

## CLI Commands

The native CLI supports additional commands not exposed in the protocol:

| Command | Alias | Description |
|---------|-------|-------------|
| `:quit` | `:q` | Exit the REPL |
| `:type <expr>` | `:t` | Show type of expression (not yet implemented) |
| `:load <file>` | `:l` | Load a Haskell file into the session |
| `:{` | - | Begin multi-line input block |
| `:}` | - | End multi-line input block and evaluate |
| `:help` | `:h`, `:?` | Show help message |

The `:load` command:
- Reads the file from disk
- Strips the `module ... where` header
- Evaluates the contents via the protocol

---

## Architecture

### Protocol Layer (`src/repl/protocol.zig`)

The core protocol module provides:

```zig
pub const Status = enum {
    success,  // Successful evaluation with a value
    failed,   // Error occurred, diagnostics available
    silent,   // Declaration or command with no value
};

pub const ProtocolResult = struct {
    status: Status,
    value: []const u8,
    diagnostics: []const Diagnostic,
};

pub fn evaluate(allocator, session, input) !ProtocolResult;
pub fn getDiagnostics(session) []const Diagnostic;
```

### Server Mode Layer (`src/repl/server.zig`)

The `ReplServer` implements JSON-RPC 2.0:

```zig
pub const ReplServer = struct {
    allocator: Allocator,
    session: Session,
    io: std.Io,

    pub fn init(allocator, io) !ReplServer;
    pub fn deinit(self: *ReplServer) void;
    pub fn run(self: *ReplServer) !void;

    fn handleInit(self, id) !void;
    fn handleEval(self, id, params) !void;
    fn handleType(self, id, params) !void;
    fn handleShutdown(self, id) !void;
};
```

### JSON-RPC Module (`src/repl/jsonrpc.zig`)

Utilities for parsing and formatting JSON-RPC messages:

```zig
pub const Request = struct {
    jsonrpc: []const u8,
    id: u32,
    method: []const u8,
    params: ?std.json.Value,
    allocator: std.mem.Allocator,
};

pub const Response = struct {
    jsonrpc: []const u8,
    id: u32,
    result: ?std.json.Value,
    @"error": ?ErrorResponse,
    allocator: std.mem.Allocator,
};

pub fn parseRequest(allocator, input) ParseError!Request;
pub fn formatResponse(allocator, response) ![]const u8;
```

### WASM Export Layer (`src/repl/exports.zig`)

Direct functions for JavaScript to call:

```zig
pub export fn repl_init() void;
pub export fn repl_evaluate(length: usize) usize;
pub export fn repl_get_input_buffer() [*]u8;
pub export fn repl_get_output_buffer() [*]u8;
```

---

## Testing

Server mode is designed for easy testing via stdin/stdout scripting:

```bash
# Run a sequence of commands
{
    echo '{"jsonrpc":"2.0","id":1,"method":"init","params":{}}'
    echo '{"jsonrpc":"2.0","id":2,"method":"eval","params":["2 + 2"]}'
    echo '{"jsonrpc":"2.0","id":3,"method":"eval","params":["let f x = x + 1"]}'
    echo '{"jsonrpc":"2.0","id":4,"method":"eval","params":["f 5"]}'
    echo '{"jsonrpc":"2.0","id":5,"method":"shutdown","params":{}}'
} | rhc repl --server
```

This output:
```
{"jsonrpc":"2.0","id":1,"result":"ok"}
{"jsonrpc":"2.0","id":2,"result":"4"}
{"jsonrpc":"2.0","id":3,"result":""}
{"jsonrpc":"2.0","id":4,"result":"6"}
{"jsonrpc":"2.0","id":5,"result":"ok"}
```

---

## Future Enhancements

Planned but not yet implemented:

- **Type inference** - The `type` command requires full type inference support in Session
- **Structured diagnostics** - Richer error reporting with source spans and notes
- **Session persistence** - Save/restore REPL session state
- **Auto-completion** - Provide completions for expressions and commands
- **Multi-file support** - Import other REPL files or modules
- **Better line editing** - linenoise integration for CLI

---

## References

- **JSON-RPC 2.0 Specification**: https://www.jsonrpc.org/specification
- Decision 0006: [REPL Architecture](../decisions/0006-repl-architecture.md)
- Decision 0007: [REPL Protocol with Structured Responses](../decisions/0007-repl-protocol.md)
- Server Mode Design: [2026-03-10-repl-protocol-server-mode-design.md](../superpowers/specs/2026-03-10-repl-protocol-server-mode-design.md)

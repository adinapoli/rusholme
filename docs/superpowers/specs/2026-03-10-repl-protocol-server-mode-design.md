# Design: REPL Protocol Server Mode

## Overview

This design adds a server mode to the Rusholme REPL that speaks JSON-RPC 2.0 over stdin/stdout. The REPL becomes a server that can be driven by multiple client implementations:
- Interactive TUI client (reference implementation)
- Browser JavaScript client (debugging the WASM REPL)
- Integration test harnesses (end-2-end REPL testing)

All backends (native and WASM) use the same protocol over stdin/stdout. The design minimizes differences between native and WASM REPL behavior.

## Goals

1. Enable systematic debugging of WASM REPL issues (like #494)
2. Extend REPL test coverage with E2E tests driving via protocol
3. Provide architecture for multiple frontends (TUI, browser, future clients)
4. Maintain identical API between native and WASM backends

## Protocol Format

### Transport
- JSON-RPC 2.0 over line-based framing
- One JSON object per line on stdin
- Responses on stdout, one JSON per line
- Uses Zig's `std.json` parser, no custom framing

### JSON-RPC Structure
Requests follow JSON-RPC 2.0 specification:
```json
{"jsonrpc":"2.0","id":1,"method":"eval","params":{"input":"main"}}
```

Responses for successful calls:
```json
{"jsonrpc":"2.0","id":1,"result":{"status":"success","value":"..."}}
```

Error responses:
```json
{"jsonrpc":"2.0","id":1,"error":{"code":-32000,"message":"Runtime error","data":"..."}}
```

## Commands

### Core Commands

**init** - Initialize REPL session
```json
{"jsonrpc":"2.0","id":1,"method":"init","params":{}}
```
Response:
```json
{"jsonrpc":"2.0","id":1,"result":{"session_id":"abc123"}}
```

**eval** - Evaluate Haskell input
```json
{"jsonrpc":"2.0","id":2,"method":"eval","params":{"input":"main"}}
```
Response:
```json
{"jsonrpc":"2.0","id":2,"result":{"status":"success","value":"Hello from Rusholme!"}}
```

**type** - Type-check expression
```json
{"jsonrpc":"2.0","id":3,"method":"type","params":{"input":"main"}}
```
Response:
```json
{"jsonrpc":"2.0","id":3,"result":{"status":"success","type":"IO ()"}}
```

**shutdown** - Shutdown cleanly (explicit quit)
```json
{"jsonrpc":"2.0","id":4,"method":"shutdown","params":{}}
```
Response:
```json
{"jsonrpc":"2.0","id":4,"result":{"status":"ok"}}
```

### REPL Commands

Map existing REPL commands (`:load`, `:type`, `:quit`, etc.) to protocol methods. `:quit` maps to `shutdown`.

## Error Handling & Diagnostics

### Error Response Format
JSON-RPC 2.0 error object:
```json
{"jsonrpc":"2.0","id":1,"error":{"code":-32000,"message":"Runtime error","data":"..."}}
```

Error codes follow JSON-RPC conventions (JSON parsing errors use predefined codes, REPL errors use -32000 application space).

### Diagnostics Integration
The design leverages existing infrastructure:
- `Session` manages diagnostics via `DiagnosticCollector`
- `JsonRenderer` (from `src/diagnostics/json.zig`) serializes diagnostics to JSON
- Protocol layer wraps existing error handling
- Diagnostics include source spans, severities, notes (reuse existing schema)

## Architecture

### Single Binary, Dual Modes
- `rhc repl` - native REPL
  - Default: interactive mode
  - `--server` flag: server mode, stdin/stdout JSON-RPC
- `rhc repl.wasm` - WASM REPL (via wasmtime)
  - Same interface via CLI args
  - Same protocol behavior
  - `--server` flag for consistent operation

### Components
```
ReplServer (src/repl/server.zig)
├── Protocol handler (JSON-RPC parsing/responses)
├── Session manager (wraps existing Session)
└── IO backend (stdin line reader, stdout writer)

JsonRpc (src/repl/jsonrpc.zig)
├── Request parsing
├── Response formatting
└── Error handling
```

### Integration Points
The new server layer wraps existing REPL infrastructure:
- `Session.eval()` returns `EvalResult` with status/value
- `Protocol.evaluate()` wraps this for browser bridge
- New `Server` layer wraps same flow with JSON-RPC

## Implementation Notes

### File Structure
- `src/repl/server.zig` - New: JSON-RPC server handler
- `src/repl/jsonrpc.zig` - New: JSON-RPC 2.0 parsing/writing
- `src/repl/exports.zig` - Update: preserve WASM browser bridge, add server entry point
- `src/main.zig` - Update: CLI argument handling (`--server` flag)

### Testing Approach
- Integration tests drive server via stdin/stdout
- Server mode works with both native and WASM (via wasmtime)
- Tests verify protocol behavior (correct JSON, error handling, diagnostics)

## Usage

### Native REPL (server mode)
```bash
rhc repl --server
```

### WASM REPL (server mode)
```bash
wasmtime repl.wasm --dir=. -- --server
```

### Example client (simple test harness)
```bash
echo '{"jsonrpc":"2.0","id":1,"method":"init","params":{}}' | rhc repl --server
echo '{"jsonrpc":"2.0","id":2,"method":"eval","params":{"input":"main"}}' | rhc repl --server
```

## References
- JSON-RPC 2.0 Specification
- docs/decisions/0006-repl-architecture.md
- docs/decisions/0007-repl-protocol.md
- src/diagnostics/json.zig (existing diagnostic JSON renderer)

# Decision 0007: REPL Protocol with Structured Responses

## Context

Decision 0006 defined the REPL architecture with separate execution engines (native and WASM). For browser/xterm.js integration, we needed to separate business logic from presentation layers in a testable way.

## Decision

Introduce a protocol interface (`src/repl/protocol.zig`) that provides structured API:
- `evaluate(allocator, session, input) -> ProtocolResult`
- `getDiagnostics(session) -> []Diagnostic`

UI layers call the protocol; they differ only in rendering:
- Native CLI: uses stdout/stderr with colors
- Browser: calls WASM exports, renders via xterm.js

## Consequences

- Protocol tests apply to both backends
- Backend-agnostic: UI doesn't care about native vs WASM
- Clean interfaces: Structured responses are explicit and testable
- Session state and pipeline remain unchanged

## Implementation Notes

The Status enum uses `failed` instead of `error` to avoid Zig reserved keyword conflicts:
```zig
pub const Status = enum {
    success,
    failed,  // Not 'error' (reserved keyword)
    silent,
};
```

The existing WASM exports (`repl_init`, `repl_evaluate`, etc.) in `src/repl/exports.zig` are unchanged to maintain compatibility with the website. The protocol layer is used internally by `cli.zig` and could be used by future WASM drivers.

## References

- docs/plans/2026-03-04-repl-protocol-design.md
- docs/plans/2026-03-04-repl-protocol-implementation.md

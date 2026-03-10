# Issue #494: Browser REPL UnboundVariable after `:load`

## Problem

When loading a Haskell file via `:load` in the browser REPL, the file appears
to load successfully ("Loaded: hello.hs"), but subsequent commands referencing
definitions from that file fail with a bare `UnboundVariable` error.

## Investigation Summary

The Zig REPL logic is correct. All 826 native tests pass, and the actual
`repl.wasm` binary works perfectly when tested programmatically in Node.js.
The `:load` → `main` flow, multi-definition accumulation, and cross-session
variable resolution all function as designed.

The bug is browser-specific and stems from two causes:

1. **Stale WASM binary** — `fetch("repl.wasm")` has no cache-busting, so the
   browser may serve an outdated binary even after rebuilding with
   `website-dev`.
2. **Opaque error reporting** — runtime errors from the GRIN evaluator
   (e.g. `UnboundVariable`) are displayed as bare `@errorName` strings with
   no context about which variable is unbound.

## Proposed Changes

### 1. Cache-busting for `repl.wasm`

In `website/template.html`, append a timestamp query parameter to the WASM
fetch URL so the browser always loads the freshly built binary:

```javascript
fetch("repl.wasm?v=" + Date.now())
```

### 2. Improved error display in browser

In `website/template.html`, when the REPL returns an error status:
- Prefix errors with "Error:" for clarity
- Display any diagnostics from the JSON response

### 3. Improved error context in protocol layer

In `src/repl/protocol.zig`, when `session.eval()` throws, include the input
that caused the error in the message so users can see what failed.

### 4. Regression tests

Two new tests in `tests/repl/repl_tests.zig`:
- `test "repl: GrinEngine — load then evaluate main"` — directly tests the
  WASM merge path with GrinEngine
- `test "repl: load file body then evaluate main"` — tests via
  `protocol.evaluate`

## Scope

No changes to the GRIN evaluator, pipeline, session accumulation, engine
logic, build system, or Nix flake. These are all correct.

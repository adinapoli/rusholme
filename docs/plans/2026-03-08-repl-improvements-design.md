# REPL Improvements Design

**Date:** 2026-03-08
**Branch:** `feature/repl-consolidation-with-tests`

## Overview

Four improvements to the Rusholme REPL on the current consolidation branch:

1. Multi-line editing via `:{ ... :}` (GHCi-compatible)
2. Fix stale `repl.wasm` in the website build
3. `:load` command to load `.hs` files from disk (and via file picker in browser)
4. Comprehensive end-to-end tests at both protocol and CLI levels

## 1. Multi-line `:{ ... :}` Support

### Problem

`stripMultilineDelimiters` exists in `eval.zig` but is never invoked from
`cli.zig`. The CLI loop processes one line at a time and treats `:{` as an
unknown command. The browser JS similarly sends each Enter-press as a
separate evaluation with no accumulation.

### Design

**CLI (`cli.zig`):**

Add an `InputMode` enum to track CLI state (avoiding boolean blindness):

```zig
const InputMode = enum {
    normal,
    multiline,
};
```

Loop state gains `mode: InputMode` and `multiline_buf: ArrayList(u8)`.

- Line `:{` (trimmed) switches to `.multiline`, prompt becomes `rusholme| `.
- Subsequent lines are appended to `multiline_buf` with `\n` separators.
- Line `:}` (trimmed) in `.multiline` mode joins the buffer, evaluates, resets to `.normal`.
- `:quit` or Ctrl+D during multiline cancels the block, returns to `.normal`.

The CLI builds inner content directly — no need to call `stripMultilineDelimiters`.

**Browser JS (`template.html`):**

Mirror with `inputMode: 'normal' | 'multiline'` and a `multilineBuffer` array.

- `:{` enters multiline mode, prompt changes to `| `.
- `:}` seals the block: content is wrapped in `:{...:}` and sent to
  `replBridge.evaluate()` so the WASM-side `stripMultilineDelimiters` handles it.
- Ctrl+D cancels multiline mode.

### Files Changed

- `src/repl/cli.zig` — multiline accumulation in the main loop
- `website/template.html` — JS multiline state machine

## 2. Fix Stale `repl.wasm`

### Problem

`build.js` copies `zig-out/bin/repl.wasm` into the website directory, but
there is no single command that rebuilds the Zig binary first. Users must
remember to run `zig build` before `npm run build`.

### Design

Add a `website/dev.sh` script:

```bash
#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
zig build
cd website
node build.js
npx serve .
```

This is the simplest correct solution — no over-engineering.

### Files Changed

- `website/dev.sh` — new convenience script

## 3. `:load` Command

### Problem

Neither CLI nor browser REPL can load a `.hs` file from disk.

### Design

**CLI (`cli.zig`):**

- Add `:load <path>` (alias `:l`) to `handleCommand`.
- Read file via `std.fs.cwd().openFile()` + `readToEndAlloc()`.
- Feed contents through `protocol.evaluate()` as a single input (same path
  as declarations — the session wraps it as a module).
- On success: print `Loaded: <path>`. On failure: show diagnostics.
- Path resolved relative to CWD, matching GHCi.

**Browser JS (`template.html`):**

- `:load` in the terminal opens a `<input type="file">` picker.
- File contents read via `FileReader` API into memory.
- Contents sent to `replBridge.evaluate()`.
- On success: print `Loaded: <filename>`.

**Session layer:** No changes needed — `processInput` already handles
multi-declaration input.

### Files Changed

- `src/repl/cli.zig` — `:load` / `:l` command handler
- `website/template.html` — file picker integration

## 4. End-to-End Tests

### A. Protocol-Level Tests (`tests/repl/repl_tests.zig`)

Extend existing suite with:

- Multiline blocks (joined content evaluated correctly)
- `:load` of a temp `.hs` file, verify declarations available
- Error recovery (bad input then good input, session intact)
- Redefinition of functions (new definition wins)
- Chained expressions depending on prior declarations
- Edge cases: empty input, whitespace-only

### B. CLI E2E Tests (new: `tests/repl/cli_e2e_tests.zig`)

Spawn `rhc repl` as a child process, pipe stdin, capture stdout/stderr,
assert on output. Tests the real user experience.

Scenarios:

- Basic expression evaluation (`42` -> `42`)
- `:help` (expect help text)
- `:quit` (expect clean exit, code 0)
- Multiline block (`:{`, `f x = x`, `:}`, `f 99` -> `99`)
- `:load` with a temp file
- Error recovery (bad expression, then good one)
- EOF (close stdin, expect clean exit)

**Infrastructure:**

- Each test spawns a `std.process.Child` running the REPL binary.
- Helper functions: `sendLine()`, `expectOutputContaining()` with timeout.
- Each test gets its own subprocess for full isolation.
- New build step `cli-e2e-tests` in `build.zig`.

### Files Changed

- `tests/repl/repl_tests.zig` — additional protocol-level tests
- `tests/repl/cli_e2e_tests.zig` — new CLI e2e test file
- `build.zig` — new test step for CLI e2e tests

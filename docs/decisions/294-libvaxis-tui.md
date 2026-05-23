# Decision 294: Evaluate libvaxis for Future REPL UX

**Status:** Deferred (keep replxx for now; revisit at M4)
**Date:** 2026-05-23
**Issue:** #294

## Context

The REPL is already implemented and uses the C library `replxx` via
`src/repl/line_editor.zig`:

- Line editing with history.
- Completion callback (with colour hints).
- Hint callback.
- Multi-line accumulation via the REPL session layer (not the line editor).

The REPL is functional today (`rhc repl` plus a WASM JSON-RPC server
mode). The M4 milestone speaks to *expanded* REPL UX — syntax highlighting
on the current line, autocompletion UI, possibly side-panel widgets, etc.
Issue #294 asks whether [libvaxis][] is a better foundation for that
expansion.

[libvaxis]: https://github.com/rockorager/libvaxis
[replxx]: https://github.com/AmokHuginnsson/replxx

## What libvaxis is

| Property | Value |
|----------|-------|
| Scope | Full TUI library: low-level cell control plus a Flutter-style framework (`vxfw`) |
| Language | Pure Zig (99.9 %) — only `uucode` as a notable dep |
| Zig version | Targets 0.16 (matches our `flake.nix`) |
| Platforms | macOS, Windows, Linux/BSD |
| Widgets | Buttons, TextInput, borders, Text; framework is extensible |
| Modern terminal | RGB, hyperlinks, kitty keyboard protocol, image protocol, synchronised output |
| Terminfo | Not used — feature-detected via terminal queries |
| Maturity | v0.5.1 (Nov 2024), 1.8k stars, 7 releases |
| License | MIT |

It is not a drop-in replacement for `replxx`. Specifically, libvaxis does
*not* ship "single-line editor with completion / hint / history" as a
pre-built widget — consumers compose that from `TextInput`, the event
loop, and their own data model.

## What we'd gain

1. **Pure-Zig stack.** Drop the C build-time dep on replxx (currently
   pulled from Nix). Removes one C↔Zig bridge from `line_editor.zig`.
2. **Modern terminal features.** RGB syntax highlighting on the input
   line, kitty keyboard protocol, mouse — none of which `replxx` reaches
   without grafting on extra code.
3. **TUI room to grow.** If the REPL evolves into something with side
   panels (type info, doc preview, browser of in-scope identifiers),
   libvaxis already has the primitives.

## What we'd pay

1. **Reimplement the editor on top of `TextInput`.** History navigation,
   completion popup, hint rendering, multi-line state, paste handling —
   all currently provided by `replxx`. This is real work and is
   load-bearing for the existing CLI E2E tests (`tests/repl/cli_e2e_tests.zig`).
2. **Event-loop integration.** Our REPL session is `readLine`-shaped; the
   `vxfw` framework is event-loop-shaped. We'd need a small thread / mode
   adapter or restructure the session layer.
3. **Risk on the WASM-REPL path.** The browser REPL talks JSON-RPC to a
   wasm32-wasi build and does *not* drive a terminal. libvaxis is not
   relevant for that path. Migration must not regress it.

## Evaluation against the issue's deliverables

| Deliverable | Status |
|-------------|--------|
| Build and test libvaxis capabilities | Library evaluated from documentation; no prototype yet. |
| Evaluate `TextInput` widget for REPL use case | `TextInput` is the right primitive but does not cover completion/hint/history out of the box. |
| Assess performance and memory footprint | Pure Zig, no terminfo, synchronised output. No measured numbers; expected to be on par with or better than `replxx` for our usage. |
| Document integration plan for future REPL | Below. |

## Integration plan (if/when adopted)

This is the plan we'd follow at M4 if and only if the M4 REPL scope grows
beyond what `replxx` can do gracefully:

1. Add libvaxis via `build.zig.zon`.
2. Introduce `src/repl/line_editor_vaxis.zig` alongside the existing
   `line_editor.zig` (replxx). Both implement the same internal trait:
   `init`, `prompt`, `readLine`, `addHistory`, `setCompletionCallback`,
   `setHintCallback`.
3. Build a `LineInput` widget over `vxfw.TextInput` that wires completion
   and hints to the existing callbacks. Reuse our session's history
   buffer; do not depend on a vaxis-internal store.
4. Gate the switch behind a build option (`-Drepl-frontend=vaxis|replxx`)
   while the CLI E2E suite is migrated to drive the new editor.
5. Once parity is verified, delete `line_editor.zig` and the replxx Nix
   dependency. The WASM-REPL path is unaffected.

## Recommendation

**Defer.** Keep `replxx` as long as the REPL UX requirements stay at
"line editor + history + completion + hint", because `replxx` provides
that as a single, well-tested unit.

Move to libvaxis when at least one of these becomes true:

- We want inline syntax highlighting on the current input line.
- We want a multi-pane REPL (input area + scope/type-info panel).
- The replxx Nix dependency becomes a portability problem (it has not).

When that day comes, follow the integration plan above. Until then, the
right work is on the REPL *semantics* (multiline `:{ / :}`, `:type`
output, completion sources), not on the editor substrate.

## Follow-ups

- None required for #294 itself.
- The plan in this doc is the seed for whatever implementation issue
  spawns this work at M4.

## References

- [libvaxis][] — TUI library.
- [replxx][] — current REPL line editor.
- `src/repl/line_editor.zig` — current integration point.
- Issues #75-76 — REPL implementation context.

# REPL Line Editor Design

**Date:** 2026-03-26
**Issue:** #76 — Implement REPL auto-completion and multi-line input
**Status:** Approved

---

## Goal

Extend the native `rhc repl` with beautiful line editing — tab completion,
inline hints, live syntax highlighting, and persistent history — surpassing
GHCi's interactive experience.

---

## Scope

This design covers only the **native TUI** (`src/repl/cli.zig` and a new
`src/repl/line_editor.zig`). The WASM REPL (`repl_wasm_main.zig`) and the
JSON-RPC server mode (`src/repl/server.zig`) are unaffected — they are
separate presentation layers that do not use terminal line editing.

---

## Library Choice: replxx (C API)

[replxx](https://github.com/AmokHuginnsson/replxx) is a C++ library that
exposes a complete C API (`replxx.h`). It provides:

- History navigation (up/down arrows, Ctrl+R reverse search)
- Tab completion with colored entries
- Inline hints (ghost text)
- Live syntax highlighting of the input line
- Unicode support
- Persistent history files

It is available in nixpkgs as `pkgs.replxx` and ships `libreplxx.so` with a
pure C header — no C++ in the Zig call sites.

**Alternatives considered:**
- *linenoise* — too minimal (no hints, no color, no Unicode)
- *pure Zig terminal handling* — contradicts DESIGN.md mantra #2 ("leverage
  battle-tested C libraries") and represents weeks of unnecessary work

---

## Module Structure

### New: `src/repl/line_editor.zig`

A native-only module that wraps the replxx C API behind a clean Zig struct.
It is only ever imported by `cli.zig` and is never compiled into the WASM build.

```zig
pub const LineEditor = struct {
    pub fn init(
        allocator: Allocator,
        session: *Session,
        history_path: []const u8,
    ) !LineEditor

    pub fn deinit(self: *LineEditor) void

    /// Read the next line. Returns null on EOF.
    pub fn readLine(self: *LineEditor, prompt: []const u8) !?[]const u8
};
```

Three C-compatible callbacks are registered at `init` time and delegate
immediately to pure Zig helper functions (testable independently):

| Callback | Helper | Purpose |
|---|---|---|
| `replxx_set_completion_callback` | `completionsFor` | Tab candidates |
| `replxx_set_hint_callback` | `hintsFor` | Ghost-text suffix |
| `replxx_set_highlighter_callback` | `highlightLine` | Input colorization |

All callbacks receive a `*Session` via the `userData` void pointer.

### Modified: `src/repl/cli.zig`

The hand-rolled `readLine()` function and its byte-by-byte loop are removed.
The main `run()` loop becomes:

```zig
const history_path = try historyFilePath(alloc);
defer alloc.free(history_path);

var editor = try LineEditor.init(alloc, &session, history_path);
defer editor.deinit();

while (try editor.readLine(prompt)) |line| {
    // ... existing dispatch logic unchanged ...
}
```

No `is_wasi` guards are needed — `cli.zig` is already native-only by
architecture. The WASM build uses `repl_wasm_main.zig` as its root and never
references `cli.zig` or `line_editor.zig`.

---

## Completion

Tab completion dispatches on the current input prefix:

| Input context | Source | Display color |
|---|---|---|
| Starts with `:` | Static command list | Cyan |
| `:load ` / `:l ` prefix | `std.fs` directory scan | White |
| Otherwise | `Session.rename_env` bound names | Bright green (constructors, capitalized) / White (functions) |

Static command list: `:quit`, `:q`, `:type`, `:t`, `:load`, `:l`, `:help`,
`:h`, `:?`, `:{`, `:}`.

---

## Hints

Replxx displays a dim gray suffix after the cursor as the user types:

- For `:` prefixes: remainder of the first matching command
  (e.g. `":t"` → hint `"ype"`)
- For identifiers: suffix of the first matching in-scope name from
  `Session.rename_env`

---

## Highlighting

A character-by-character scan over the current input line. No parser —
token-level recognition only.

| Token | Color |
|---|---|
| REPL command (`:word`) | Cyan |
| Keyword (`let`, `in`, `where`, `data`, `case`, `of`, `if`, `then`, `else`, `do`) | Blue |
| Constructor / type (leading uppercase) | Bright green |
| Number literal | Yellow |
| String literal (`"..."`) | Yellow |
| Operator (`->`, `::`, `=`, `\`, `+`, `-`, `*`, …) | Magenta |
| Other | Default |

---

## History

| Property | Value |
|---|---|
| File path | `~/.rhc/repl_history` |
| Directory | `~/.rhc/` — created at init if absent |
| Load | `replxx_history_load` at `init`; silent if file missing |
| Save | `replxx_history_save` at `deinit` |
| Max entries | 1000 |
| Deduplication | `replxx_set_unique_history(true)` |

`~/.rhc/` is the shared hidden directory for Rusholme user data, reusable
for future compiler configuration and caches.

---

## Build Integration

### `build.zig`

Added to the native executable target only:

```zig
mod.linkSystemLibrary("replxx", .{});
mod.linkLibCpp();
```

`linkLibCpp()` is required because replxx is a C++ library. The WASM build
target does not link replxx.

### `flake.nix`

Added to the default dev shell `buildInputs`:

```nix
pkgs.replxx
```

---

## Testing

| What | How |
|---|---|
| `completionsFor` | Unit tests in `line_editor.zig` using `std.testing` |
| `hintsFor` | Unit tests in `line_editor.zig` using `std.testing` |
| `highlightLine` | Unit tests in `line_editor.zig` using `std.testing` |
| `LineEditor` end-to-end | Manual smoke test (requires real TTY) |

Manual smoke test checklist (for PR description):
1. `rhc repl` launches with prompt `rusholme> `
2. Tab after `:` cycles through REPL commands
3. Tab on a partial identifier completes from session scope
4. Tab after `:load ` completes filesystem paths
5. Ghost hint appears while typing a command or identifier
6. Keywords and constructors are colored correctly
7. Up/Down arrows navigate history within session
8. `~/.rhc/repl_history` exists and is populated after exit
9. History survives across REPL restarts

---

## References

- Issue #76: Implement REPL auto-completion and multi-line input
- Issue #15: Epic — REPL / interactive mode
- `docs/decisions/0006-repl-architecture.md` — REPL architecture
- `docs/proxy/repl_protocol.md` — protocol / presentation layer separation
- replxx C API: `replxx.h` in nixpkgs `pkgs.replxx`

# Design: Migrate rhc CLI to zig-clap

**Date:** 2026-04-07
**Issue:** #292
**Branch:** `llm-agent/issue-292`
**Status:** Approved

## Context

`src/main.zig` and `src/packages/pkg_cmd.zig` currently dispatch subcommands by
comparing `args[0]` with `std.mem.eql`. Flags are extracted by manual `while`
loops. Help strings are hand-written and duplicated. This design replaces both
dispatchers with zig-clap using a consistent two-stage pattern.

## Scope

Four files change; all others (including `pkg_cmd.zig`'s implementation
functions and their tests) are untouched.

| File | Change |
|------|--------|
| `build.zig.zon` | Add `zig-clap` dependency |
| `build.zig` | Wire `clap` module into `rhc` executable |
| `src/main.zig` | Replace manual dispatch with zig-clap two-stage pattern |
| `src/packages/pkg_cmd.zig` | Replace `cmdPkg` dispatcher; impl functions unchanged |

## Architecture

### Pattern

A single `clap.args.SliceIterator` wraps the raw args slice. Every dispatch
level uses `clap.parseEx` with `terminating_positional = 0` to consume the
subcommand name and stop, then passes the same iterator to the next stage.

```
args slice
  └─ clap.args.SliceIterator
       ├─ stage-1 parse (terminating_positional=0) → subcommand name
       └─ stage-2 parse (per-subcommand params)    → typed flags + positionals
```

### Top-level dispatch (`src/main.zig`)

```
main
  → init.minimal.args.toSlice() → skip argv[0]
  → SliceIterator{ .args = user_args }
  → parseEx(top_params, &it, .{ .terminating_positional = 0 })
  → switch positionals[0]:
      "parse" | "check" | "core" | "grin" | "ll"
          → parseEx(file_params, &it) → positionals[0] = file_path
            (all five share one `file_params` declaration: `-h/--help` + `<file.hs>`)
      "repl"
          → parseEx(repl_params, &it) → args.server (bool flag)
      "build"
          → parseEx(build_params, &it)
              flags:  --backend <str>, -o <str>, --package-db <str> (multi), --repl
              positionals: <file.hs>...
      "pkg"
          → cmdPkg(alloc, io, &it)
      else → clap diagnostic + exit(1)
```

Top-level params include `-h/--help` and `--version`. `clap.help()` replaces
the hand-written `printUsage()` function entirely.

### `pkg` dispatch (`src/packages/pkg_cmd.zig`)

`cmdPkg` signature changes:
```zig
// Before
pub fn cmdPkg(alloc: std.mem.Allocator, io: Io, args: []const []const u8) !void

// After
pub fn cmdPkg(alloc: std.mem.Allocator, io: Io, it: *clap.args.SliceIterator) !void
```

Internal dispatch:
```
cmdPkg
  → parseEx(pkg_params, it, .{ .terminating_positional = 0 })
  → switch positionals[0]:
      "list"       → cmdPkgList(...)
      "describe"   → parseEx(describe_params, it) → positionals[0]
      "install"    → parseEx(install_params, it)  → positionals[0]
      "unregister" → parseEx(unreg_params, it)    → positionals[0]
      "check"      → cmdPkgCheck(...)
      else         → clap diagnostic + exit(1)
```

`writePkgUsage()` and `writePkgStderr()` helper functions are deleted.
`clap.help()` generates pkg-level and per-subcommand help.

## Data Flow Details

### `--package-db` (multi-value)

zig-clap accumulates repeated `--package-db` flags automatically into a slice
when the param is declared with `...` multiplicity. The manual `while` loop
collecting them is deleted.

### `--backend` validation

Stays post-parse: `parseBackendKind(res.args.backend orelse "native")` returns
`null` for unknown values; the caller prints the error and exits. No change to
validation logic.

### `--repl` flag on `build`

Boolean flag in `build_params`. zig-clap sets it to `true` if present.

## Error Handling

| Scenario | Before | After |
|----------|--------|-------|
| Missing required positional | Manual check + hand-written message | zig-clap `Diagnostic` → `stderr` + `exit(1)` |
| Unknown flag | Falls through to "unknown command" | zig-clap catches automatically with diagnostic |
| Unknown subcommand | Manual `stderr` + exit | Same, via zig-clap diagnostic on `terminating_positional` mismatch |
| Unknown `--backend` value | Manual switch | Unchanged — post-parse validation |

In all error paths we print the diagnostic to stderr and call `std.process.exit(1)`,
matching current behaviour.

## Help Generation

Every `parseParamsComptime` block includes `-h, --help`. Calling
`clap.help(stderr, clap.Help, &params, .{})` produces aligned, formatted output
automatically. The following are deleted:
- `printUsage()` in `main.zig`
- `writePkgUsage()` in `pkg_cmd.zig`
- `writePkgStderr()` in `pkg_cmd.zig`

## Testing

- All unit tests in `pkg_cmd.zig` pass unchanged — they call `cmdPkgList`,
  `cmdPkgDescribe`, etc. directly, bypassing `cmdPkg`.
- All e2e tests pass unchanged — they invoke the binary end-to-end.
- No new tests are added: zig-clap's parsing is tested by zig-clap itself;
  the logic being replaced is pure string dispatch with no business logic.

## Dependency Addition

```bash
zig fetch --save git+https://github.com/Hejsil/zig-clap#master
```

In `build.zig`:
```zig
const clap = b.dependency("clap", .{});
rhc_exe.root_module.addImport("clap", clap.module("clap"));
```

## What Is Not Changing

- All `cmdParse`, `cmdCheck`, `cmdCore`, `cmdGrin`, `cmdLl`, `cmdBuild`,
  `cmdRepl` implementation functions — signature and body unchanged
- All `cmdPkgList`, `cmdPkgDescribe`, `cmdPkgInstall`, `cmdPkgUnregister`,
  `cmdPkgCheck` implementation functions and their tests — untouched
- Exit codes and stderr/stdout routing — unchanged

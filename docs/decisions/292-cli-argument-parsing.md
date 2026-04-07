# Decision 292: CLI Argument Parsing Library

**Status:** Accepted — zig-clap
**Date:** 2026-04-07
**Issue:** #292

## Context

`rhc` currently parses arguments by hand: `args[0]` is compared against
subcommand strings with `std.mem.eql`, and flags are extracted by iterating
`args[1..]` manually.  This is already fragile (three subcommands have ad-hoc
`--backend` / `-o` / `--package-db` extraction) and will not scale to the full
CLI described in issues #142 and #145:

- Multiple subcommands: `parse`, `check`, `core`, `grin`, `ll`, `build`,
  `repl`, `pkg` (with its own subcommands)
- Complex flags: `--output`, `--backend`, `--package-db` (repeatable),
  `--optimize`, …
- Consistent `--help` output for every subcommand
- Shell completion (bash/zsh/fish) tracked in #145

## Candidates

Three Zig-native libraries were evaluated.

### 1. zig-clap (Hejsil/zig-clap)

| Criterion | Result |
|-----------|--------|
| Zig 0.16-dev support | **Explicit** — `minimum_zig_version = "0.16.0-dev.2261+d6b3dd25a"` |
| Last commit | March 19, 2026 |
| GitHub stars | 1 511 |
| Subcommand support | Two-stage: parent parser stops at `terminating_positional`, iterator handed off to sub-handler |
| Flag ergonomics | Compile-time DSL (`parseParamsComptime`); typed result struct, no runtime type checks |
| Help generation | `clap.help()` / `clap.usage()` from same DSL — no duplication |
| Shell completion | **Not built-in** — must be authored manually |
| External deps | None |
| License | MIT |
| Maintenance | Actively maintained, tracks Zig master |

**Subcommand example (two-stage pattern):**
```zig
const main_params = comptime clap.parseParamsComptime(
    \\-h, --help     Display help.
    \\<subcommand>
);
// first stage
var res = try clap.parse(clap.Help, &main_params, clap.parsers.default, .{
    .diagnostic = &diag,
    .terminating_positional = 0,
});
// second stage
if (std.mem.eql(u8, res.positionals[0], "build")) {
    try cmdBuild(it);  // pass remaining iterator
}
```

---

### 2. yazap (PrajwalCH/yazap)

| Criterion | Result |
|-----------|--------|
| Zig 0.16-dev support | **Unknown** — v0.7.0 (latest stable) supports up to 0.15.2; `main` branch targets Zig master but not verified for 0.16-dev |
| Last commit | February 1, 2026 |
| GitHub stars | 206 |
| Subcommand support | Hierarchical `addSubcommand()` with `ArgMatches` |
| Flag ergonomics | Builder API (`Arg.booleanOption`, `Arg.singleValueOption`); readable but more verbose |
| Help generation | Automatic; `app.displayHelp()` |
| Shell completion | Not built-in |
| External deps | None |
| License | MIT |
| Maintenance | Active; v0.7.0 introduces API renames (breaking change pattern) |

**Concern:** Cannot confirm Zig 0.16-dev compatibility. Rusholme's
`minimum_zig_version` is `0.16.0-dev.2565+684032671`; adopting a library that
is only tested against 0.15.2 would create an unverified dependency.

---

### 3. zli (xcaeser/zli)

| Criterion | Result |
|-----------|--------|
| Zig 0.16-dev support | **Unknown** — CI tests only 0.15.2 |
| Last commit | January 27, 2026 |
| GitHub stars | 314 |
| Subcommand support | Yes — `cmd.addCommand()` with `CommandContext` |
| Flag ergonomics | Type-safe `ctx.flag("name", Bool/Int/String)` |
| Help generation | `--help` / `-h` automatic |
| Shell completion | Not built-in |
| External deps | None |
| License | MIT |
| Maintenance | Active; v4.3.0 released November 2025 |

**Concern:** "Persistent flags" (inherited by subcommands) listed as unimplemented
in the feature checklist. Rusholme needs `--package-db` to be available on the
`build` subcommand alongside top-level flags. Same 0.16-dev compatibility gap
as yazap.

---

## Comparison Matrix

| Criterion | zig-clap | yazap | zli |
|-----------|----------|-------|-----|
| Zig 0.16-dev confirmed | **Yes** | No | No |
| Stars (adoption) | **1 511** | 206 | 314 |
| Subcommand support | Two-stage | Hierarchical | Hierarchical |
| Help auto-generated | Yes | Yes | Yes |
| Shell completion | No | No | No |
| Persistent / inherited flags | Manual | Yes | **No (open issue)** |
| Maintenance cadence | Monthly | Bi-monthly | Quarterly |
| API stability | Stable | Breaking changes between minor versions | Stable |

## Analysis

### Zig version compatibility is the hard gate

Rusholme's `build.zig.zon` declares `minimum_zig_version = "0.16.0-dev.2565+…"`.
Adopting a library that has never been tested against 0.16-dev means every Zig
update becomes a potential silent breakage. zig-clap is the only candidate that
explicitly declares and tests 0.16-dev compatibility — it is a hard requirement.

### Adoption and ecosystem health

zig-clap has 7× more stars than its nearest competitor and is the de-facto
standard CLI library in the Zig ecosystem. Bug reports surface quickly, fixes
land quickly, and the probability of the library being maintained across multiple
Zig releases is substantially higher.

### API ergonomics

The compile-time `parseParamsComptime` DSL is idiomatic Zig — it leverages
`comptime` to derive a typed result struct, eliminating runtime type assertions.
The two-stage subcommand pattern requires ~15 lines of boilerplate for dispatch,
but this is a one-time cost in `main.zig`.

### Shell completion

None of the three libraries provide shell completion. This is a known gap
tracked in issue #145. The approach recommended there (having `rhc` emit
completion scripts itself, similar to GHC/optparse-applicative) is independent
of which parsing library is chosen and remains viable with zig-clap.

### Current `main.zig` migration

The existing hand-rolled parser is already using the same structural pattern
that zig-clap formalises (top-level dispatch on `args[0]`, per-subcommand flag
extraction). Migration is a straightforward refactor: replace `std.mem.eql`
chains with `parseParamsComptime` declarations and a single dispatch block.

## Recommendation

**Adopt zig-clap.**

### Rationale

1. **Only library with confirmed Zig 0.16-dev support** — this is a hard
   requirement given `minimum_zig_version`.
2. **Most widely adopted** — reduces maintenance risk and improves the
   probability of long-term support.
3. **Clean, idiomatic API** — compile-time DSL aligns with Zig's philosophy;
   typed result struct prevents accidental option misuse.
4. **Auto-generated help** — eliminates the current hand-written usage string
   in `main.zig` and keeps flags and help in sync automatically.
5. **No external dependencies** — fits Rusholme's minimalist dependency policy.
6. **MIT license** — compatible with the project.

### Migration plan

1. Add zig-clap to `build.zig.zon` via:
   ```
   zig fetch --save git+https://github.com/Hejsil/zig-clap#master
   ```
2. Wire the module in `build.zig`:
   ```zig
   const clap = b.dependency("clap", .{});
   exe.root_module.addImport("clap", clap.module("clap"));
   ```
3. Replace the manual `args[0]` dispatch in `src/main.zig` with zig-clap's
   two-stage subcommand pattern.
4. Move per-subcommand flag parsing (`--backend`, `-o`, `--package-db`) into
   per-handler `parseParamsComptime` declarations.
5. Delete the hand-written `printUsage()` function — zig-clap generates it.

This migration is tracked as the implementation work for issue #292 itself.

### Shell completion

No library provides this automatically. Implement per issue #145 as a
post-zig-clap follow-up: add `rhc --bash-completion-script` / `--zsh-…` /
`--fish-…` flags that emit pre-built completion scripts. This pattern does not
depend on the parsing library choice.

## References

- zig-clap repository: https://github.com/Hejsil/zig-clap
- yazap repository: https://github.com/PrajwalCH/yazap
- zli repository: https://github.com/xcaeser/zli
- Issue #142: rhc CLI implementation
- Issue #145: Shell completion for rhc CLI
- Current CLI: `src/main.zig`

# Decision 291: Evaluate Benchmarking Libraries (zBench, poop)

**Status:** Accepted (use both, at different layers)
**Date:** 2026-05-23
**Issue:** #291

## Context

Rusholme needs benchmarking infrastructure for three distinct things:

1. **Micro-benchmarks** — measure the cost of individual passes (lexer,
   parser, renamer, typechecker, GRIN translation, LLVM codegen) on
   representative inputs. Useful for catching regressions in tight inner
   loops.
2. **End-to-end compilation throughput** — `rhc build foo.hs` on a fixed
   corpus, comparing wall-clock and peak RSS between branches.
3. **Generated-code performance** — running compiled programs (a future
   `bench/` corpus) and comparing runtime vs GHC and historical Rusholme
   builds.

These three needs map to two different kinds of tool: an in-process
benchmark library that lives inside `zig build test`, and a CLI runner
that compares whole-command executions.

[zBench]: https://github.com/hendriknielaender/zBench
[poop]: https://github.com/andrewrk/poop

## Candidate: zBench

| Property | Value |
|----------|-------|
| Form factor | Library — call from Zig code inside `test` blocks |
| Zig version | Tracks Zig master with stability branches for 0.12 / 0.13 |
| Packaging | `build.zig` + `build.zig.zon` |
| Output | Text report: runs, mean ± σ, min/max, p75/p99/p995 |
| License | MIT |
| Scope | Micro-benchmarks over repeated iterations (default 2 s budget) |

zBench is a good fit for layer (1). It plugs into the existing
`zig build test` infrastructure, accepts a benchmark function with
`std.mem.Allocator`, and reports the percentile distribution we'd want for
"did this PR regress the parser?". It does *not* measure peak memory or
hardware counters — that's outside its scope.

## Candidate: poop

| Property | Value |
|----------|-------|
| Form factor | CLI tool — runs other binaries and compares them |
| OS support | Linux only (uses `perf_event_open`) |
| Methodology | Hardware perf counters + repeated sampling (default 5 s) |
| Output | Coloured terminal UI; first command = reference, deltas shown |
| License | MIT |

poop is a good fit for layer (2): "does `rhc build` on this corpus get
faster or slower between two branches?" Hardware counters and peak RSS
give us signals that a wall-clock-only library can't. The trade-off is
that poop is Linux-only — it won't help us on macOS CI.

## Evaluation

### Coverage matrix

| Need | zBench | poop |
|------|--------|------|
| (1) micro-benchmarks in test suite | Strong | n/a (CLI-only) |
| (2) end-to-end compile throughput | Awkward (would need test wrappers) | Strong |
| (3) generated-code runtime | Awkward (per-benchmark harness needed) | Strong |
| macOS support | Yes | No (Linux-only) |
| Hardware counters | No | Yes |
| Inside `zig build test` | Native | No (external invocation) |

### Integration cost

- **zBench**: one `build.zig.zon` dependency; a new `bench/` directory with
  `bench_*.zig` files mirroring `tests/*_test_runner.zig`; a new `zig build
  bench` step that runs the benchmark binary. Zero impact on `zig build
  test` (won't run by default).
- **poop**: zero source-tree integration. A small `bench/poop.sh` (or
  `bench/Makefile`) that calls `poop ./before/rhc ./after/rhc ...` against a
  fixed corpus is sufficient. Local-developer / Linux-CI tool, not part of
  the unit-test loop.

### Maintenance

- zBench tracks Zig master; this matches Rusholme's own posture (we are on
  Zig 0.16-dev). Brief breakage windows when both sides update are
  acceptable.
- poop is a stable CLI we don't compile in; version drift is invisible to
  the codebase.

## Recommendation

**Accept both. They occupy non-overlapping layers.**

- Use **zBench** for in-process micro-benchmarks: pass-level performance,
  inner-loop regressions, allocator behaviour for individual passes.
  Land it via a new `bench/` directory and a `zig build bench` step that
  is *not* a dependency of the default `test` step.
- Use **poop** for compare-two-binaries CLI runs: end-to-end compilation
  throughput on a fixed `.hs` corpus, generated-code runtime once the
  benchmark corpus exists. Document the recipe in `bench/README.md`.
  Recognise that this is Linux-only; macOS users will rely on zBench plus
  ad-hoc `time(1)`.

Neither tool overlaps the other. Picking one would force the other layer
to use the wrong shape, which is exactly the failure mode an evaluation
should prevent.

## Follow-ups

The actual implementation of either layer is out of scope for the
research issue. Concrete next steps (file as separate issues when the
respective need becomes urgent):

1. Add `zBench` as a dependency and stand up `bench/lexer_bench.zig`
   covering at least lexing, parsing, and renaming on a fixed `Prelude.hs`
   + a small synthetic large file. Owner: M1+ once parser velocity slows.
2. Curate a small `bench/corpus/` of `.hs` programs (Fibonacci, Ackermann,
   tree-folds) and document the `poop` invocation that compares two `rhc`
   builds on it. Owner: M2+ when generated-code performance starts to
   matter.

## References

- [zBench][] — micro-benchmark library.
- [poop][] — CLI command-comparison tool.
- Issue #62 — test harness setup.
- `docs/decisions/293-string-libraries.md` — same dual-tool pattern
  (different libraries for different layers).

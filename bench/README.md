# Rusholme micro-benchmarks

Small curated set of Haskell programs used to track Rusholme's
mutator/GC performance over time. Run any program through
`scripts/bench.sh` (#758) — hyperfine handles warm-up, runs, and
optional GHC -O2 comparison.

## Programs

| File              | Profile                                                                 |
|-------------------|-------------------------------------------------------------------------|
| `fib_rec.hs`      | Pure compute. No allocation. Isolates call-overhead + Int arithmetic.   |
| `sum_to.hs`       | Tail-style recursion over an Int range. Stresses calls, no allocs.      |
| `build_list.hs`   | Allocates one Cons cell per element; folds the list. Alloc-heavy.       |
| `tree_sum.hs`     | Balanced binary tree of `Node Int Tree Tree`. 2 pointer fields per node — exercises the tracer's per-tag pointer mask (#779). |

## Usage

```sh
# Single program, rhc only (10 runs, 3 warmups, -O2)
scripts/bench.sh bench/build_list.hs

# Compare against GHC -O2
scripts/bench.sh -g bench/build_list.hs

# Export raw timings to JSON for later trend analysis
scripts/bench.sh -j bench/build_list.json bench/build_list.hs
```

Both binaries (`rhc` and, with `-g`, `ghc`) are run through hyperfine
and their stdouts diffed before timing — output divergence aborts the
benchmark with exit code 2.

## Notes

- `scripts/bench.sh` does not currently know about `--rts=arena|immix`.
  To compare backends, run the script once, then compile the same
  source with `./zig-out/bin/rhc build --rts=immix ...` and time
  manually. A `-r arena|immix` flag for the wrapper is a follow-up.

- These benchmarks are intentionally tiny so they stay portable to
  the CI runner without ballooning iteration time. As Rusholme grows
  more language features the suite should grow accordingly — add a
  program (and a row in the table above) for any new performance
  surface that needs ongoing coverage.

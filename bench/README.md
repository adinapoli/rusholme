# Rusholme micro-benchmarks

Small curated set of Haskell programs used to track Rusholme's
mutator/GC performance over time. Run any program through
`scripts/bench.sh` (#758) — hyperfine handles warm-up, runs, and
optional GHC -O2 comparison.

## Programs

| File                | Profile                                                                 |
|---------------------|-------------------------------------------------------------------------|
| `fib_rec.hs`        | Pure compute. No allocation. Isolates call-overhead + Int arithmetic.   |
| `sum_to.hs`         | Tail-style recursion over an Int range. Stresses calls, no allocs.      |
| `build_list.hs`    | Allocates one Cons cell per element; folds the list. Alloc-heavy.       |
| `tree_sum.hs`       | Balanced binary tree of `Node Int Tree Tree`. 2 pointer fields per node — exercises the tracer's per-tag pointer mask (#779). |
| `binary_trees.hs`   | Alloc-heavy tree create + destroy. Short-lived allocation, GC stress.   |
| `rose_tree.hs`      | Rose tree traversal. Variable-arity children, less regular than binary.|
| `mergesort.hs`      | Merge sort. Comparison + allocation of intermediate lists.             |
| `fannkuch.hs`       | Prefix reversal on a list. Pattern matching + list manipulation.       |
| `fasta.hs`          | String concatenation (append-heavy). Quadratic list-append pattern.   |
| `knucleotide.hs`    | BST frequency counting. Comparison + lookup + update of a search tree.|
| `regex_dna.hs`      | State machine dispatch. Multi-branch pattern-match overhead on small ADTs. |
| `reverse_complement.hs` | List reversal + per-element complement. Pattern matching + allocation. |
| `pidigits.hs`       | GCD inner loop. Tight arithmetic recursion, no allocation.            |
| `nbody_simple.hs`   | Newton's method (isqrt) in a tight loop. Numerical + recursive.       |
| `mandelbrot.hs`     | Mandelbrot escape iteration, fixed-point Int arithmetic. Compute-bound. |
| `spectral_norm.hs`  | Matrix-vector multiply (fixed-point). Nested recursive loops.          |
| `lazy.hs`           | Call-by-need thunk evaluation. Tests thunk skip/force/sharing overhead.|
| `nsieve.hs`         | **Sieve of Eratosthenes.** Sequential list filtering — removes multiples of each prime. Different from knucleotide (BST): flat linear marking/filtering pattern. |
| `tak.hs`            | **Takeuchi function.** 3-way deep recursion (unlike fib's 2-way). Enormous call tree with nested recursive calls. Pure compute, no allocation. |
| `queens.hs`         | **N-Queens.** Backtracking search with early pruning. Non-uniform control flow, building/discarding partial solutions. Tests different iteration pattern than any other bench. |
| `matmul.hs`         | **Matrix-matrix multiply.** Dense triple-nested loops with index-based list access. Different from spectral_norm (sparse matrix-vector). |
| `hof_chain.hs`      | **Higher-order function chains.** Map + fold with partially applied closures (addN k). Tests closure allocation + application overhead, unlike all direct-recursion benches. |
| `hanoi.hs`          | **Towers of Hanoi.** 2-way branching with 4 Int arguments (disk + 3 pegs). Different calling-convention surface than fib (1 arg) or tak (3 args). Non-tail + checksum. |

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

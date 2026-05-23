# Decision 290: Evaluate `williamw520/toposort` for Dependency Ordering

**Status:** Rejected (keep in-tree implementation)
**Date:** 2026-05-23
**Issue:** #290

## Context

Rusholme already uses topological sorting in two places:

1. **Module dependency ordering** — `src/modules/module_graph.zig`'s `topoSort`
   drives the compilation order in `CompileEnv.compileProgram`. Uses Kahn's
   algorithm; reports import cycles via Tarjan's SCC algorithm as structured
   `import_cycle` diagnostics.
2. **Renamer / dependency-tracked declarations** — definition-level ordering
   inside a module (see `docs/decisions/433-definition-level-module-deps.md`).

Two further potential uses sit on the roadmap:

3. **Binding group analysis in the typechecker** — sorting let-rec groups by
   dependency before generalisation.
4. **GRIN pass ordering** — sequencing dataflow analyses.

Issue #290 asked whether the [`williamw520/toposort`][toposort] Zig library
should replace the in-tree implementation for (1) and provide the substrate
for (2)–(4).

[toposort]: https://github.com/williamw520/toposort

## Candidate: `williamw520/toposort` (v1.0.5, August 2025)

### What it provides

| Feature | Status |
|---------|--------|
| `TopoSort(T)` generic over node type (`usize`, `[]const u8`, …) | Implemented |
| `add()` for explicit edges, plus Makefile-text input | Implemented |
| Topological ordering | Implemented |
| Cycle detection (reports cyclic nodes) | Implemented |
| Dependence-free subsets (parallel-execution batches) | Implemented |
| `build.zig.zon` packaging, current Zig (0.15.1) | Yes |
| License | MIT |
| Companion `toposort-cli` for Makefile-style files | Bundled |

Algorithm: classic Kahn's algorithm in `O(|N| + |E|)`, with optional
`max_range` optimisation for compact integer key domains.

### What we already have

`src/modules/module_graph.zig` implements:

- `ModuleGraph` — string-keyed adjacency list.
- `topoSort` — Kahn's algorithm. Same `O(|N| + |E|)` characteristics.
- `tarjanSCC` — strongly connected components, used to format cycle
  diagnostics by enumerating the offending modules in their cycle order.
- Integration with the project's `DiagnosticCollector` so that cycles emit
  `import_cycle` diagnostics with `SourceSpan`s rather than bubbling up as a
  generic error value.

The implementation is ~330 lines (one file), under our zero-leak policy, and
covered by 10+ unit tests (linear chain, diamond, 2- and 3-cycles,
self-loops, empty graph).

## Evaluation criteria

1. Behavioural fit for our use cases.
2. Integration cost with our diagnostics, allocator policy, and module-name
   model.
3. Maintenance cost (in-tree code vs external dependency churn).
4. Algorithmic completeness for the *open* use cases (binding groups, GRIN).

### 1. Behavioural fit

- **Module dependency ordering:** Both implementations produce the same
  Kahn-order output and detect cycles. `toposort`'s "dependence-free subsets"
  output is a strict superset of what we use today.
- **Cycle reporting:** This is where the libraries differ most. `toposort`
  reports cyclic *nodes*; our in-tree `tarjanSCC` reports the cycle as an
  ordered chain (`A → B → C → A`), which is what the `import_cycle`
  diagnostic renders. To match GHC-quality output we would still maintain
  Tarjan-style SCC logic alongside any external sort.
- **Definition-level dependencies (#433):** Already integrated with our
  graph; no library benefit.
- **Binding groups / GRIN passes:** Speculative use cases. Both have
  *specific* structural requirements (binding groups need SCCs, not just
  topo-order; GRIN passes need a fixed-point driver). A general-purpose
  topo-sort library doesn't move the needle for either.

### 2. Integration cost

- New `build.zig.zon` dependency. Adds a remote pin to maintain.
- API mismatch: our graph values are arbitrary strings keyed into an arena
  alongside other compiler data; `toposort`'s `TopoSort(T)` generic would
  push T to `[]const u8` and force a copy or interning layer.
- Diagnostics: cycle handling would need to be re-plumbed through our
  `DiagnosticCollector` either way — the library's cyclic-node list isn't
  directly usable.

### 3. Maintenance

- Removing ~330 lines of straightforward Zig and adding a tracked external
  dependency is a *negative* trade unless the library replaces materially
  more code than it costs. It does not.
- The in-tree implementation has needed zero changes since the parse-cache
  refactor landed (#443) and is fully covered by the project's own tests.
- An external dependency adds version-pinning, transitive-package, and
  CI-network considerations that the project does not otherwise carry.

### 4. Algorithmic completeness for open use cases

- Binding-group analysis wants SCCs, not topo-order. We already have
  `tarjanSCC` in-tree; the library's cycle-detection output is a less
  expressive subset.
- GRIN dataflow ordering, when we get there, is a fixed-point /
  worklist problem; topo-sort is at best a starting point. Either
  implementation can seed it.

## Recommendation

**Keep the in-tree implementation; do not add `williamw520/toposort` as a
dependency.**

The library is well-engineered for its scope, but its scope is narrower
than what Rusholme needs from a graph subsystem. Our existing code already:

- runs the algorithm we need (Kahn's),
- emits the diagnostics we need (Tarjan-formatted cycle chains, not just
  cyclic-node lists),
- integrates cleanly with the `DiagnosticCollector` / `SourceSpan` stack,
- is small enough that maintaining it is cheaper than pinning and tracking
  an external dependency.

For the speculative future use cases (binding groups, GRIN pass ordering),
the right abstraction is *SCC + worklist*, not generic topo-sort. We
already have the SCC half.

## Follow-ups

- None required for #290 itself.
- If the binding-group analysis (downstream of the typechecker) ever wants
  to consolidate "topologically ordered SCCs" as a reusable primitive, the
  natural home is `module_graph.zig` (or a sibling `graph.zig`), not a
  third-party crate.

## References

- `src/modules/module_graph.zig` — `ModuleGraph`, `topoSort`, `tarjanSCC`.
- `docs/decisions/288-zig-graph-evaluation.md` — prior rejection of
  `mitchellh/zig-graph` for the same use cases (different reasons:
  abandoned, Zig 0.9-era APIs).
- `docs/decisions/433-definition-level-module-deps.md` — current
  definition-level dependency tracking.
- Issue #290 itself.

# Decision 288: Evaluate zig-graph for Dependency and Analysis Graphs

**Status:** Rejected
**Date:** 2026-02-22
**Issue:** #288

## Context

Rusholme needs graph data structures for several compiler subsystems:

1. **Module dependency analysis** (#149) — import cycle detection, topological ordering
2. **GRIN heap points-to analysis** (#44) — the core whole-program analysis that enables
   GRIN's optimisation passes (unboxing, dead code elimination, etc.)
3. **Call graph construction** — reachability analysis for dead code elimination (#45)

Issue #288 proposed evaluating [zig-graph](https://github.com/mitchellh/zig-graph)
by Mitchell Hashimoto as a potential foundation.

## Candidate: zig-graph

### What it provides

| Feature | Status |
|---------|--------|
| Directed graph with weighted edges | Implemented |
| Tarjan's SCC detection | Implemented |
| Cycle detection (via SCC filtering) | Implemented |
| DFS traversal (iterator) | Implemented |
| Graph reversal | Implemented |
| Clone / deep copy | Implemented |
| Topological sort (Kahn's) | **Not implemented** (listed as TODO) |
| Dijkstra / shortest path | **Not implemented** (listed as TODO) |
| BFS traversal | **Not implemented** |

### Source

- Repository: https://github.com/mitchellh/zig-graph
- Last commit: September 2022
- Total commits: ~20
- Zig version: targets ~0.9 (no `build.zig.zon`)
- Author note: "This is literally the first piece of Zig code I've ever written"

## Evaluation

### 1. Zig version incompatibility (blocking)

Rusholme targets Zig 0.16-dev. zig-graph was last updated for Zig ~0.9. The
standard library API has changed drastically between these versions (`std.HashMap`,
allocator patterns, build system, package management). The library would require
a near-complete rewrite to compile against current Zig.

### 2. Missing critical algorithms

Topological sort is the single most important graph operation for Rusholme (module
dependency ordering, GRIN pass scheduling). It is listed as a TODO in zig-graph
and was never implemented. BFS is also absent.

### 3. Insufficient scope

The implemented surface area (adjacency maps + Tarjan + DFS) is approximately
300 lines of code. This is not a substantial dependency that saves meaningful
implementation effort.

### 4. Wrong abstraction for GRIN analysis

Heap points-to analysis (#44) is a **dataflow analysis**, not a graph traversal
problem. It requires fixpoint iteration over abstract domains (sets of possible
tags per variable). A generic `DirectedGraph` type is the wrong abstraction level
entirely. What GRIN analysis needs is closer to a constraint solver or abstract
interpretation engine, which must be purpose-built regardless of whether a graph
library is adopted.

### 5. Maintenance risk

An unmaintained external dependency (no commits in 3+ years) creates ongoing risk
of breakage as Zig evolves. For a foundational data structure that the compiler
depends on throughout its pipeline, this is unacceptable.

## Alternatives considered

No other Zig graph libraries of sufficient maturity were found. The Zig ecosystem
does not currently have a well-maintained, feature-complete graph library.

## Recommendation: Build purpose-built graph utilities

Build a small internal graph module with exactly the operations Rusholme needs:

| Use case | What to build |
|----------|--------------|
| Module dependency analysis (#149) | Directed graph + topological sort (Kahn's) + SCC detection (Tarjan's) for cycle error reporting |
| Call graph / dead code (#45) | Reachability via DFS from `main` — reuses the same directed graph type |
| GRIN heap points-to (#44) | Separate abstract interpretation framework with fixpoint iteration — not a graph library concern |

The directed graph + topological sort + SCC module is estimated at 300-400 lines
of idiomatic Zig. The algorithms are well-understood and straightforward to
implement correctly. This avoids carrying an unmaintained dependency while
aligning with the project's goal of learning Zig.

The GRIN analysis infrastructure should be designed when #44 is properly scoped,
as its own module with its own abstractions.

## Decision

**Reject** adoption of zig-graph. Build internal graph utilities as needed,
starting when module dependency analysis (#149) or GRIN analysis (#44) are
implemented.

## References

- zig-graph: https://github.com/mitchellh/zig-graph
- Tarjan's SCC algorithm: Tarjan, R.E. (1972). "Depth-first search and linear graph algorithms"
- Kahn's topological sort: Kahn, A.B. (1962). "Topological sorting of large networks"
- GRIN heap points-to: Hruska et al. (2020). "A Modern Look at GRIN"
- Issue #44: Heap points-to analysis for GRIN
- Issue #149: Renamer (module dependency tracking)
- Issue #45: GRIN dead code elimination

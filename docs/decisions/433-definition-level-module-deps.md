# Decision 433: Definition-level inter-module dependency graph

**Status:** Recommendation
**Date:** 2026-03-01
**Issue:** #433
**Type:** Research

---

## Context

Issue #367 implemented a module-level dependency graph with Kahn topological sort
and Tarjan SCC cycle detection (`src/modules/module_graph.zig`). This conservative
graph has a vertex per module and an edge A → B for every import declaration. Any
cycle yields a hard error; mutual module imports require `.hs-boot` stubs in GHC.

The module_graph.zig header already documents this limitation:

```
//! - Mutual recursion (`.hs-boot` files) is out of scope for M2. An import
//!   cycle always yields a hard error.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/433
```

This document evaluates whether a definition-level dependency graph can avoid
spurious cycle errors for module pairs that appear mutually dependent at the module
level but have no circular definitions at the binding level.

---

## The Problem With Module-Level Graphs

GHC treats each module as a vertex. An edge A → B exists for every `import B` in A,
regardless of which specific symbols are used. When A imports B and B imports A,
GHC detects a cycle at the module level and requires the programmer to break it
with `.hs-boot` files — even if the actual binding-level dependencies form no cycle.

Classic motivating example:

```haskell
-- Module A
module A where
import B (sumForest)
data Tree = Leaf Int | Node Tree Tree
treeSum :: Tree -> Int
treeSum (Leaf n)   = n
treeSum (Node l r) = treeSum l + treeSum r + sumForest (forestFromTree l)

-- Module B
module B where
import A (Tree)
newtype Forest = Forest [Tree]
sumForest :: Forest -> Int
sumForest (Forest ts) = sum (map treeSum' ts)
  where treeSum' (Leaf n)   = n
        treeSum' (Node l r) = treeSum' l + treeSum' r
```

At the module level this is a cycle. At the definition level:
- `A.treeSum` → `B.sumForest` → references `A.Tree` (a type, not a value binding)
- `B.sumForest` does **not** reference `A.treeSum` — it implements its own traversal

There is no definition-level cycle among value bindings. A definition-aware compiler
could compile `A.Tree`, `B.Forest`, `B.sumForest`, `A.treeSum` in this order without
any stub mechanism.

---

## Formal Definition

Let G_def = (V, E) be the **definition-level dependency graph** where:

- **Vertices** V: every top-level exported or non-local definition across all
  modules under compilation. Each vertex is a pair (M, name) where M is the
  originating module.

- **Edges** E: a directed edge `(M, f) → (N, g)` exists if and only if:
  - N ≠ M (cross-module reference), AND
  - the definition body of `f` in module M directly mentions name `g` from
    module N (in its RHS, guard, where-clauses, or type annotation).

For clarity, intra-module edges are omitted; GHC already computes intra-module SCCs
during renaming and the same analysis applies here.

A **true cross-module cycle** is any strongly-connected component of G_def with
size > 1. Such a cycle cannot be resolved without an external interface declaration
(the functional equivalent of `.hs-boot`).

Modules A and B **may be compiled without stubs** if no SCC of G_def spanning both
A and B contains a genuine cycle. In that case, the SCC analysis yields a partial
order on definitions that the compiler can follow.

---

## Type-Level vs Value-Level Treatment

The definition-level approach works cleanly for **value-level** bindings (`FunBind`,
`PatBind`). The dependencies of a value binding are:

1. Free variables referenced in the RHS.
2. Free variables in type annotations (if explicit signatures are present).
3. Free variables in where-clauses.

For **type-level declarations** (`DataDecl`, `NewtypeDecl`, `TypeDecl`, `ClassDecl`),
mutual recursion across module boundaries is possible:

```haskell
-- Module A
data Tree = Leaf Int | Node Tree Forest -- references B.Forest
-- Module B
data Forest = Empty | Cons Tree Forest  -- references A.Tree
```

This is a genuine type-level mutual recursion. Unlike the value-level case, it cannot
be resolved by compilation ordering: to compile `A.Tree` the compiler needs the layout
of `B.Forest`, and vice versa. This requires a form of knot-tying (GHC uses `fixM`
within a single compilation batch) that is fundamentally harder to automate across
modules without external declarations.

**Recommendation for M3+**: apply definition-level analysis to value bindings only.
Type declarations stay at module-level granularity, consistent with the conservative
#367 approach. If a module-level cycle involves only type declarations, that cycle is
reported as a hard error regardless of whether the types are mutually recursive.

This restriction is conservative but sound: it does not introduce new false negatives
(real cycles still error), and it does not require knot-tying infrastructure.

---

## Algorithm

The algorithm proceeds in three phases.

### Phase 1 — Module-level check (existing, #367)

Perform Kahn topological sort on the module-level graph. If the sort is complete
(no cycle), proceed directly to per-module compilation in topo order. No definition
analysis is needed.

If Kahn fails (cycle detected), proceed to Phase 2 rather than immediately erroring.

### Phase 2 — Definition-level graph construction (new, post-renamer)

**Prerequisite**: the renamer (#149) must be complete. Definition-level analysis
requires resolved `Name` values with unique IDs and their originating module, which
is exactly what the renamer produces.

For each module M in the candidate cycle:

1. Iterate over M's top-level `Decl` nodes.
2. For each `FunBind` or `PatBind` declaration `d`:
   - Collect all free qualified names in `d`'s matches, RHS, and where-clauses.
   - For each name `(N, g)` where N ≠ M, add edge `(M, d_name) → (N, g)` to G_def.
3. Skip `DataDecl`, `NewtypeDecl`, `TypeDecl`, `ClassDecl` — these remain at
   module-level granularity.

The name collection walk is structurally recursive over `Expr`, `Pattern`, and `Rhs`
variants in `src/frontend/ast.zig`. Since the renamer already walks the same
structure, this walk can share the traversal pattern.

### Phase 3 — SCC analysis and compilation ordering

Run Tarjan's SCC algorithm on G_def (the same algorithm already used in `module_graph.zig`
for module-level cycles, factored out or re-applied here).

- SCCs of size 1 (singletons): no cycle. Build a topological order over singletons
  and singleton-containing batches.
- SCCs of size > 1: a genuine cross-module definition cycle. Emit a structured
  diagnostic at the definition level (not just module level), naming the specific
  bindings that form the cycle.

The resulting ordering is a sequence of **compilation batches**, each batch being
a set of definitions that can be compiled in parallel (no dependencies between them
within the batch). Within each batch, definitions from the same module are compiled
together.

---

## Error Reporting

A definition-level cycle diagnostic is more informative than a module-level one.
Instead of:

```
error: import cycle detected: A → B → A
```

The compiler can emit:

```
error: definition cycle detected:
  A.treeSum (A.hs:12:1) references B.sumForest
  B.sumForest (B.hs:8:1) references A.treeSum
```

This directly identifies the offending bindings and lets the programmer see
exactly which cross-module call closes the cycle. The Diagnostic infrastructure
in `src/diagnostics/` already supports multi-span diagnostics; the cycle
report is a sequence of `(span, message)` pairs annotating each edge in the
cycle.

---

## Interaction with ModIface and CompileEnv

### The chicken-and-egg problem

To rename module A, the compiler needs B's exported types in scope (loaded from
B's `.rhi` file). If A and B are in a definition-level cycle, neither `.rhi`
file has been written yet.

This is the same problem that `.hs-boot` solves in GHC: a thin interface stub
that satisfies the type-checker's needs during the first pass, before the full
compilation of B completes.

### Resolution strategy for M3+

A two-pass compilation strategy within a cycle batch:

**Pass 1 — Type signatures only**: for each module in the batch, parse and
rename only the type signature declarations (`TypeSigDecl`) and type
declarations. Build partial `ModIface` values containing exported type signatures
but no implementation. Write these as provisional `.rhi` files.

**Pass 2 — Full compilation**: compile each module in the batch using the
provisional `.rhi` files from Pass 1. Replace the provisional files with the
final interfaces.

This two-pass approach is possible because Haskell's type system is manifestly
typed at the interface level — a function's type signature does not require
knowing the implementation of other functions. Pass 1 requires only the type
signatures and data declarations to be present in source, which is always the
case for well-typed Haskell.

Pass 1 corresponds to what GHC computes from `.hs-boot` files: a minimal interface
sufficient for type-checking. Rusholme can infer the boot interface automatically
rather than requiring the programmer to write it.

### M2 scope

For M2, `CompileEnv` (`src/modules/compile_env.zig`) does not yet use the
definition-level graph. The existing module-level topological sort in
`module_graph.zig` is the compile ordering mechanism. Any import cycle yields a
hard error (existing behaviour).

The definition-level algorithm described here becomes relevant in M3, when:
- The renamer (#149) is complete
- Multiple source modules are compiled in a single session
- Mutual imports are encountered in real programs

---

## Relationship to #367 (Module Graph + Topo Sort)

This approach **augments**, not replaces, #367.

The module-level graph serves two roles that cannot be replaced by definition-level
analysis:

1. **Module discovery** (`discoverModules`): scanning import headers to find
   which `.hs` files to compile. This requires only the module graph, not
   resolved names. Discovery runs before the renamer; the definition graph
   cannot exist yet.

2. **Conservative fast path**: when the module graph is acyclic (the common case),
   the compiler uses Kahn sort directly without ever building the definition graph.
   This avoids the overhead of Phase 2 for the majority of programs.

The definition-level analysis is a fallback engaged only when the module graph
has a cycle — which is rare in well-structured programs.

The amended pipeline for M3 is:

```
discoverModules → ModuleGraph → Kahn sort
                                    │ acyclic → compile in topo order (existing)
                                    │ cycle → Phase 2: build G_def
                                                            │ no true cycle → compile in def order
                                                            │ true cycle  → error with def-level diagnostic
```

---

## Comparison With GHC's `.hs-boot` Approach

| Property | GHC `.hs-boot` | Rusholme Definition Graph |
|---|---|---|
| Who resolves the cycle? | Programmer (manual stub) | Compiler (automatic) |
| Granularity | Module-level | Definition-level |
| False positive cycles | Yes (any mutual import) | No (only true def cycles) |
| Requires explicit annotation | Yes (`.hs-boot` file per cycle) | No |
| Type-level mutual recursion | Supported via `.hs-boot` | Hard error (M3 scope) |
| Implementation complexity | Low (parse stubs) | High (requires renamer) |
| Error message quality | Module names only | Specific binding names + spans |

GHC's `.hs-boot` is a pragmatic escape hatch that puts the burden on the programmer.
The definition graph automates the reasoning GHC expects the programmer to perform
manually, with better diagnostics.

---

## Comparison With Build Systems à la Carte

Mokhov, Mitchell, Peyton Jones (ICFP 2018) formalise task graphs keyed on
individual definitions (their "keys") rather than files. Their framework distinguishes:

- **Applicative build systems** (Make, Shake): dependencies are known statically
  before task execution.
- **Monadic build systems** (Bazel, Nix): dependencies may be discovered
  dynamically during execution.

The definition-level dependency graph is an **applicative** model: all edges are
known after renaming, before any code generation runs. This maps cleanly onto their
framework and implies the same theoretical properties — in particular, minimal
recompilation (recompile only definitions whose transitive dependencies have changed)
and maximal parallelism (definitions with no shared dependencies can compile in
parallel).

The interaction with #371 (recompilation avoidance via `.rhi` fingerprinting) is
direct: the fingerprint for definition `f` should ideally be keyed on the fingerprint
of `f`'s own source text plus the fingerprints of each directly-referenced definition,
not the fingerprint of the entire containing module. This finer key granularity is
exactly Build Systems à la Carte's prescription for minimal recompilation.

Connecting issue: #371's current module-level fingerprint becomes a definition-level
fingerprint in M3+.

---

## Conclusion and Recommendation

### M2 (current scope)

Maintain the conservative module-level graph from #367. Any import cycle is a hard
error. This is correct, simple, and matches GHC's baseline behaviour (without `.hs-boot`
support). No changes to `module_graph.zig` are needed.

### M3 (future work)

Implement the definition-level dependency graph as described above. The work decomposes
into three sequential issues, each depending on the previous:

1. **Prerequisite**: #149 (renamer) — required for resolved cross-module name
   references. The definition graph cannot be built without it.

2. **Core algorithm**: new file `src/modules/def_graph.zig` — `DefinitionGraph`
   type mirroring `ModuleGraph` but keyed on `(module_name, def_name)` pairs;
   `buildDefGraph(renamed_modules)` walker; SCC analysis producing compilation batches;
   definition-level cycle diagnostics.

3. **Two-pass compilation**: extend `CompileEnv.compileProgram` with a batch
   compilation path — Pass 1 (type signatures → provisional `.rhi`) followed by
   Pass 2 (full compilation using provisional `.rhi` values).

Filing the M3 tracking issue for the definition graph implementation is deferred
until #149 (renamer) is underway, as the precise API design depends on the renamer's
name representation.

### Summary answer to the issue's research question

> Can we do better than `.hs-boot` files for handling mutual imports?

Yes, in principle, and the algorithm is well-defined. The practical path is:
(1) complete the renamer, (2) build the definition graph as a post-rename pass,
(3) apply the two-pass compilation strategy for definition-cycle batches.

The definition graph is not a speculative idea — GHC already performs exactly this
analysis within a single module (`depAnalBinds` in `GHC.Tc.Module`), and Build
Systems à la Carte provides the theoretical grounding. Extending it across module
boundaries is a clean architectural step, not a fundamental departure.

---

## References

- Mokhov, Mitchell, Peyton Jones: *Build Systems à la Carte* (ICFP 2018).
  https://dl.acm.org/doi/10.1145/3236774
- Tarjan, R.E. (1972). "Depth-first search and linear graph algorithms."
  *SIAM Journal on Computing*, 1(2), 146–160.
- GHC source: `compiler/GHC/Tc/Module.hs` (`depAnalBinds`, `tcRnSrcDecls`)
- GHC source: `compiler/GHC/Driver/Make.hs` (`downsweep`, `upsweep`)
- Haskell 2010 Report §5.4: Separate Compilation and Mutually Recursive Modules
- Issue #288: zig-graph evaluation (recommends purpose-built graph utilities)
- Issue #367: Module graph + topo sort (M2 baseline)
- Issue #149: Renamer (prerequisite for Phase 2 above)
- Issue #371: Recompilation avoidance via `.rhi` fingerprinting
- Issue #365: Epic — Module system and multi-module compilation
- `src/modules/module_graph.zig`: existing Kahn + Tarjan implementation
- `src/modules/mod_iface.zig`: `ModIface` serialisation
- `src/modules/compile_env.zig`: `CompileEnv` and compilation pipeline

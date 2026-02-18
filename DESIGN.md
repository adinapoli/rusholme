# Rusholme — A Toy Haskell Compiler in Zig

**Rusholme** is a toy Haskell compiler written in [Zig](https://ziglang.org/),
developed collaboratively with AI assistance. The project serves two purposes:

1. **Learning Zig** — by working on a non-trivial, real-world-ish project.
2. **Exploring compiler construction** — by implementing a subset of Haskell
   from scratch (lexing, parsing, type checking, code generation).

## Why "Rusholme"?

[Rusholme](https://en.wikipedia.org/wiki/Rusholme) is an area in Manchester
famous as **"the Curry Mile"** for its vibrant Indian restaurant scene. Since
*currying* is one of the most fundamental concepts in Haskell, the name felt
like a perfect fit — a nod to Manchester, good food, and functional programming
all at once.

> **Status:** Early stages — project skeleton only.

## Goals

- Implement a *subset* of Haskell 2010 (enough to be interesting, not enough to
  be GHC).
- **Preserve laziness** — laziness is fundamental to Haskell; we won't
  compromise on call-by-need semantics.
- **Multi-backend code generation** — emit code for multiple targets (C, JS,
  LLVM/native, WebAssembly).
- **Compilation and runtime speed** — keep the compiler fast and produce
  reasonably efficient output.
- Keep the codebase simple, readable, and well-documented so it doubles as a
  learning resource for Zig.
- Make incremental progress: each milestone should produce something that
  compiles and runs.

### Project Mantras

1. **Parse everything GHC parses.** Rusholme should eventually accept every
   Haskell program that GHC accepts, even if runtime behaviour differs depending
   on what we implement and how.
2. **Leverage battle-tested C libraries.** Zig has exceptional C interop — use
   strong, industrial-grade C libraries for hard tasks whenever possible, and
   source them cleanly via Nix.

## Non-Goals (for now)

- Full Haskell compliance.
- Performance parity with production compilers.
- Package management / Cabal support.

## Compilation Pipeline

Rusholme uses a simplified pipeline inspired by GHC but replacing STG+Cmm with
**GRIN** (Graph Reduction Intermediate Notation):

```
Haskell Source
  → Lexing / Parsing       → AST
  → Typechecking / Desugar → Core    (typed, small, optimisable)
  → Core → GRIN                      (laziness-aware, backend-agnostic)
  → GRIN → Backend         ├─→ C
                           ├─→ JavaScript
                           ├─→ LLVM (→ native, WebAssembly)
                           └─→ (others in future)
```

### Why this pipeline?

| Stage | Role |
|-------|------|
| **AST** | Faithful representation of the Haskell source, used for error reporting |
| **Core** | A typed intermediate language modelled on GHC's System F_C. Serves as the type-safety firewall — if Core typechecks, later stages can be trusted. Full GHC Core compatibility enables future interop: import GHC's `-ddump-simpl` output directly into the Rusholme pipeline |
| **GRIN** | Replaces both STG and Cmm. Explicitly represents memory operations (`store`/`fetch`/`update`) and thunks as first-class IR constructs. Supports whole-program optimisation: dead code elimination, unboxing, heap-to-stack conversion. Crucially, **preserves lazy evaluation** while being backend-agnostic |

### Key references

- **GRIN**: Csaba Hruska et al., *"A Modern Look at GRIN, an Optimising
  Functional Language Back End"*, Acta Cybernetica, 2020.
  Project: https://grin-compiler.github.io/
- **Lambda the Ultimate SSA**: Bhat et al., arXiv 2022 — MLIR regions for
  functional language compilation (relevant if we explore SSA-based optimisation
  in future).
- **PureCake**: Kanabar et al., PLDI 2023 — verified compiler for a lazy
  functional language (interesting for correctness, less so for multi-backend).

### What we skip (and why)

- **Renaming pass** — GHC has a dedicated renamer between parsing and
  typechecking. We may fold this into typechecking or keep it separate; TBD.
- **STG** — replaced by GRIN, which handles laziness without baking in GHC's
  runtime assumptions.
- **Cmm** — replaced by GRIN, which talks directly to backends.
- **Core-to-Core optimisations** — all optimisation is deferred to GRIN. This
  makes the pipeline faster and lets us fully showcase GRIN's capabilities.

## Language Subset

Rusholme targets a pragmatic subset of Haskell, growing over time.

### Included (from the start)

- **Type system**: Hindley-Milner with type classes. `forall` for type
  signatures (not kinds). ADTs, `newtype`, `type` aliases. GADTs.
- **Deriving**: `Show`, `Eq`, `Read`, `Ord` (stock strategy).
- **Pattern matching**: full — nested patterns, guards, `where`, `case`.
- **Modules**: imports, exports, qualified imports.
- **Syntax**: `do`-notation, `where` clauses, `if/then/else`, `let/in`.
- **String representation**: `[Char]` by default (Haskell 2010 faithful).
  Potential compiler flag for `Text`-like representation in future.
- **Unicode**: full Unicode support in identifiers and operators.

### Deferred

- List comprehensions.
- FFI (foreign function interface).
- Template Haskell, quasi-quotes.
- GHC-specific flags, pragmas, and language extensions — Rusholme compiles
  standard Haskell; GHC runtime-specific flags (e.g. worker-wrapper) won't
  apply.

### Prelude

A minimal Prelude is required. We will research existing trimmed-down Preludes
from teaching compilers and adapt one. Must include at minimum: basic types
(`Bool`, `Int`, `Char`, `String`, `Maybe`, `Either`, `IO`, lists), core
functions (`id`, `const`, `map`, `filter`, `foldr`, `foldl`), and basic type
classes (`Eq`, `Ord`, `Show`, `Read`, `Num`, `Monad`).

## Frontend Strategy

### Parsing

Parser technique is TBD — requires research. Options under consideration:

1. **Reuse GHC's Alex/Happy grammar** — port or translate the grammar specs.
2. **tree-sitter-haskell** — community-maintained, quite complete.
3. **Hand-written recursive descent** — informed by GHC's grammar.

Whichever approach we choose: the full Haskell 2010 layout rule must be
implemented (not a simplified version).

### Error diagnostics

Structured diagnostic infrastructure from day one. Errors are an AST, not
strings — enabling rich rendering (terminal, JSON, LSP). Individual error
messages may start simple, but the infrastructure must support GHC-quality
diagnostics. Source spans are tracked from the lexer onwards.

Goals beyond GHC:
- Report errors for *all* modules, not just the first failure.
- Avoid confusing cascading errors from layout rule ambiguity.

## Backend Strategy

### LLVM first

LLVM is the primary backend. It generates both native code and WebAssembly from
a single backend, and its optimisation infrastructure is unmatched.

### Runtime in Zig

The runtime system (entry point, thunk evaluation, heap allocation, basic I/O)
is written in Zig. This keeps the entire project in one language and leverages
Zig's C interop for any C libraries we need.

### Calling convention

TBD — requires research. Candidates: eval/apply (GHC's approach), push/enter
(Marlow & Peyton Jones), CPS.

## GRIN Details

### Dialect

"Modern GRIN" from Hruska et al. (2020), which refines Boquist's original
representation with improved node types and analysis.

### Core → GRIN translation

Plan TBD. The translation must handle thunks, partial applications, and
constructors mapping to GRIN nodes. The codebase must have clear interfaces at
this boundary to allow the translation strategy to evolve.

### Optimisation passes

All optimisation is in GRIN (no Core-to-Core passes). Priority order TBD based
on impact analysis, likely starting with dead code elimination. Heap points-to
analysis depth for v1 is TBD.

## Testing Strategy

### Unit tests

Zig's built-in `test` blocks. Each pipeline stage tested independently: lexer,
parser, typechecker, Core, GRIN, codegen.

### Golden / snapshot tests

Compile Haskell snippets and compare output against expected results. Borrow
simple test programs from GHC's testsuite where possible.

### End-to-end tests

Compile + run a Haskell program and check stdout matches expected output.

### CI

GitHub Actions using the Nix flake for reproducible builds. Set up early.

## Project Structure

### Layout

Split into modules per pipeline stage (not one big `src/`). Zig supports this
via its package system. Modularity and information hiding (Parnas) are core
principles.

### Error handling

Zig error unions + a custom diagnostic type that can render to multiple formats
(terminal, JSON, LSP-compatible). Errors propagate cleanly across stages.

### Logging and debug output

`std.log` for runtime logging. Pretty-printers per IR for dumping intermediate
representations. Leverage C libraries via Zig's C interop where helpful.

## Milestones

| Milestone | Goal | Key deliverables |
|-----------|------|------------------|
| **M0** | Project infrastructure | CI, project layout, error scaffolding, Nix flake |
| **M1** | `main = putStrLn "Hello"` | Lexer, parser, typechecker, Core, GRIN, LLVM backend, tree-walking interpreter. Produce an ELF binary and (if feasible) Wasm output |
| **M2** | Basic programs | ADTs, pattern matching, type classes, modules, minimal Prelude |
| **M3** | GRIN optimisations | Dead code elimination, unboxing, heap-to-stack, heap points-to analysis |
| **M4** | Multi-backend + polish | Wasm output, REPL, improved diagnostics |

## Memory Management

GHC uses a generational copying GC with a nursery and older generations, plus a
concurrent non-moving collector (Ben Gamari, GHC 8.10) for latency-sensitive
workloads and pinned object fragmentation. For Rusholme we take a different,
phased approach.

### Strategy: phased, from simple to ambitious

| Phase | Approach | Description |
|-------|----------|-------------|
| **Phase 1** | Arena / Region allocator | Use Zig's built-in `std.heap.ArenaAllocator` to get something working fast. Regions are freed in bulk — natural fit with Zig and sufficient for early milestones |
| **Phase 2** | Immix (mark-region GC) | Implement an Immix-style collector as a custom `std.mem.Allocator`. Immix allocates in 32KB blocks / 128B lines, with opportunistic defragmentation. Best balance of performance and complexity. Simon Marlow noted GHC's allocator is "quite similar to Immix" |
| **Phase 3** | ASAP-style static deallocation | Leverage GRIN's whole-program analysis to insert compile-time deallocation where provably safe. Goal: eliminate runtime GC for as much of the program as possible, falling back to Immix for the rest |

### Plug-and-play via Zig allocators

A key enabler of this phased strategy is Zig's `std.mem.Allocator` interface.
In Zig, `Allocator` is a **vtable-based interface** — any struct that provides
`alloc`, `resize`, and `free` function pointers can serve as an allocator. The
entire runtime and all data structures are parameterised over `Allocator`,
meaning:

- **Phase 1 → Phase 2 is a swap, not a rewrite.** The runtime code calls
  `allocator.alloc(...)` and `allocator.free(...)` everywhere. Switching from
  `ArenaAllocator` to an Immix allocator means changing which allocator is
  passed in — the rest of the codebase is untouched.
- **Multiple strategies can coexist.** Different parts of the runtime (e.g.
  the parser vs. the GRIN evaluator) can use different allocators
  simultaneously.
- **Testing and benchmarking is trivial.** We can run the same program under
  Arena, Immix, and ASAP allocators and compare behaviour, memory usage, and
  performance with no code changes.

This is analogous to Haskell's type class polymorphism, but at the systems
level — and it's a zero-cost abstraction in Zig (the vtable is resolved at
comptime when the concrete allocator type is known).

### Why Immix?

- 7–25% faster than canonical GCs in benchmarks (Blackburn & McKinley, PLDI 2008)
- Space efficiency of mark-compact with speed of mark-sweep
- Opportunistic defragmentation avoids the "all-or-nothing" copying cost
- LLVM-based implementation exists; GRIN targets LLVM
- Can be implemented as a Zig custom allocator

### Why ASAP?

- No runtime GC overhead for statically-deallocatable values
- GRIN's explicit `store`/`fetch`/`update` make static deallocation insertion
  natural
- Whole-program analysis (required by ASAP) is already part of the GRIN pipeline
- Could be Rusholme's differentiating feature among toy compilers

### Key references

- **Immix**: Blackburn & McKinley, *"Immix: A Mark-Region Garbage Collector
  with Space Efficiency, Fast Collection, and Mutator Performance"*, PLDI 2008.
  PDF: https://users.cecs.anu.edu.au/~steveb/pubs/papers/immix-pldi-2008.pdf
- **ASAP**: Proust, *"ASAP: As Static As Possible memory management"*,
  Cambridge TR-908, 2017.
  PDF: https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-908.pdf
- **Cloaca**: Hardware-assisted concurrent GC for non-strict functional
  languages, Haskell Symposium 2024.
  DOI: https://doi.org/10.1145/3677999.3678277
- **Liveness-based GC**: Kumar et al., *"Liveness-Based Garbage Collection
  for Lazy Languages"*, arXiv 2016.
  PDF: https://arxiv.org/pdf/1604.05841

### What we skip (and why)

- **GHC's generational copying GC** — well-proven but complex to implement;
  Immix achieves better performance with simpler design.
- **Non-moving concurrent GC** — solves latency issues we don't yet have; adds
  significant complexity.
- **Hardware GC (Cloaca)** — fascinating research but requires FPGA; not
  applicable to a software runtime.

## Decisions Log

*Decisions will be recorded here as the project evolves.*

| # | Decision | Rationale | Date |
|---|----------|-----------|------|
| 1 | Use Zig as the implementation language | Learning Zig through a substantial project | 2026-02-15 |
| 2 | Target a subset of Haskell 2010 | Keep scope manageable for a toy compiler | 2026-02-15 |
| 3 | AI-assisted development | Pair-programming with AI to accelerate learning | 2026-02-15 |
| 4 | Preserve laziness (call-by-need) | Laziness is fundamental to Haskell; dropping it would break compatibility with real Haskell code | 2026-02-15 |
| 5 | Use GRIN instead of STG+Cmm | GRIN explicitly models laziness and memory ops in a single IR, supports whole-program optimisation, and is backend-agnostic — simpler pipeline with more flexibility | 2026-02-15 |
| 6 | Full GHC Core (System F_C) | Enables future interop: import GHC's `-ddump-simpl` output into the Rusholme pipeline | 2026-02-15 |
| 7 | Target multiple backends (C, JS, LLVM) | Explore code generation to different platforms from a single IR | 2026-02-15 |
| 8 | Phased GC strategy: Arena → Immix → ASAP | Start simple (arena/regions), graduate to Immix for real GC, explore ASAP for compile-time deallocation | 2026-02-15 |
| 9 | Immix as primary runtime GC | Best balance of performance, simplicity, and compatibility with GRIN/LLVM; Marlow-endorsed for Haskell | 2026-02-15 |
| 10 | Explore ASAP-style static deallocation | Leverage GRIN's whole-program analysis to eliminate runtime GC where possible — differentiating feature | 2026-02-15 |
| 11 | Implement GC as Zig custom allocator | Zig's `std.mem.Allocator` interface allows swapping GC strategies cleanly | 2026-02-15 |
| 12 | ADTs + type classes as baseline type system | Extensible foundation; `forall` for types (not kinds) included | 2026-02-15 |
| 13 | GADTs + stock deriving (Show, Eq, Read, Ord) | Essential for compiling realistic programs | 2026-02-15 |
| 14 | Full pattern matching, modules, do-notation | Core Haskell features needed from day one | 2026-02-15 |
| 15 | No FFI or list comprehensions initially | Keep initial scope manageable | 2026-02-15 |
| 16 | `[Char]` strings by default | Haskell 2010 faithful; potential compiler flag for Text-like in future | 2026-02-15 |
| 17 | Full Unicode support | Per Haskell 2010 spec for identifiers and operators | 2026-02-15 |
| 18 | Structured error diagnostics from day one | Errors as AST, not strings; infrastructure for GHC-quality diagnostics | 2026-02-15 |
| 19 | Source spans tracked from the lexer | Right foundation from the start; essential for good error messages | 2026-02-15 |
| 20 | All optimisation deferred to GRIN | No Core-to-Core passes; showcases GRIN's value and simplifies pipeline | 2026-02-15 |
| 21 | Modern GRIN dialect (Hruska et al.) | Newer research with improved node representation | 2026-02-15 |
| 22 | LLVM as primary backend | Generates native + Wasm; unmatched optimisation infrastructure | 2026-02-15 |
| 23 | Runtime system written in Zig | Single language for entire project; leverages Zig's C interop | 2026-02-15 |
| 24 | Tree-walking interpreter before codegen | Validate frontend pipeline before tackling backend complexity | 2026-02-15 |
| 25 | GitHub Actions CI via Nix flake | Reproducible builds from the start | 2026-02-15 |

| 26 | Stress-test parser with real Haskell code (Epic #11) | After Epic #4 completion, incrementally test GHC test programs to (1) drive golden test infrastructure, (2) discover parser gaps → new issues under Epic #4, (3) improve error diagnostics, and (4) build CLI parse-checker interface | 2026-02-17 |

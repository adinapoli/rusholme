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
| **Core** | A small, typed intermediate language (simplified System F). Serves as the optimisation stage and type-safety firewall — if Core typechecks, later stages can be trusted |
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

## Decisions Log

*Decisions will be recorded here as the project evolves.*

| # | Decision | Rationale | Date |
|---|----------|-----------|------|
| 1 | Use Zig as the implementation language | Learning Zig through a substantial project | 2026-02-15 |
| 2 | Target a subset of Haskell 2010 | Keep scope manageable for a toy compiler | 2026-02-15 |
| 3 | AI-assisted development | Pair-programming with AI to accelerate learning | 2026-02-15 |
| 4 | Preserve laziness (call-by-need) | Laziness is fundamental to Haskell; dropping it would break compatibility with real Haskell code | 2026-02-15 |
| 5 | Use GRIN instead of STG+Cmm | GRIN explicitly models laziness and memory ops in a single IR, supports whole-program optimisation, and is backend-agnostic — simpler pipeline with more flexibility | 2026-02-15 |
| 6 | Keep a simplified Core (à la System F) | Small typed IR for optimisation and as a safety firewall between frontend and GRIN | 2026-02-15 |
| 7 | Target multiple backends (C, JS, LLVM) | Explore code generation to different platforms from a single IR | 2026-02-15 |

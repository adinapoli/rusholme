# GRIN — Graph Reduction Intermediate Notation

> Source: https://grin-compiler.github.io/
> GitHub: https://github.com/grin-compiler/grin
> Author: Csaba Hruska et al.
> Retrieved: 2026-02-15

## Overview

GRIN is a compiler framework and an intermediate representation. It is short
for Graph Reduction Intermediate Notation. GRIN could significantly improve the
tooling, performance and size of functional programs and could enable functional
technologies to target new platforms like WebAssembly.

Functional languages are compiled in three stages:

1. Language frontend
2. High-level optimizer (functional)
3. Low-level optimizer (imperative)

While LLVM handles the last step, GRIN as a functional optimizer can capture
the original language semantics and can perform transformations that are
infeasible at LLVM level.

## Language Frontends

- **Haskell** — [GHC/GRIN](https://github.com/grin-compiler/ghc-grin):
  combination of GHC's Haskell language frontend and the GRIN optimizer.
- **Idris** — [Idris/GRIN](https://github.com/grin-compiler/idris-grin):
  adding GRIN optimizer to the Idris compiler pipeline.
- **Agda** — [Agda/GRIN](https://github.com/grin-compiler/agda-grin):
  initial code stub.

## Benefits

### Tooling

Whole program analysis enables: immediate feedback while typing, visual
debugging and profiling, memory structure inspection, laziness debugging,
visualisation of unevaluated expressions. Could highlight optimization effects
on source code (dead code/data, linear variable usage, laziness, strictness,
tail call, unboxing, stack/heap allocation) via Language Server Protocol.

### Smaller Executables

Whole program analysis removes dead code and dead data fields more effectively,
including unused type class instances. Cuts down referenced external libraries
and symbols.

### Better Performance

Removes lots of redundant computation: unnecessary laziness and redundant memory
operations. GRIN represents memory operations and laziness explicitly, allowing
aggressive memory layout optimizations (unboxing, heap-to-stack/register
conversion). Eliminates indirect function calls, enabling LLVM to perform more
optimizations.

### New Platforms

Uses LLVM for machine code generation. Supports x64, ARM, WebAssembly —
covering desktop, mobile and web.

## Related Work

### Whole Program Compilers

- **Boquist GRIN** — the original GRIN formulation
- **UHC, JHC, LHC** — other Haskell whole-program compilers
- **[HRC (Intel Labs Haskell Research Compiler)](http://www.leafpetersen.com/leaf/publications/hs2013/hrc-paper.pdf)**
  — showed performance effect of whole program optimization on Haskell
  - Also: [Measuring the Haskell Gap](http://www.leafpetersen.com/leaf/publications/ifl2013/haskell-gap.pdf)
- **[MLton](http://mlton.org/)** — leading industrial strength whole program
  compiler for SML; showed whole program compilation is feasible with low
  compile times

### Program Analysis

- **[Souffle datalog compiler](https://souffle-lang.github.io/)** — synthesizes
  native parallel C++ from logic specifications; used for points-to, control
  flow and other analyses
- **[P4F: Pushdown Control-Flow Analysis for Free](https://arxiv.org/pdf/1507.03137.pdf)**
  — advanced control flow analysis that can boost optimizer efficiency

### Memory Management

- **[ASAP Memory Management](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-908.pdf)**
  — compile-time automatic memory management using whole program analysis;
  generates a specialised garbage collector per program; may enable running
  Haskell without a runtime GC
- **[Gibbon](https://github.com/iu-parfunc/gibbon)** — experiments with packed
  memory data representation; pointerless data reduces cache misses

## Key Paper

> Csaba Hruska, Péter Dávid Podlovics, Andor Pénzes.
> **"A Modern Look at GRIN, an Optimizing Functional Language Back End"**
> *Acta Cybernetica*, Volume 25, 2020, pp. 847–876.
> PDF: http://nbviewer.jupyter.org/github/Anabra/grin/blob/fd9de6d3b9c7ec5f4aa7d6be41285359a73494e3/papers/stcs-2019/article/tex/main.pdf

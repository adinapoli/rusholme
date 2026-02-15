# 🍛 Rusholme

**A toy Haskell compiler written in Zig — baked with LLMs, served with curry.**

> *[Rusholme](https://en.wikipedia.org/wiki/Rusholme) is an area in Manchester
> famous as "the Curry Mile." Since currying is one of the most fundamental
> concepts in Haskell, the name felt like a perfect fit.*

---

## ⚠️ Disclaimer

This is an **experimental, educational project** built collaboratively between a
human and AI (LLM-assisted development). It exists purely for fun and learning.
If you're looking for a production Haskell compiler, you want
[GHC](https://www.haskell.org/ghc/). If you're looking for a good time, read on.

## What Is This?

Rusholme aims to compile a subset of Haskell 2010 using an unconventional
pipeline:

```
Haskell Source → Parse → Typecheck/Desugar → Core → GRIN → Backend
                                                      ├─→ C
                                                      ├─→ JavaScript
                                                      └─→ LLVM (native, Wasm)
```

Key design choices:

- **Zig** as the implementation language (because learning Zig is half the point)
- **GRIN** instead of STG+Cmm (explicit laziness, whole-program optimisation,
  backend-agnostic)
- **Immix GC** as the primary garbage collector, with ASAP-style compile-time
  deallocation as an experimental goal
- **Laziness preserved** — no compromises on call-by-need semantics

See [DESIGN.md](DESIGN.md) for the full rationale and decisions log.

## Project Status

🚧 **Early stages** — project skeleton and design documents only. No compiler
code yet.

## Building

Requires [Zig](https://ziglang.org/) (see `build.zig.zon` for minimum version).

```bash
zig build
```

## Documentation

The `docs/` directory contains reference materials and paper summaries that
inform the design. See [docs/README.md](docs/README.md) for the full index.

## Why LLM-Assisted?

This project is an experiment in AI-assisted compiler construction. Every design
decision, research summary, and line of code is produced through human–AI
pair-programming. The human brings domain expertise (Haskell, compilers); the AI
brings tireless literature review and Zig boilerplate. It's a collaboration, not
a generation.

## License

Not yet decided. For now, consider this code available for reading and learning.

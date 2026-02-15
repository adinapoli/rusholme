<p align="center">
  <img src="assets/logo.png" alt="Rusholme logo" width="200">
</p>

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

## Development

Requires [Nix](https://nixlang.org/) with flakes enabled, or
[Zig](https://ziglang.org/) (see `build.zig.zon` for minimum version).

```bash
# Enter the development shell (provides Zig + LLVM)
nix develop

# Build the executable
zig build

# Run all tests (use --summary all to see what ran)
zig build test --summary all

# Run the compiler
zig build run
```

> **⚠️ Note on `zig build` vs `zig build test`**
>
> Zig uses lazy compilation — `zig build` only compiles code paths reachable
> from `main.zig`. Since `main.zig` doesn't yet use the library modules,
> **`zig build` alone will not catch compilation errors in library code.**
> Always use `zig build test --summary all` to verify correctness.
> The `--summary all` flag prints the number of tests discovered and their
> pass/fail status, which is critical for confirming tests are actually
> running. `src/root.zig` uses `std.testing.refAllDecls` to force the test
> runner to discover tests across all submodules.
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

<p align="center">
  <img src="assets/logo.png" alt="Rusholme logo" width="200">
</p>

<p align="center">
  <a href="https://github.com/adinapoli/rusholme/actions/workflows/ci.yml">
    <img src="https://github.com/adinapoli/rusholme/actions/workflows/ci.yml/badge.svg" alt="CI Status">
  </a>
  <img src="https://img.shields.io/badge/Zig-0.16.0--dev-orange?logo=zig" alt="Zig Version">
  <img src="https://img.shields.io/badge/Haskell-2010-blue?logo=haskell" alt="Haskell 2010">
  <img src="https://img.shields.io/badge/License-TBD-lightgrey" alt="License">
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

🚧 **Active development** — the compiler can parse, rename, typecheck, desugar,
lambda-lift, and translate Haskell to GRIN IR. A tree-walking GRIN evaluator
with PrimOp support is wired up. See the showcase below!

## See It In Action

Given a Haskell source file:

```haskell
module Demo where

compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

apply :: (a -> b) -> a -> b
apply f x = f x

identity :: a -> a
identity x = x
```

**Type inference** — `rhc check demo.hs`:

```
compose  :: forall a b c. (a -> b) -> (c -> a) -> c -> b
apply    :: forall a b. (a -> b) -> a -> b
identity :: forall a. a -> a
```

**GRIN IR** — `rhc grin demo.hs`:

```
=== GRIN Program (3 defs) ===
compose f g x =
  g x ;
  \arg ->
    f arg

apply f x =
  f x

identity x =
  pure x
```

Notice how `compose` correctly sequences the nested application `f (g x)` —
the inner call `g x` is evaluated first and bound to `arg`, then `f arg` is
called with the result. This is monadic bind (`>>=`) in GRIN's
imperative notation.

**LLVM IR** — `rhc ll hello.hs` (for `main = putStrLn "Hello"`):

```llvm
@.str = private unnamed_addr constant [6 x i8] c"Hello\00", align 1

define i32 @main() {
entry:
  %0 = call i32 @puts(ptr @.str)
  ret i32 0
}

declare i32 @puts(ptr)
```

The full pipeline — from Haskell source through parsing, renaming, typechecking,
Core desugaring, lambda lifting, GRIN translation, all the way to LLVM IR —
produces a real program that calls libc `puts` to print "Hello".

**Native executable** — `rhc build hello.hs`:

```bash
$ rhc build hello.hs
$ ./hello
Hello
```

`rhc build` runs the full pipeline, emits a native object file via LLVM, and
links it into an executable using the system C compiler.
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

## Binary Cache (Cachix)

Rusholme uses [Cachix](https://cachix.org/) for binary caching to speed up builds.
To use the cache locally, create or edit `~/.config/nix/nix.conf`:

```conf
substituters = https://cache.nixos.org https://adinapoli-rusholme.cachix.org
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= adinapoli-rusholme.cachix.org-1:TPBkX8B1CfCiqiMRQbq1rg12C8Lgaczubka/fO/cHeo=
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

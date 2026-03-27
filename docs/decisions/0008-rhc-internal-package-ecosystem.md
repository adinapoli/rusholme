# Vision: `rhc-internal` and the Rusholme Package Ecosystem

**Date:** 2026-03-27
**Status:** Vision / North Star
**Related issues:** #10 (Epic: Minimal Prelude), #531, #616, #615, #566, #623

---

## Motivation

Today `lib/Prelude.hs` is a monolithic file that simultaneously plays three roles:
- Declares `foreign import prim` wrappers over compiler PrimOps
- Implements core data types and type class instances
- Exposes the public `Prelude` surface that user code sees

This conflation couples the public API directly to compiler internals. It creates the same versioning headache that plagued GHC for years: `base` was locked to a specific GHC version because it was full of internal dependencies. GHC's ongoing "relocatable base" effort (and the `ghc-internal` split) is the fix. Rusholme should get this right from the start.

The vision is a layered package ecosystem where `base` is pure Haskell and can, in principle, be compiled against different versions of `rhc-internal` as long as the internal interface is stable.

---

## Design Principle

> **Anything that requires knowledge of Rusholme internals or PrimOps goes in an `rhc-*` package. Pure Haskell code goes in `base`.**

`base` may import *types* and use *instances* from `rhc-internal`, but it must never call `foreign import prim` directly and must contain no compiler-specific knowledge.

---

## The Three-Layer Package Stack

```
┌─────────────────────────────────────────────────┐
│  base                                           │
│  Pure Haskell. Re-exports from rhc-internal.    │
│  Prelude, Data.Maybe, Data.List, System.IO, ... │
└───────────────────┬─────────────────────────────┘
                    │ imports types + instances
┌───────────────────▼─────────────────────────────┐
│  rhc-internal                                   │
│  Compiler-magic types. Class defs + primitive   │
│  instances. Thin IO wrappers over primops.      │
│  RHC.Base, RHC.IO                               │
└───────────────────┬─────────────────────────────┘
                    │ foreign import prim
┌───────────────────▼─────────────────────────────┐
│  rhc-prim                                       │
│  foreign import prim declarations only.         │
│  RHC.Prim                                       │
└─────────────────────────────────────────────────┘
```

### `rhc-prim`

Nothing but `foreign import prim` declarations. No logic, no data types.

```
rhc-prim/
  RHC/Prim.hs    -- primAddInt, primEqInt, primPutChar, primError,
                 -- intToChar, charToInt, ...
```

### `rhc-internal`

Compiler-magic types, type class definitions with their primitive instances,
and thin IO wrappers. Everything here knows about the compiler.

```
rhc-internal/
  RHC/Base.hs    -- Bool, Int, Char (magic types)
                 -- Eq, Ord, Num, Show, Enum class definitions
                 -- instance Eq Int, instance Ord Int, instance Num Int, ...
  RHC/IO.hs      -- IO type; putChar (thin wrapper over primPutChar)
```

### `base`

Pure Haskell throughout. Imports types and instances from `rhc-internal`
but contains no `foreign import prim` and no compiler knowledge.

```
base/
  Prelude.hs           -- re-exports
  Data/Bool.hs         -- not, (&&), (||), otherwise
  Data/Maybe.hs        -- Maybe, maybe, fromMaybe
  Data/Either.hs       -- Either, either
  Data/List.hs         -- map, filter, foldr, foldl, (++), take, drop, concat, ...
  Data/Char.hs         -- intToDigit, future char classification
  Data/Function.hs     -- id, const, flip, (.), ($)
  System/IO.hs         -- putStr, putStrLn, print
                       -- (call into RHC.IO, but pure Haskell logic)
```

---

## Package Store

Following GHC's model, packages live in a versioned store:

```
~/.rhc/store/<arch>-<os>-<rhc-version>/
  package.conf.d/               -- one .conf (JSON) per installed package
  rhc-prim-0.1.0/
    RHC/Prim.rhi
    grin/RHC.Prim.grin          -- canonical compiled IR
    llvm/x86_64-linux/
      rhc-prim.bc               -- cached LLVM bitcode (target-specific)
  rhc-internal-0.1.0/
    RHC/Base.rhi
    RHC/IO.rhi
    grin/RHC.Base.grin
    grin/RHC.IO.grin
    llvm/x86_64-linux/
      rhc-internal.bc
  base-0.1.0/
    Prelude.rhi
    Data/Maybe.rhi
    ...
    grin/...
    llvm/x86_64-linux/
      base.bc
```

### Artifact layers

| Artifact | Scope | Purpose |
|----------|-------|---------|
| `.rhi` | Per module | Types, `ClassEnv`, `DictNameMap` — always present |
| `.grin` | Per module | GRIN IR — canonical compiled form, backend-agnostic |
| `.bc` | Per package per target | Cached LLVM bitcode — avoids re-translating GRIN for LLVM backends |

The `.bc` cache is keyed by target triple and can be invalidated independently
of the GRIN IR when the LLVM backend changes. The GRIN IR is the canonical
artifact; `.bc` is a build-time optimisation.

**Boot packages** (`rhc-prim`, `rhc-internal`, `base`) ship with the compiler
and are pre-installed into the store at compiler build time. The store is
versioned by `rhc` version, so a compiler upgrade gets a clean store.

A `rhc-pkg` tool (mirroring `ghc-pkg`) manages `package.conf.d/` entries:
install, query, remove, check.

---

## Dependency Graph to Get Here

### Phase 0 — Compiler correctness (prerequisite for everything)

These open issues must be resolved before module splitting makes sense:

| Issue | Description | Why it blocks |
|-------|-------------|---------------|
| #531 | `Eq`/`Ord`/`Num` as real type classes | Monomorphic operators are not real Haskell |
| #616 | `ClassEnv` not persisted in `.rhi` | Multi-module type class dispatch is broken without this |
| #615 | GRIN evaluator dictionary-passing | Evaluator backend needs class dispatch to work |
| #566 | Declaration-order-independent inference | Module splitting immediately hits forward references |
| #623 | Where-clause bindings not in scope | Correctness issue that surfaces in `base` code |

### Phase 1 — Package infrastructure

- `rhc-pkg` tool: install, query, remove packages from the store
- Store layout at `~/.rhc/store/<arch>-<os>-<version>/`
- Package descriptor format (`.rhc-pkg` file, subset of Cabal syntax)
- Compiler flag `--package-db` to point at a store

### Phase 2 — Boot packages as real packages

- Split `lib/Prelude.hs` into `rhc-prim`, `rhc-internal`, `base`
- Boot packages pre-installed into the store at compiler build time
- `known.zig` and `env.zig` shrink to knowing the store path and boot package names only

### Phase 3 — `base` as pure Haskell

- `base` compiles with no `foreign import prim`
- The version boundary between `rhc-internal` and `base` is real and enforced
- Changing `rhc-internal`'s interface is a breaking change; changing `base` internals is not

### Phase 4 — Cabal compatibility (long-term north star)

- `rhc` CLI implements enough of the GHC command-line surface that Cabal can drive it
- Fork or patch `Cabal-the-library` to recognise `rhc` as a compiler flavour
- Users can write `compiler: rhc-0.1` in their `cabal.project`

---

## What This Is Not

- This is not a proposal to implement all phases now. Phases 1–4 depend on Phase 0,
  and Phase 0 has several open compiler bugs.
- This is not a Cabal replacement. The long-term goal is Cabal *compatibility*, not
  a parallel build tool.
- This is not a commitment to full Haskell 2010 `base`. The module structure mirrors
  GHC's, but only the functions Rusholme currently implements will be present.

# Decision 0001: PrimOps and RTS Architecture

**Status:** Proposed  
**Date:** 2026-02-22  
**Context:** How should Rusholme handle built-in functions like `putStrLn` without hardcoding a full `base` library?

---

## Problem Statement

Rusholme currently "cheats" by hardcoding ~40 known functions in `src/naming/known.zig`:
- Functions: `putStrLn`, `map`, `foldr`, `error`, etc.
- Types: `Int`, `Bool`, `IO`, etc.
- Classes: `Eq`, `Monad`, etc.

These are:
1. **Populated in the renamer** via `populateBuiltins()`
2. **Typed in the typechecker** via `initBuiltins()`
3. **Not implemented** — no evaluator/runtime exists

This approach doesn't scale. A real `base` package has thousands of definitions, and hardcoding them all is infeasible.

---

## Options Considered

### Option A: PrimOps + Minimal Prelude
Define a small set of primitive operations (PrimOps) that the runtime implements. Everything else is Haskell code calling these PrimOps.

### Option B: Tiny Runtime + FFI
Ship a minimal runtime library (Zig/C) exposing foreign functions. The compiler only knows about FFI; `base` calls into the runtime.

### Option C: GHC-Internal Style
Split into `rusholme-internal` (primops) and `rusholme-base` (standard library) with a package database.

### Option D: Self-Hosting Prelude in Zig
Write Prelude functions in Zig as part of the compiler, exposed as if they were Haskell.

### Option E: GRIN-Level PrimOps
Define PrimOps at the GRIN IR level. The GRIN evaluator dispatches PrimOps to an RTS written in Zig.

---

## Recommendation: Layered Approach (Option A + E)

Adopt a **PrimOp-centric architecture** where:

1. **~15-30 PrimOps** form the contract between compiler and RTS
2. **Prelude is Haskell source** that calls PrimOps
3. **RTS is written in Zig** and linked as a static library
4. **FFI to C** is a bridge mechanism, not the primary interface

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     Rusholme Compilation Pipeline                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Haskell ──► Parse ──► Rename ──► Typecheck ──► Core ──► GRIN          │
│                                                                  │       │
│   ┌──────────────────────────────────────────────────────────────┐     │
│   │                    PrimOp Lowering                            │     │
│   │   High-level: putStrLn, (+), (==)                            │     │
│   │   Low-level:  write_stdout#, add_Int#, eq_Int#               │     │
│   └──────────────────────────────────────────────────────────────┘     │
│                                                                  │       │
│   ┌──────────────────────────────────────────────────────────────┐     │
│   │                    GRIN Evaluator                             │     │
│   │   ┌────────────────────────────────────────────────────────┐ │     │
│   │   │              RTS (librusholme-rts.a)                   │ │     │
│   │   │   • PrimOp implementations (Zig)                       │ │     │
│   │   │   • Memory management (heap, GC)                       │ │     │
│   │   │   • IO subsystem                                       │ │     │
│   │   │   • FFI bridge to C                                    │ │     │
│   │   └────────────────────────────────────────────────────────┘ │     │
│   └──────────────────────────────────────────────────────────────┘     │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## PrimOp Design

### Canonical Definition

PrimOps are defined in `src/grin/primop.zig`:

```zig
pub const PrimOp = enum(u16) {
    // ── IO Primitives ─────────────────────────────────────────────────
    write_stdout,   // String -> IO ()
    read_stdin,     // IO String
    write_stderr,   // String -> IO ()
    
    // ── Arithmetic (unboxed) ──────────────────────────────────────────
    add_Int#,       // Int# -> Int# -> Int#
    sub_Int#,       // Int# -> Int# -> Int#
    mul_Int#,       // Int# -> Int# -> Int#
    neg_Int#,       // Int# -> Int#
    eq_Int#,        // Int# -> Int# -> Bool
    lt_Int#,        // Int# -> Int# -> Bool
    le_Int#,        // Int# -> Int# -> Bool
    
    // ── Comparison ───────────────────────────────────────────────────
    eq_Char#,       // Char# -> Char# -> Bool
    
    // ── Heap Operations ──────────────────────────────────────────────
    newMutVar#,     // a -> State# s -> (# State# s, MutVar# s a #)
    readMutVar#,    // MutVar# s a -> State# s -> (# State# s, a #)
    writeMutVar#,   // MutVar# s a -> a -> State# s -> State# s
    
    // ── FFI Bridge ───────────────────────────────────────────────────
    ccall,          // Generic FFI call (function pointer + args)
    
    // ── Control Flow ─────────────────────────────────────────────────
    error#,         // String -> a  (diverges)
    unreachable#,   // a  (compiler bug if reached)
};
```

### Naming Convention

- PrimOps end with `#` to match GHC convention (e.g., `add_Int#`)
- High-level Haskell functions (no `#`) are defined in Prelude in terms of PrimOps

### Example: `putStrLn` Implementation

**In Prelude (Haskell):**
```haskell
foreign import prim "write_stdout"
  writeStdout# :: String -> IO ()

putStrLn :: String -> IO ()
putStrLn s = writeStdout# (s ++ "\n")

putStr :: String -> IO ()
putStr = writeStdout#
```

**In RTS (Zig):**
```zig
// src/rts/io.zig
pub fn writeStdout(args: []const Value) !Value {
    const str = args[0].asString();
    try std.io.getStdOut().writeAll(str);
    return .unit;
}
```

**In GRIN Evaluator:**
```zig
fn evalPrim(alloc: Allocator, op: PrimOp, args: []const Value) !Value {
    return switch (op) {
        .write_stdout => rts.io.writeStdout(args),
        .read_stdin => rts.io.readStdin(args),
        .add_Int# => .{ .int = args[0].int + args[1].int },
        // ...
    };
}
```

---

## IO Representation

### Phase 1-2 (M0/M1): Direct Side-Effects

For initial implementation, IO operations are direct side-effects executed by the evaluator in order:

```grin
-- GRIN IR for: main = putStrLn "a" >> putStrLn "b"
main =
  _ <- eval (App putStrLn "a")
  _ <- eval (App putStrLn "b")
  unit
```

The evaluator maintains an "effects in order" invariant without explicit token threading.

**Pros:**
- Simpler to implement
- No need for `State# RealWorld` types initially
- Sufficient for strict sequencing (most IO)

**Cons:**
- Cannot support lazy IO (`readFile` returning content read on-demand)
- Less precise semantics for `unsafePerformIO`

### Phase 3+ (M2/M3): Token-Passing

Once lazy IO is required, migrate to token-passing:

```grin
-- GRIN IR with tokens
main =
  w0 <- eval RealWorld
  w1 <- eval (App write_stdout# "a" w0)
  w2 <- eval (App write_stdout# "b" w1)
  unit
```

**Benefits of token-passing:**
- Pure IR semantics (sequencing via data dependency)
- Enables lazy IO via `unsafeInterleaveIO`
- GRIN optimizations (dead token elimination, effect fusion)
- Matches GHC semantics precisely

**Tracking Issue:** [To be filed] "Implement token-passing IO for lazy semantics"

---

## Boxed vs Unboxed Types

### Surface Language

The surface Haskell language has both boxed and unboxed types:
- `Int` — boxed, may be a THUNK
- `Int#` — unboxed, always evaluated

### GRIN Layer

At the GRIN level:
- Boxed values are heap-allocated (via `store`)
- Unboxed values are raw machine words
- GRIN's `Eval` node forces thunks

```grin
-- boxed Int is a heap reference
x <- store (ConI 42)

-- unboxed Int# is immediate
y = 42#

-- GRIN optimizer can unbox when safe
```

### Optimization Path

1. **Initial:** All values are boxed at Core→GRIN translation
2. **Later:** GRIN optimizer performs unboxing analysis (strictness-based)
3. **Future:** Join points and strict fields enable aggressive unboxing

---

## FFI Design

### Syntax

```haskell
foreign import ccall "printf"
  printf :: CString -> IO ()

foreign import prim "write_stdout"
  writeStdout# :: String -> IO ()
```

- `foreign import prim` — calls a Rusholme PrimOp (compiler-known)
- `foreign import ccall` — calls a C function via FFI

### Implementation

The RTS provides a `ccall` PrimOp that:
1. Marshals Haskell values to C representation
2. Calls the C function via Zig's `@cCall`
3. Marshals the result back to Haskell

---

## Migration Path

### Phase 1 (M0/M1): Minimal PrimOps + Hardcoded Prelude

**Goal:** `main = putStrLn "Hello"` works

**Changes:**
1. Define ~10 PrimOps in `src/grin/primop.zig`
2. Keep `known.zig` for now (shrinks over time)
3. Add GRIN evaluator with PrimOp dispatch
4. Hardcode tiny Prelude in compiler

### Phase 2 (M1/M2): `foreign import prim` + External Prelude

**Goal:** Prelude is a Haskell file

**Changes:**
1. Implement `foreign import prim` syntax
2. Ship `rusholme-prelude/` as `.hs` files
3. `known.zig` shrinks to PrimOp names only
4. Renamer/typechecker learn PrimOp types

### Phase 3 (M2): FFI to C

**Goal:** Call arbitrary C functions

**Changes:**
1. Implement `foreign import ccall`
2. Add `PrimOp.ccall`
3. RTS bridges to C ABI

### Phase 4 (M3+): Package System + Full Base

**Goal:** Compile arbitrary Haskell packages

**Changes:**
1. Package database (`.rhi` interface files)
2. Dependency resolution
3. Multiple package versions

---

## Impact on Current Code

### `src/naming/known.zig`

Shrinks from ~40 entries to ~15 PrimOps:

```zig
// BEFORE
pub const Fn = struct {
    pub const putStrLn = name("putStrLn", 0);
    pub const print = name("print", 2);
    // ... 30+ functions
};

// AFTER
pub const PrimOp = struct {
    pub const write_stdout = name("write_stdout#", 0);
    pub const read_stdin = name("read_stdin#", 1);
    pub const add_Int = name("add_Int#", 100);
    // ... ~15 primops
};
```

### `src/typechecker/env.zig`

`initBuiltins()` shrinks to PrimOp types only.

### New Files

- `src/grin/primop.zig` — PrimOp enum and utilities
- `src/rts/` — Runtime system (io.zig, memory.zig, ffi.zig)
- `rusholme-prelude/` — Prelude as Haskell source

---

## Open Questions / Future Work

1. **Exception handling:** How should `throw`/`catch` be implemented at the RTS level?
2. **Concurrent IO:** Can the RTS support threads (via Zig's async or OS threads)?
3. **GC integration:** How do PrimOps interact with the garbage collector?
4. **Debugging:** How do we provide stack traces for PrimOp failures?

---

## References

- GHC's `ghc-prim` and `ghc-internal` packages
- Boquist's GRIN thesis (Chapter 5: Primitives)
- Johnsson's "An LLVM Backend for GRIN"
- GHC Wiki: "The PrimOp story"

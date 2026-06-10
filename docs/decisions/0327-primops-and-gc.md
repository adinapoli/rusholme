# Decision 0327: PrimOps and Garbage-Collection Integration

**Status:** Accepted
**Date:** 2026-06-10
**Tracks:** Issue [#327](https://github.com/adinapoli/rusholme/issues/327)
**Depends on:** Decision [0001](0001-primops-and-rts-architecture.md) (PrimOps and RTS Architecture),
[Issue #780](https://github.com/adinapoli/rusholme/issues/780) (shadow-stack ABI),
[Issue #779](https://github.com/adinapoli/rusholme/issues/779) (per-tag pointer masks)

---

## Problem

PrimOps that produce or consume `*Node` heap values must cooperate with
the Immix collector in three places:

1. Allocations done inside a PrimOp must come from the GC-managed heap
   (`rts_alloc`), not a raw allocator.
2. Every `*Node` value that a PrimOp's lowering keeps live across a
   collection point must be visible to the collector as a root.
3. Mid-PrimOp collection must not invalidate the values the PrimOp
   reads from the mutator's `*Node` SSAs.

The risks are familiar from GHC's RTS commentary on storage: a
collector triggered mid-PrimOp must see every reachable Haskell value,
and the PrimOp must not cache stale pointers across the collection
point.

---

## Mechanism

Rusholme's PrimOp lowering already satisfies the three requirements by
construction, but the chain of guarantees is non-obvious. This decision
records why.

### A. Allocation goes through the GC heap

Every PrimOp lowering that builds a `*Node` issues a `rts_alloc` call.
`rts_alloc` is exported by `src/rts/node.zig` and routes through the
`heap.gcAllocator()` interface — under `--rts=immix` that is the
Immix block allocator, including the auto-collect trigger (#781).
There is no raw-`malloc` path inside the PrimOp set.

### B. PrimOp arguments are rooted by the caller

PrimOp arguments are `*Node` SSAs produced in the caller's GRIN
function. The LLVM backend emits a `rts_shadow_push` at every `*Node`
SSA definition (#780, inlined per #788). By the time the PrimOp's IR
runs, every pointer-typed argument is already in the shadow-stack
buffer between the caller's `rts_shadow_save` and `rts_shadow_restore`
brackets. The collector therefore sees them as roots without any
PrimOp-side bookkeeping.

### C. PrimOp lowerings are inline, with no mid-PrimOp safepoints

Backend PrimOps fall into three lowering shapes:

- **Inline-IR instructions** (`emitInstruction` in `grin_to_llvm.zig`).
  Pure LLVM `add` / `icmp` / `getelementptr` sequences. They have no
  intermediate `rts_alloc` calls, so there is no collection point
  inside the PrimOp, and the `*Node` SSAs the lowering loads are
  unchanged after it completes.

- **Wrappers around `rts_alloc`** (`wrapComparisonAsBool`, the
  comparison-result boxing path, plus the `Pure ConstTagNode` / `Pure
  Unit` / `Store` paths described in decision 0001). These call
  `rts_alloc` exactly once. The `*Node` arguments that feed the
  allocation are already on the shadow stack from their caller-side
  definitions; the `rts_alloc` call itself is the only safepoint and
  the post-call code consumes the freshly-returned pointer in tail
  position, so no stale `*Node` is held across the alloc.

- **Foreign C calls** (`ccall`). Cross the C ABI to functions in the
  RTS (`rts_putStrLn`, `rts_putStr`, `rts_putChar`, `rts_error`).
  None of these allocate from the GC heap (they write to stdio /
  invoke `abort()`); collection cannot fire inside them. Their
  `*Node` arguments stay valid across the call without any extra
  rooting.

### D. PrimOp results that must survive subsequent allocations

A PrimOp's result is bound in the caller via the GRIN translator's
`bindAndRoot` helper — the same hook every other SSA goes through.
The first thing the caller does with a fresh PrimOp result is push it
onto the shadow stack. From that point on it is a root for every
collection until the function returns.

---

## Contract for new allocating PrimOps

When a new PrimOp is added that allocates more than once from the GC
heap (e.g. a future `newArray#`, the not-yet-implemented `newMutVar`
chain), the lowering must follow this contract:

1. **Use `rts_alloc`** for every heap allocation. Do not introduce a
   parallel allocator.

2. **Hold no `*Node` SSA across an internal `rts_alloc`.** Either:
   - Allocate first, then read the `*Node` arguments via
     `translateValToLlvm`, OR
   - Emit a temporary `rts_shadow_push` for the SSA before the
     allocation if the value cannot be re-derived from `self.params`.
     This pairs with a `rts_shadow_restore` snapshot — usually the
     surrounding function's `shadow_saved_top` is sufficient, since
     the PrimOp lives inside that function's frame.

3. **Bind the PrimOp's result via `bindAndRoot`** in the caller. The
   existing PrimOp emission paths in `translateAppToValue` and
   `translateBind` already do this.

4. **Document allocation behaviour** in `src/grin/primop.zig` next to
   the enum variant. Test coverage in
   `tests/e2e/e2e_327_primop_gc.hs` runs the PrimOp under
   `--rts=immix` with a small heap budget so collection fires inside
   it.

---

## Contract for `foreign import ccall` symbols

C functions reached via `ccall` (decision 0001 §FFI, issue
[#536](https://github.com/adinapoli/rusholme/issues/536)) split into
two classes:

- **Non-allocating** (current set: `rts_putStrLn`, `rts_putStr`,
  `rts_putChar`, `rts_error`). The caller's shadow stack roots their
  Haskell-pointer arguments by construction. No callee-side action is
  required.

- **Allocating** (none today; this contract applies to future
  additions). A C function that may call `rts_alloc` while holding
  Haskell `*Node` parameters must push them onto the shadow stack via
  `rts_shadow_push` on entry and call `rts_shadow_restore` on exit,
  using the same `rts_shadow_save` / `rts_shadow_restore` pair that
  Zig-emitted code uses. The C ABI signatures live in
  `src/rts/heap.zig`; importing them from C is a single
  `extern void rts_shadow_push(uint64_t)` etc. declaration.

The list of supported `ccall` symbols
(`PrimOp.isSupportedCCallSymbol`) is the gating point — adding any
new symbol forces an explicit decision on its GC behaviour.

---

## What this is *not*

This decision does not introduce any new compiler pass or runtime
function. It records the design that already follows from #780 (shadow
stack), #779 (precise pointer masks), and decision 0001 (PrimOps are
either inline IR or wrap a single `rts_alloc` call). The corresponding
verification test (`tests/e2e/e2e_327_primop_gc`) exercises this
design end-to-end so any future drift fails CI.

# GRIN eval: inline in the backend vs. callable at the GRIN level

**Issue:** [#520](https://github.com/adinapoli/rusholme/issues/520) — Reconcile GRIN-level eval with LLVM backend inline eval
**Status:** Decided — Option A. Long-term research tracked in [#732](https://github.com/adinapoli/rusholme/issues/732).
**Date:** 2026-06-09

## Context

GRIN has a distinguished `eval p` operation: fetch the node at `p`, and
if its tag is a function thunk (`F`-tagged) or indirection (`Ind`),
force/follow it; otherwise return the node as-is. The original
intention in `src/grin/translate.zig` was to *materialise* `eval`
(and `apply`) as ordinary GRIN definitions via
`generateEvalApply` — `generateEvalFunc` built a literal
`fetch p >>= \n -> case n of …` body, and `generateApplyFunc` was a
stub.

The LLVM backend never used those generated definitions. Instead,
`grin_to_llvm.zig::translateCase` *inlines* the eval loop at every
case scrutinee site, with phi nodes that follow `Ind` chains and
dispatch on the node tag directly.

This left the IR and the backend disagreeing about what `eval` is.

## Options considered

### Option A — Document the inline approach; delete the stubs

Keep the current backend behaviour (inline eval at every case
scrutinee) and explicitly mark `generateEvalApply` and friends as the
*ahistorical* design we did not take. Remove the dead helpers so the
codebase has one canonical answer.

- **Pros:** Reflects what the backend actually does. No risk of
  importing the never-tested generated code. Smaller IR surface to
  reason about. Mechanical change.
- **Cons:** GRIN-level optimisations (eval inlining, known-case
  elimination) cannot operate on `eval` because it does not exist as
  a function — they'd have to recognise the inline loop pattern.
  This is the long-term cost.

### Option B — Make the backend call a GRIN-generated `eval`

Resurrect `generateEvalApply`, finish `generateApplyFunc`, fix the
generated GRIN body so it actually drives forcing, and change
`translateCase` to lower scrutinees to a call into the generated
`eval`/`apply` instead of inlining the loop.

- **Pros:** GRIN IR matches what runs. Standard GRIN optimisations
  (Boquist 1999) can operate on the real eval mechanism. Inlining
  becomes a peephole pass at the GRIN level, not a special case in
  the backend.
- **Cons:** Substantial change. Touches GRIN IR, the LLVM backend, the
  closure/F-tag conventions (#386, #780), and the heap-points-to
  analysis (#44). The generated `apply` is currently a stub that
  returns Unit — making it correct end-to-end is a project in itself.
  No measured benefit until the GRIN-level optimisation passes
  (#7) exist to consume it.

## Decision

**Option A.** Delete the dead generators (`generateEvalApply`,
`generateEvalFunc`, `generateApplyFunc`, the `TagInfo`/`collectTags`
helpers) and treat the inline eval loop in `translateCase` as the
canonical design until the broader GRIN-optimisation epic (#7) makes
the switch worthwhile.

The architectural question is not closed — Option B remains the
"right" long-term design once we have a reason to need GRIN-level
optimisation passes. That research is tracked in
[#732](https://github.com/adinapoli/rusholme/issues/732); it should
reopen and motivate Option B *before* anyone re-adds a GRIN-level
`eval` definition. Re-adding it without first reasoning about the
end-to-end story (closure ABI, partial-application dispatch, points-to
analysis interaction) is what landed us in the inconsistent state #520
flagged in the first place.

## Consequences

- `src/grin/translate.zig` no longer contains `eval`/`apply`
  generators. The IR pretty-printer and downstream consumers see one
  fewer definition per program.
- `src/backend/grin_to_llvm.zig::translateCase` is the **sole**
  implementation of `eval` semantics. Future changes to thunk forcing
  (e.g. the shadow-stack precise-roots work in #780) edit this site.
- A future Option B PR will need to re-introduce these helpers (or
  successors) — there is no value in keeping skeletons around for
  that hypothetical world. Git history has them.

## References

- Boquist & Johnsson, *"The GRIN Project: A Compiler for Lazy
  Functional Languages"* (1996/1999).
- `src/backend/grin_to_llvm.zig::translateCase` — current eval site.
- Issue [#732](https://github.com/adinapoli/rusholme/issues/732) —
  long-term research on the GRIN-level eval/apply approach.

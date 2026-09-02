# Decision 939: Representation of First-Class `IO a` Values

**Status:** Accepted
**Date:** 2026-09-02
**Issue:** #939

## Context

#926 made `IO` actions usable as *values* — elements of a list handed to
`sequence_`, the `m` parameter of `instance Monad IO`'s `(>>=)`. To perform
such a value, `src/grin/translate.zig` wraps it in the `runIO` stub
(`performAction`), which the backend lowers to `__rhc_force`: the action is a
suspended thunk and forcing it is what running it means.

Forcing a thunk in GRIN *updates it in place* (memoisation — the essence of
call-by-need), which is exactly right for a pure value and exactly wrong for
an effect. The first performance of an action value rewrote its thunk to
`Ind → result`, so every later performance returned the memoised result and
the effect never ran again. `sequence_ acts >> sequence_ acts` printed `once`
where GHC prints it twice, and `replicateM_ n act` would run `act` once.

An `IO a` value needs a representation whose *performance is repeatable*.
This document records the chosen representation and its contract with the
GRIN calling convention.

## Options Evaluated

### 1. GHC's state-token function

`IO a ≅ State# RealWorld -> (# State# RealWorld, a #)`. An action is a
*function*; performing it is calling it with a state token, and calling it
twice runs it twice by construction. This is the representation GHC and the
GRIN literature (Boquist 1999) use, and it is where `State#` primops
(`newIORef#`, …) want to end up.

**Rejected for now.** It requires unboxed tuples and a `State#` primitive
type, neither of which exists in the IR today; threading the token through
every IO bind is a pipeline-wide change (Core types, translate, backend, RTS)
that would block a correctness bugfix on a large feature. It also interacts
with #941, which will re-home the IO `do`-lowering. Nothing in this decision
forecloses it: perform sites are centralised (see below), so migrating `IO`
to state-token functions later replaces the perform lowering at a handful of
sites and leaves the call sites untouched.

### 2. A non-updatable thunk flavour (distinct node tag for action thunks)

Allocate `IO a` values with a new tag flavour whose force semantics re-enter
the body on every force — including plain forces at case sites and return
sites.

**Rejected.** Distinguishing the flavour at *allocation* requires knowing
that the suspended expression is `IO`-typed. The Core→GRIN translator is
type-blind today (it works on names and uniques), so this would need a new
IO-ness analysis over Core threaded through every thunk-allocation site
(`translateLet`, `wrapWithLazyBindsForFunc`, `liftExprToThunkStore`, …) plus
a new tag flavour rippling through the tag registry, node format, force
dispatch, and the JIT. All of that to cover only the corner case where an
action thunk is reached by a *plain* force (strictness on an `IO` value)
instead of by a perform.

### 3. The perform operation is a first-class, non-destructive eval  ✅

An `IO a` value occupies exactly the same heap-node shapes as any other
suspended computation (an F-tag thunk, a saturated P-node). What makes `IO`
different is the *operation that consumes it*: performing an action value is
a distinct runtime operation, `__rhc_perform`, which dispatches exactly like
`__rhc_force` (follow `Ind`, call F-tag bodies, call saturated P-nodes, pass
WHNF through) but **never updates the node in place**. Every perform re-enters
the body; every performance of the same action value runs its effect again.
The distinction is planted where the compiler already knows an action is
being performed — the `runIO` stub that `performAction` plants at
`>>`/`>>=`-argument sites — so no type information is needed anywhere.

## Decision

Option 3.

> **An `IO a` value is a suspended computation like any other; performing it
> is an explicit, non-destructive eval (`__rhc_perform`). Effect repetition
> is a property of the perform operation, not of the node. Memoisation
> (`__rhc_force`) remains the exclusive business of pure eval.**

The calling-convention contract, extending `003-calling-convention.md`:

- `__rhc_force(ptr) -> ptr` — eval **with** in-place update. Call-by-need.
  Only for pure values. Result values may be cached by the code generator
  (per-variable WHNF cache): a second force of the same variable reuses the
  first result.
- `__rhc_perform(ptr) -> ptr` — eval **without** update. Call-by-effect.
  Re-enters the body on every call. The code generator must **not** cache a
  performed value: a later `runIO` of the same variable must emit a fresh
  call.
- Both share one eval loop; the backend emits `__rhc_perform` alongside
  `__rhc_force` (whole-program and shared force module), declares it external
  in per-def/REPL modules, and lowers every `runIO` site to it. `runIO` is
  *not* dropped: it is the marker of a perform site in GRIN (the mirror of
  the `apply` stub), and something must force a `Return(v)` action value at a
  structural bind — the new representation makes that force repeatable
  instead of removing it.

## Consequences and known corners

- **`sequence_ acts; sequence_ acts` runs the effect twice** — the thunk is
  never updated, so the second `runIO` re-enters `putStrLn`. Same for an
  action repeated in one list (`replicateM_ n act` semantics).
- **Pure payload inside a multiply-performed action is re-computed.**
  `let m = return (expensive 42) in m >> m` re-runs `expensive 42` per
  perform. GHC shares the pure payload (it is allocated outside the
  state-token lambda). This is unobservable for effects and matches the
  "an action re-executes its body" semantics; sharing is a pure-optimisation
  concern deferred until demand analysis can see `IO`.
- **A plain force of an action thunk still memoises** (strict arguments,
  `seq`-like demand, case-scrutinee eval): `__rhc_force` is unchanged, and
  forcing an `IO` value to WHNF *is* running it in this model — the same
  semantics the pre-#939 code had. Only the perform path is non-destructive.
  A later migration to state-token functions (option 1) subsumes this corner.
- **The backend must not treat performs as forces**: no `params`/`whnf_vars`
  caching across a perform, or dominated re-performances would be elided.

## References

- `src/grin/translate.zig` — `performAction`, `run_io_name` (perform sites)
- `src/backend/grin_to_llvm.zig` — the `runIO` interception, `emitEvalFunction`
- `docs/decisions/520-grin-eval-inline-vs-callable.md` — the decision that made
  eval a callable function; this one gives it a second flavour
- #926 (action values become first-class), #941 (do-notation will route
  through `instance Monad IO` once this lands), epic #845
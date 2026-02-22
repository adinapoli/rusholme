# Decision 042: Core to GRIN Translation Strategy

**Status:** Accepted
**Date:** 2026-02-22
**Issue:** #42

## Context

Rusholme's pipeline is: `Haskell Source -> Core -> GRIN -> Backend`. The Core IR
(System F_C, defined in `src/core/ast.zig`) is a typed, declarative lambda
calculus. The GRIN IR (`src/grin/ir.zig`) is an imperative monadic language
with explicit memory operations. The translation must bridge these two worlds,
making laziness, memory allocation, and evaluation order explicit.

This document answers the eight key questions posed in #42 and establishes
the translation strategy for #313, #314, #315, and #317.

Worked examples with concrete GRIN syntax for each rule are in the companion
document: `docs/references/core-to-grin-translation.md`.

## Translation Rules

### Q1: How do Core lambdas become GRIN function definitions?

**Strategy: Lambda lifting followed by flattening.**

A separate lambda lifting pass (#313) transforms the Core program so that all
lambdas are top-level. This pass:

1. Computes free variables for each nested lambda.
2. Lifts nested lambdas to top-level `Bind` entries, adding free variables
   as extra parameters.
3. Rewrites call sites to pass the captured free variables.

After lifting, the Core→GRIN translator (#314) converts each top-level binding
into a GRIN `Def` by collecting the chain of `Expr.Lam` binders into a single
parameter list:

```
Core:  f = \x -> \y -> body
GRIN:  f x y = [[ body ]]
```

**Rationale:** Separating lambda lifting from translation keeps both passes
simpler. Lambda lifting is a well-understood transformation (Johnsson 1985)
that can be tested independently. GRIN requires all functions to be top-level
`Def`s, so this is not optional.

### Q2: How are thunks represented?

**Strategy: F-tagged nodes on the heap.**

A thunk (suspended computation) is stored as an `F`-tagged node:

```
Core:  let x = f y in body
GRIN:  store (Ff [y]) >>= \p -> [[ body[x := p] ]]
```

The `F` tag (`TagType.Fun`) indicates the node is unevaluated. It captures the
function name and its arguments. The `store` returns a heap pointer that is
used in place of the original variable.

Forcing a thunk is done by the whole-program `eval` function (see Q6).

### Q3: How are partial applications represented?

**Strategy: P-tagged nodes with missing-argument count.**

When a function of arity `n` receives `k < n` arguments:

```
Core:  map f           -- map has arity 2, 1 arg supplied
GRIN:  store (P(1)map [f])
```

The `P(n-k)` tag (`TagType.Partial`) records how many arguments are still
missing. The captured arguments are stored in the node's fields.

When a partial application receives its final argument, the `apply` function
(see Q6) calls the underlying function with all accumulated arguments.

Over-application (more args than arity) is handled by chaining `apply` calls:

```
Core:  (f x) y z       -- f has arity 1
GRIN:  app f [x] >>= \r1 -> apply r1 y >>= \r2 -> apply r2 z
```

**Arity tracking:** The translator maintains a map from function names to their
arities, built from the Core program's top-level bindings. Application chains
(`Expr.App` nesting) are uncurried and compared against this map.

### Q4: How do constructors map to GRIN nodes?

**Strategy: C-tagged heap nodes.**

```
Core:  Just 42         -- constructor application
GRIN:  store (CJust [#42])

Core:  Nothing         -- nullary constructor
GRIN:  store (CNothing [])

Core:  Cons x xs       -- multi-field
GRIN:  store (CCons [x, xs])
```

The `C` tag (`TagType.Con`) marks a fully evaluated constructor. Constructor
names from `AltCon.DataAlt` map directly to `Tag { .tag_type = .Con }`.

### Q5: How does `case` translate?

**Strategy: Explicit eval + case.**

The scrutinee must be forced to WHNF before pattern matching:

```
Core:  case expr of { Just x -> e1; Nothing -> e2 }
GRIN:  [[ expr ]] >>= \p ->
         eval p >>= \val ->
           case val of
             (CJust [x])    -> [[ e1 ]]
             (CNothing [])  -> [[ e2 ]]
```

Pattern mapping:
- `AltCon.DataAlt` -> `CPat.NodePat` (match tag, bind fields)
- `AltCon.LitAlt` -> `CPat.LitPat`
- `AltCon.Default` -> `CPat.DefaultPat`

The Core `Case.binder` (which binds the scrutinee value in GHC style) maps to
the bind pattern before the GRIN case.

**Note:** The initial translation conservatively inserts `eval` on every
scrutinee. GRIN optimisation passes (evaluated case elimination, #46) will
later remove redundant `eval` calls where the value is already known to be
evaluated.

### Q6: How is `eval` implemented?

**Strategy: Whole-program generated function.**

The `eval` function is not hand-written — it is generated from the complete
set of tags in the program (#315). It has one branch per known tag:

```
eval p =
  fetch p >>= \node ->
    case node of
      -- Constructors: already evaluated, return directly
      (CJust [x])    -> return (CJust [x])
      (CNothing [])  -> return (CNothing [])
      (CCons [h, t]) -> return (CCons [h, t])
      -- Thunks: call function, memoize result, return
      (Ff [y])       -> app f y >>= \result ->
                           update p result >>= \_ ->
                             return result
      -- Partial applications: already a value, return directly
      (P(1)map [f])  -> return (P(1)map [f])
      ...
```

Similarly, `apply` is generated to handle applying one argument to a value:

```
apply f x =
  case f of
    (P(1)g [a])    -> app g [a, x]       -- saturated: call
    (P(2)g [a])    -> store (P(1)g [a, x])  -- still partial
    ...
```

**Rationale:** This is GRIN's whole-program nature. Because `eval` and `apply`
enumerate all possible tags, GRIN optimisations can later narrow them (sparse
case, dead code elimination). The generated functions are ordinary GRIN `Def`s.

### Q7: How are let bindings handled?

**Strategy: Lazy let = store thunk + bind. Strict let = eval immediately.**

Non-recursive let:

```
Core:  let x = f y in body
GRIN:  store (Ff [y]) >>= \p -> [[ body[x := p] ]]
```

Recursive let (mutually recursive bindings):

```
Core:  let rec { a = f b; b = g a } in body
GRIN:  store (Ff [dummy]) >>= \p_a ->
         store (Fg [dummy]) >>= \p_b ->
           update p_a (Ff [p_b]) >>= \_ ->
             update p_b (Fg [p_a]) >>= \_ ->
               [[ body[a := p_a, b := p_b] ]]
```

Recursive bindings require allocating placeholder nodes first, then
backpatching with `update` once all pointers are known.

**Simplification for M1:** For the initial implementation, we can require
that recursive bindings are always function definitions (which is the common
case in Haskell). This avoids backpatching — recursive functions can be
lambda-lifted and called by name without heap allocation.

### Q8: How are literals handled?

**Strategy: Direct mapping.**

```
Core:  42       (Expr.Lit with Literal.Int)
GRIN:  return #42   (Expr.Return with Val.Lit)

Core:  'A'      (Expr.Lit with Literal.Char)
GRIN:  return #'A'
```

`Core.Literal` and `grin.Literal` are intentionally parallel types with the
same variants (Int, Float, Char, String).

Type and coercion nodes (`Expr.Type`, `Expr.Coercion`) are erased — they have
no runtime representation and are simply dropped during translation.

## Implementation Plan

The translation is decomposed into four sub-issues with a clear dependency chain:

1. **#313 — Lambda lifting** (Core→Core pass, prerequisite)
2. **#314 — Simple expression translation** (Core→GRIN, the main translator)
3. **#315 — eval/apply generation** (whole-program, post-translation)
4. **#317 — Partial/over-application** (extends #314 with arity tracking)

## Open Questions for Future Work

- **Strictness analysis:** Could allow `let` bindings to skip thunk allocation
  when the value is known to be needed. Deferred to GRIN optimisation passes.
- **Recursive let backpatching:** The placeholder+update strategy works but is
  inefficient. A better approach may emerge once the evaluator (#318-#320) is
  operational and we can observe real programs.
- **String representation:** Currently `Literal.String` holds `[]const u8`.
  The runtime representation of strings (packed, cons-list, rope) is an open
  question that affects constructor mapping.

## References

- Boquist, U. (1999). *Code Optimisation Techniques for Lazy Functional
  Languages*. PhD thesis, Chalmers. Chapter 4.
- Podlovics, Hruska & Penzes (2020). "A Modern Look at GRIN". Section 3.
- Johnsson, T. (1985). "Lambda Lifting: Transforming Programs to Recursive
  Equations".
- GHC/GRIN project: https://github.com/grin-compiler/ghc-grin
- Worked examples: `docs/references/core-to-grin-translation.md`
- Core IR: `src/core/ast.zig`
- GRIN IR: `src/grin/ir.zig`

# Core to GRIN Translation — Worked Examples

> Purpose: Concrete examples of how each Core IR construct maps to GRIN IR,
> using Rusholme's actual type definitions from `src/core/ast.zig` and
> `src/grin/ir.zig`.
>
> This document is a companion to the formal research decision for #42.
> It is not a specification — it captures intuition and worked examples
> to guide the implementation in #43.

## Pipeline Context

```
Haskell Source → Lexer → Parser → Typecheck/Desugar → Core → GRIN → Backend
                                                       ▲        ▲
                                                   typed,    imperative,
                                                   declarative  explicit memory
```

Core is a typed lambda calculus (System F_C). It says *what* to compute.
GRIN is an imperative monadic IR. It says *how* memory works: where things
are allocated (`store`), read (`fetch`), and overwritten (`update`).

The translation makes three things that are implicit in Core explicit in GRIN:

1. **Laziness** — thunk allocation and forcing
2. **Memory** — heap nodes for constructors and closures
3. **Evaluation order** — monadic sequencing via `Bind`

## Tag Conventions

GRIN nodes carry tags that distinguish their role (see `grin/ir.zig: TagType`):

| Tag prefix | Meaning | Example |
|------------|---------|---------|
| `C` | Data constructor | `CJust`, `CCons`, `CNil` |
| `F` | Function closure / thunk | `Fmap`, `Ffoldr` |
| `P(n)` | Partial application (missing `n` args) | `P(1)map` |

## 1. Constructors → Tagged Heap Nodes

Core constructors become `store` of a `CTag` node.

```
-- Core (Expr.App of constructor):
Just 42

-- GRIN:
store (CJust [#42])           -- allocate CJust node on heap, return pointer
```

A nullary constructor:

```
-- Core:
Nothing

-- GRIN:
store (CNothing [])
```

A multi-field constructor:

```
-- Core:
Cons x xs

-- GRIN:
store (CCons [x, xs])
```

**Mapping:** `Core.AltCon.DataAlt` names become `Tag { .tag_type = .Con }` in GRIN.
Constructor fields become the `fields` slice of `Val.ConstTagNode`.

## 2. Let Bindings → Thunk Allocation (store)

In Core, `let` is lazy — the RHS is not evaluated until needed. In GRIN,
this becomes a heap allocation of a thunk (an `F`-tagged node).

```
-- Core (Expr.Let, NonRec):
let x = f y
in body

-- GRIN:
store (Ff [y]) >>= \p ->       -- allocate thunk for (f y), bind pointer to p
  [[ body[x := p] ]]           -- translate body, replacing x with pointer p
```

The thunk `(Ff [y])` captures the function `f` and its argument `y`. It is
*not* evaluated yet — it is just stored on the heap.

**Mapping:**
- `Core.Bind.NonRec` → `Expr.Bind` with `Expr.Store` on the LHS
- The binder becomes a `Val.Var` pattern in the bind
- Recursive bindings (`Core.Bind.Rec`) need backpatching or fixed-point
  allocation (store placeholder nodes, then update with final values)

## 3. Forcing a Thunk — The eval Protocol

When something needs the value of a thunk, the GRIN `eval` function forces it:

```
-- GRIN eval function (generated per-program):
eval p =
  fetch p >>= \node ->            -- read the heap node
    case node of
      (CJust [x])    -> return (CJust [x])     -- already a value: return it
      (CNothing [])  -> return (CNothing [])    -- already a value: return it
      (Ff [y])       -> app f y >>= \result ->  -- unevaluated: call the function
                          update p result >>= \_ ->  -- memoize (overwrite thunk)
                            return result
      ...                                       -- one branch per known tag
```

Key insight: `eval` is **whole-program** — it has a branch for every constructor
and function tag in the entire program. This is why GRIN requires whole-program
compilation, and also why it can optimise so aggressively (it knows the complete
set of possible tags).

**Mapping:**
- `fetch` → `Expr.Fetch { .ptr = name, .index = null }`
- `update` → `Expr.Update { .ptr = name, .val = result }`
- The case branches cover all `TagType.Con` (return directly) and
  `TagType.Fun` (call and update) variants

## 4. Case Expressions → eval + case

Core `case` evaluates its scrutinee to WHNF and branches. In GRIN, the
forcing is explicit:

```
-- Core (Expr.Case):
case expr of
  Just x  -> e1
  Nothing -> e2

-- GRIN:
[[ expr ]] >>= \scrutinee_ptr ->
  eval scrutinee_ptr >>= \val ->     -- force to WHNF
    case val of
      (CJust [x])    -> [[ e1 ]]
      (CNothing [])  -> [[ e2 ]]
```

If the scrutinee is already known to be evaluated (e.g. a literal or a
variable that was already forced), the `eval` call can be skipped. This
is one of GRIN's key optimisations ("evaluated case elimination"), but
it happens in analysis passes, not during initial translation.

**Mapping:**
- `Core.Alt` → `grin.Alt`, with `Core.AltCon.DataAlt` becoming `CPat.NodePat`
- `Core.AltCon.LitAlt` → `CPat.LitPat`
- `Core.AltCon.Default` → `CPat.DefaultPat`
- The `Core.Case.binder` (which binds the scrutinee value) maps to the
  bind pattern before the GRIN case

## 5. Lambda Abstractions → GRIN Function Definitions

Core lambdas at the top level are "lambda-lifted" into GRIN `Def`s:

```
-- Core (top-level Bind):
f = \x -> \y -> x + y

-- GRIN (after flattening nested lambdas):
f x y =
  eval x >>= \x_val ->             -- force argument x
    eval y >>= \y_val ->           -- force argument y
      _prim_int_add x_val y_val    -- call primitive
```

Nested lambdas are flattened: `\x -> \y -> body` becomes a single
definition `f x y = ...` with both parameters.

**Mapping:**
- `Core.Expr.Lam` chains → single `grin.Def` with all parameters collected
- `Core.BindPair` at top level → `grin.Def { .name, .params, .body }`
- Arguments may or may not need `eval` depending on strictness (the initial
  translation conservatively evals everything; optimisation removes redundant evals)

## 6. Function Application

### Fully applied (known arity)

```
-- Core (Expr.App chain):
f x y     -- where f has arity 2

-- GRIN:
app f [x, y]
```

### Partial application (fewer args than arity)

```
-- Core:
map f     -- map has arity 2, only 1 arg supplied

-- GRIN:
store (P(1)map [f])            -- store partial application node, missing 1 arg
```

### Over-application (more args than arity)

```
-- Core:
(f x) y z   -- where (f x) returns a function

-- GRIN:
app f [x] >>= \result ->
  apply result [y] >>= \result2 ->
    apply result2 [z]
```

The `apply` function handles calling a value that might be a partial
application or a function pointer.

**Mapping:**
- `Core.Expr.App` chains are uncurried: collect the function and all arguments
- Arity comparison determines whether it's a direct `Expr.App`, a `store` of
  a `P(n)` node, or a sequence of `app` + `apply` calls

## 7. Literals

Literals map directly:

```
-- Core (Expr.Lit):
42

-- GRIN:
return #42                     -- Val.Lit { .Int = 42 }
```

```
-- Core:
'A'

-- GRIN:
return #'A'                    -- Val.Lit { .Char = 'A' }
```

**Mapping:** `Core.Literal` → `grin.Literal` (the types are intentionally parallel).

## 8. Type Erasure

Core's `Expr.Type` and `Expr.Coercion` nodes have no runtime representation.
They are simply dropped during translation:

```
-- Core:
f @Int x          -- type application of f to Int, then to x

-- GRIN:
app f [x]         -- the @Int is erased
```

## 9. Recursive Let Bindings

Mutual recursion requires allocating placeholder nodes first, then
updating them:

```
-- Core (Expr.Let, Rec):
let rec
  a = f b
  b = g a
in body

-- GRIN:
store (Ff [dummy_b]) >>= \p_a ->       -- allocate with placeholder
  store (Fg [dummy_a]) >>= \p_b ->     -- allocate with placeholder
    update p_a (Ff [p_b]) >>= \_ ->    -- backpatch a's thunk with real b
      update p_b (Fg [p_a]) >>= \_ ->  -- backpatch b's thunk with real a
        [[ body[a := p_a, b := p_b] ]]
```

This is the trickiest part of the translation and may benefit from a
simpler strategy initially (e.g. requiring that recursive bindings are
always functions, which can be lambda-lifted without backpatching).

## Summary Table

| Core construct | GRIN translation | Key GRIN operations |
|---------------|-----------------|-------------------|
| Constructor application | `store (CTag [fields])` | `Store` |
| `let x = e in body` | `store (FTag [args]) >>= \p -> body` | `Store`, `Bind` |
| `case e of alts` | `eval e >>= \v -> case v of alts` | `Fetch`, `Case`, `Bind` |
| Lambda (top-level) | `Def { name, params, body }` | `Def` |
| Function application | `app f [args]` | `App` |
| Partial application | `store (P(n)Tag [args])` | `Store` |
| Literal | `return #lit` | `Return` |
| Type / Coercion | (erased) | — |
| Recursive let | store + backpatch via `update` | `Store`, `Update`, `Bind` |

## References

- Boquist, U. (1999). *Code Optimisation Techniques for Lazy Functional
  Languages*. PhD thesis, Chalmers. Chapter 4: "Compiling Lazy Languages to GRIN".
- Podlovics, Hruska & Penzes (2020). "A Modern Look at GRIN". Section 3.
- GHC/GRIN project: https://github.com/grin-compiler/ghc-grin
- Rusholme Core IR: `src/core/ast.zig`
- Rusholme GRIN IR: `src/grin/ir.zig`

# Decision 005: Typechecking Approach for Rusholme

**Status:** Accepted
**Date:** 2026-02-18
**Issue:** (research issue — TBD)

## Context

With the parser complete, the next major pipeline stage is:

```
AST → [Renamer] → [Typechecker] → [Desugarer] → Core IR
```

None of these stages exist yet. This document decides the algorithm and
architecture for the typechecking and desugaring pipeline, with the explicit
goal of compiling `main = putStrLn "Hello"` as an ELF binary (M1) by
mid-March 2026.

---

## How GHC Does It (Reference Architecture)

GHC's frontend pipeline after parsing has four distinct stages, each with its
own data type:

```
HsSyn RdrName   -- parser output: raw reader names (bare strings)
    ↓ Renamer
HsSyn Name      -- fully-resolved names, scope-checked
    ↓ Typechecker
HsSyn Id        -- names annotated with types, constraints solved
    ↓ Desugarer
Core (System F_C)
```

### Renamer
Resolves qualified names (`Map.lookup` → `Data.Map.lookup_u42`), builds
`GlobalRdrEnv` / `LocalRdrEnv`, checks for undefined names, handles fixity
declarations, and produces a renamed AST where every identifier is globally
unique.

### Typechecker (OutsideIn(X))
GHC implements **OutsideIn(X)** (Vytiniotis, Peyton Jones, Schrijvers,
Sulzmann, JFP 2011) — a constraint-based Hindley-Milner extension that handles
GADTs, type families, and local type assumptions.

Key properties:
- **Constraint generation**: Walk AST top-down, collecting `Wanted` constraints
  (equality, class) without solving them immediately.
- **OutsideIn solving**: User-provided type signatures act as top-down
  `Given` constraints that guide local inference. Iterative fixed-point loop
  alternates between simplification and residual emission.
- **Evidence terms (`EvTerm`)**: Every solved constraint produces a proof term
  that the desugarer uses to insert dictionary arguments for type classes.
- **Type classes** → dictionary passing: `Show a =>` becomes a `Dict_Show_a`
  argument in Core.

### Desugarer
Mechanical translation of typed `HsSyn Id` to Core (System F_C):
- Multi-equation function bindings → nested `case`
- Guards → `if-then-else` / `case` on `Bool`
- `do`-notation → `(>>=)` / `(>>)` chains
- `where` → `let`
- List/tuple syntax → constructor applications
- Type class dictionaries (from evidence terms) → explicit lambda arguments

**Key design decision by GHC:** *typecheck before desugar*. Type errors are
reported against readable surface syntax, not desugared Core. This is a huge
UX win — we adopt it too.

---

## Options Evaluated

### A. Full OutsideIn(X)
- Handles GADTs, type families, rank-N types, local assumptions
- Paper is 60+ pages; GHC's implementation is tens of thousands of lines
- **Verdict**: wildly over-engineered for M1. `putStrLn "Hello"` needs none of
  this. Can be evolved towards later.

### B. Classic Algorithm W (Damas-Milner)
- Complete for rank-1 polymorphism; Robinson unification; let-generalisation
- Used by most toy compilers (WYAH, mini-haskell, etc.)
- Type classes are an awkward bolt-on (separate dictionary-passing pass)
- **Verdict**: solid foundation, but the architecture is a bit ad hoc for our
  clean pipeline model.

### C. Bidirectional Type Checking (Dunfield & Krishnaswami, ICFP 2013)
- Mixes *synthesis* mode (infer type bottom-up) and *checking* mode (verify
  expression has expected type top-down).
- Principled, clean, relatively easy to implement.
- Excellent localisation of errors: at each node you know whether you are
  synthesising or checking, so the error site is precise.
- Naturally supports rank-2 type annotations (functions with `forall` in
  argument position) without full unification machinery.
- Reference implementation: github.com/ollef/Bidirectional (Haskell, ~600 LOC).
- The 2020 survey paper "Bidirectional Typing" (Dunfield & Krishnaswami,
  arXiv:1908.05839) traces all variants.
- **Verdict**: the right modern choice for a clean, readable implementation.

### D. Constraint-based Elaboration (Lean/Agda style)
- Constraint generation and solving are fully separated.
- Elaborator converts surface AST to typed Core, inserting solved constraints
  along the way.
- Cleanest architecture for our pipeline model (generation → solving →
  elaboration are separate modules with clear interfaces).
- **Verdict**: the right *architecture* — we combine it with bidirectional
  checking as the generation strategy.

---

## Recommendation: Bidirectional TC + Constraint Elaboration (Simplified)

We adopt a **hybrid** that takes the best of each option:

```
Renamed AST
    ↓ Bidirectional Typechecker (synthesis + checking modes)
      → emits Wanted constraints (equality only for M1)
    ↓ Constraint Solver (Robinson unification + substitution)
      → produces type substitution σ
    ↓ Elaborator / Desugarer
      → applies σ, inserts type annotations, produces Core IR
Core IR
```

### Rationale

1. **Bidirectional is simpler and better-specified than Algorithm W** for our
   use case. Algorithm W fuses generation and solving in a single recursive
   walk, making it hard to give good error messages or to extend later.
   Bidirectional separates the two concerns cleanly.

2. **Constraint-based elaboration maps naturally to our pipeline**. The
   typechecker is purely a constraint *generator*. The solver is a separate,
   independently testable module. The elaborator is a separate pass. This
   mirrors the Parnas decomposition principle in DESIGN.md.

3. **M1 needs only equality constraints**. To compile `main = putStrLn "Hello"`
   we need: function application, string literals, `IO ()`, `String`, and
   `putStrLn :: String -> IO ()`. There are no overloaded operators, no type
   class resolution, no polymorphism beyond what's in a fixed built-in
   environment. Equality constraints (τ ~ σ) solved by unification are
   sufficient.

4. **Type classes come in M2**. Dictionary passing can be added as an
   extension to the constraint solver: class constraints (`Show a`) become
   `Wanted` constraints that the solver resolves by looking up instances and
   emitting dictionary arguments into Core. This is a well-isolated addition.

5. **Aligns with the existing Core IR**. `core.ir.CoreType` already has
   `TyVar`, `TyCon`, `FunTy`, `ForAllTy`. The elaborator just needs to
   fill these in from the solved substitution.

6. **Esoteric bonus**: Bidirectional type checking is more modern than
   Algorithm W, featured in recent languages (Idris, Lean, Hazel), and a
   legitimate research contribution to highlight. It fits the "experiment with
   cool stuff" mantra from DESIGN.md.

---

## Pipeline Stages in Detail

### Stage 0: Renamer (new stage)

**Input:** `ast.Module` (with bare `[]const u8` names)
**Output:** `RenamedModule` (with unique `naming.Name` everywhere)

Operations:
- Resolve every identifier to a `Name` using `UniqueSupply.freshName`
- Build a `Scope` (stack of `HashMap([]const u8, Name)`)
- Check that every reference resolves; emit `Diagnostic` for undefined names
- Handle import/export tables (initially: treat everything as in scope)
- Collect fixity declarations (already available from parser)

**This stage does not do any type inference.** Names only.

### Stage 1: Typechecker (Bidirectional)

**Input:** Renamed AST + initial `TyEnv` (built-in types and functions)
**Output:** Typed AST + constraint set `[]Constraint`

Two modes per expression node:
- `synth(expr) → (TypedExpr, HType)` — infer the type
- `check(expr, HType) → TypedExpr` — verify the type

`HType` is the typechecker's *internal* type representation — it differs from
`CoreType` in that it contains **unification metavariables** (`?0`, `?1`, …),
i.e. mutable cells that get filled in by the solver.

Constraints emitted: `Constraint.Eq(HType, HType, SourceSpan)` for M1.

### Stage 2: Constraint Solver

**Input:** `[]Constraint` from the typechecker
**Output:** `Substitution` (map from metavariable index → `HType`)

Algorithm: Robinson unification with occurs check.
- Walk each `Eq(τ, σ)` constraint
- Unify `τ` and `σ`, extending the substitution
- Occurs check: reject `?0 ~ [?0]` (would produce an infinite type)
- On failure: emit a structured `Diagnostic` with the two conflicting types
  and the source span of the constraint

### Stage 3: Elaborator / Desugarer

**Input:** Typed AST + solved `Substitution`
**Output:** `core.ir.CoreProgram`

Two responsibilities:
1. **Elaborate**: Apply substitution to all `HType`s, converting them to
   `CoreType`. Every `Id` binder gets its final `CoreType`.
2. **Desugar**: Mechanically lower Haskell constructs:
   - Multi-equation bindings → `Lam` + `Case`
   - Guards → `Case` on `Bool` or nested `if`
   - `do`-notation → `App (App bind m) (Lam p body)`
   - `where` → `Let (NonRec ...)`
   - List literals → `Cons`/`Nil` constructor applications
   - Tuple literals → constructor applications
   - Sections → `Lam` wrapping

---

## What "HType" Looks Like

The typechecker needs its own type representation distinct from `CoreType`
because it must support mutable unification variables:

```zig
pub const HType = union(enum) {
    /// Unification metavariable — mutable, filled in by solver.
    Meta: MetaVar,
    /// Rigid type variable (from a forall binder or function signature).
    Rigid: Name,
    /// Type constructor application: `Maybe Int`, `Int`, `IO ()`.
    Con: struct { name: Name, args: []const HType },
    /// Function type: a -> b.
    Fun: struct { arg: *const HType, res: *const HType },
    /// Polymorphic type: forall a. ...
    ForAll: struct { binder: Name, body: *const HType },
};

pub const MetaVar = struct {
    id: u32,
    ref: ?*HType,   // null = unsolved; non-null = solution
};
```

The key is `MetaVar.ref` — an optional pointer that the solver fills in. This
is a standard technique called *mutable metavariables* (used by GHC, Lean,
Agda). It avoids threading the substitution explicitly through every recursive
call during unification.

Post-solving, `HType → CoreType` is a straightforward traversal that follows
`MetaVar.ref` chains and converts the result.

---

## M1 Scope (Minimal to Compile `putStrLn "Hello"`)

For M1 we need to typecheck exactly this program:

```haskell
main :: IO ()
main = putStrLn "Hello"
```

Required:
- Type `String` = `[Char]` (built into TyEnv)
- Type `IO a` (built-in type constructor)
- `putStrLn :: String -> IO ()` (built into TyEnv)
- `main :: IO ()` (top-level signature)
- Checking a string literal against `String`
- Function application typechecking

Not required for M1:
- Type class resolution (no `Show`, `Eq`, etc.)
- Polymorphic let-generalisation
- Pattern matching exhaustiveness
- GADTs, type families, rank-N types
- Import resolution (built-in env is enough)

---

## Issue Breakdown (Proposed)

New issues to create, in dependency order:

| # | Title | Deps | Priority |
|---|-------|------|----------|
| NEW | Research: Typechecking approach (this doc) | — | critical |
| NEW | Implement Renamer: resolve AST names to unique `Name`s | #27, #69 | critical |
| NEW | Define `HType`: internal type representation with metavariables | #34 | critical |
| NEW | Implement Robinson unification with occurs check over `HType` | HType | critical |
| NEW | Implement `TyEnv`: scoped type environment | HType | critical |
| NEW | Implement Constraint Solver: equality constraints + substitution | Unification | high |
| #36 | *(repurposed)* Implement bidirectional typechecker (synth + check) | Renamer, HType, TyEnv | critical |
| #38 | Implement desugarer / elaborator: typed AST → Core IR | #36, Solver | critical |
| #35 | Implement Core IR pretty-printer | #34 ✓ | high |
| #39 | Implement Core lint | #34 ✓ | medium |

Existing issues #36 and #38 should have their descriptions updated on GitHub to
reflect the bidirectional approach and the new stage breakdown.

---

## References

- Dunfield & Krishnaswami, *"Complete and Easy Bidirectional Typechecking for
  Higher-Rank Polymorphism"*, ICFP 2013.
  PDF: https://www.cl.cam.ac.uk/~nk480/bidir.pdf
- Dunfield & Krishnaswami, *"Bidirectional Typing"* (survey), arXiv 2020.
  https://arxiv.org/abs/1908.05839
- Vytiniotis, Peyton Jones, Schrijvers, Sulzmann, *"OutsideIn(X): Modular Type
  Inference with Local Assumptions"*, JFP 2011.
  https://simon.peytonjones.org/outsideinx/
- Jones, *"Typing Haskell in Haskell"*, Haskell Workshop 1999. (~500 LOC HM
  in Haskell — excellent reference implementation)
- Peyton Jones et al., *"Practical type inference for arbitrary-rank types"*,
  JFP 2007.
- AOSA Book: *"The Glasgow Haskell Compiler"* chapter.
  https://aosabook.org/en/v2/ghc.html
- ollef/Bidirectional (Haskell reference implementation of Dunfield-Krishnaswami):
  https://github.com/ollef/Bidirectional

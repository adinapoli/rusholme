# Design: `deriving` Mechanism for Stock Classes

**Issue:** [#679](https://github.com/adinapoli/rusholme/issues/679)
**Date:** 2026-05-17
**Status:** Approved (brainstorming)

## Summary

Implement Haskell 2010 `deriving` clauses for the stock classes `Eq`, `Ord`,
`Show`, `Bounded`, and `Enum`, plus newtype deriving (via stock-equivalence,
since `coerce` is deferred). The parser already preserves `deriving` lists on
data/newtype declarations; this work adds a new pipeline pass that walks the
parsed module, synthesizes surface-level `InstanceDecl` AST nodes for every
clause, and inserts them before the renamer runs. The renamer and typechecker
then process the synthesized instances exactly as if the user had written them.

## Scope

**In scope:**

- Synthesize `Eq`, `Ord`, `Show`, `Bounded`, `Enum` instances from `deriving`
  clauses on `data` and `newtype` declarations.
- Honour standalone `deriving instance C T` declarations (existing
  `DerivingDecl` AST node) by lowering to the same synthesis path.
- Newtype deriving for the five stock classes implemented as stock-equivalence
  on the single underlying field (semantically identical to GHC for these
  classes).
- Add the missing `Ord`, `Bounded`, `Enum` class definitions and built-in
  instances to `lib/Prelude.hs`.
- Add diagnostic codes and span-faithful error reporting for non-derivable
  clauses.

**Out of scope (file follow-up issues):**

- `Coercible` class, `coerce` primop, role system, full `deriving newtype`
  strategy for arbitrary classes.
- `deriving Generic`, `Generic1`, `GHC.Generics` compatibility (already
  tracked by [#680](https://github.com/adinapoli/rusholme/issues/680)).
- `DerivingVia`, `DerivingStrategies` GHC extensions.
- Full `ShowS` / `showsPrec` / precedence-aware `Show` (Prelude uses the
  simplified single-method form; matching that here).
- Derived `Read`.
- Optimisation of `compare` cross-constructor dispatch beyond the naive nested
  case.

## Decisions

| # | Question | Decision |
|---|---|---|
| 1 | Class scope | All 5 stock + newtype; extend Prelude to add missing classes |
| 2 | Pipeline placement | New pass between parser and renamer |
| 3 | PR slicing | Single PR closing #679 (Prelude additions + deriving pass together) |
| 4 | Newtype strategy | Stock-equivalence (defer `coerce` to follow-up) |
| 5 | Synthesis approach | Source-AST template construction (Approach A) |

## Architecture

### Pipeline placement

```
source
  → frontend/parser   (preserves `deriving` clauses on DataDecl/NewtypeDecl)
  → deriving/deriving (NEW: walks module, synthesizes InstanceDecl per clause)
  → renamer
  → typechecker
  → core/desugar
  → grin → backend
```

### Entry point

```zig
// src/deriving/deriving.zig
pub fn derive(
    arena: std.mem.Allocator,
    module: *ast.Module,
    diags: *DiagnosticCollector,
) DeriveError!void
```

Mutates `module.decls` in place, appending one `InstanceDecl` per
`(data type, class name)` pair found in every `DataDecl.deriving`,
`NewtypeDecl.deriving`, and standalone `DerivingDecl`. Pure of side effects
beyond `module.decls` and `diags`. No global state, no class env access — the
typechecker is the sole arbiter of whether the synthesised body is
well-formed.

### Module layout

```
src/deriving/
├── deriving.zig          -- entry point: derive(arena, module, diags)
├── eq.zig                -- synthEqInstance
├── ord.zig               -- synthOrdInstance
├── show.zig              -- synthShowInstance
├── bounded.zig           -- synthBoundedInstance
├── enum_class.zig        -- synthEnumInstance
├── builder.zig           -- shared AST construction helpers
└── shape.zig             -- DataShape classification
```

`builder.zig` provides small constructors that wrap the tedium of building
`ast.Expr`, `ast.Pat`, `ast.Match`, `ast.InstanceDecl` nodes with explicit
spans:

```zig
pub fn mkVar(arena, name, span) ast.Expr
pub fn mkApp(arena, f, args, span) ast.Expr
pub fn mkConPat(arena, name, sub_pats, span) ast.Pat
pub fn mkCase(arena, scrutinee, arms, span) ast.Expr
pub fn mkInstance(arena, ctx, head, binds, span) ast.InstanceDecl
pub fn mkAndChain(arena, exprs, span) ast.Expr   -- folds with &&, base True
```

`shape.zig` classifies a `DataDecl` (or `NewtypeDecl` treated as a one-con
data) into one of:

- `Enumeration` — all constructors are nullary. Legal for Eq, Ord, Show,
  Bounded, Enum.
- `SingleProduct` — exactly one constructor with at least one field. Legal for
  Eq, Ord, Show, Bounded.
- `SumOfProducts` — multiple constructors, at least one with fields. Legal
  for Eq, Ord, Show.
- `Empty` — zero constructors. Legal for Eq, Ord; Show with empty `case`.

Each per-class file dispatches on `DataShape` and returns either an
`ast.InstanceDecl` or emits a diagnostic and returns `error.NotDerivable`. The
top-level `derive` collects successful instances, skips erroring ones, and
continues, so a single compile run surfaces every undérivable clause.

## Per-class synthesis semantics

Every synthesised AST node carries `class_name_span` — the span of the class
identifier inside the `deriving (...)` clause — so downstream diagnostics
point at the user's source, not at a phantom location.

### Eq

Synthesises `(==)`. Instance context: `Eq a` for every type variable `a` that
appears in any field type.

```haskell
data T a b = C1 a | C2 a b | C3
-- becomes:
instance (Eq a, Eq b) => Eq (T a b) where
  C1 x1     == C1 y1     = x1 == y1
  C2 x1 x2  == C2 y1 y2  = x1 == y1 && x2 == y2
  C3        == C3        = True
  _         == _         = False
```

The catch-all `_ == _ = False` clause is omitted when the type has exactly
one constructor.

### Ord

Synthesises `compare`. Constructor order = order of declaration in the source.
Field comparison is lexicographic.

```haskell
instance (Ord a, Ord b) => Ord (T a b) where
  compare (C1 x1)    (C1 y1)    = compare x1 y1
  compare (C2 x1 x2) (C2 y1 y2) = case compare x1 y1 of
      EQ -> compare x2 y2
      o  -> o
  compare C3 C3 = EQ
  compare a b   = compare (conTag a) (conTag b)
```

`conTag` is a hidden helper synthesised alongside the instance for any
`SumOfProducts`/`Enumeration` shape, returning the constructor's positional
tag as `Int`. For pure `Enumeration` shapes the tag mapping can be inlined.

### Show

Uses the simplified single-method `show :: a -> String` already present in
Prelude. Format:

- Nullary constructor: `"ConName"`
- Constructor with args: `"ConName" ++ " " ++ show arg1 ++ " " ++ show arg2 ...`

```haskell
instance (Show a, Show b) => Show (T a b) where
  show (C1 x1)    = "C1 " ++ show x1
  show (C2 x1 x2) = "C2 " ++ show x1 ++ " " ++ show x2
  show C3         = "C3"
```

Record syntax, infix operators, and precedence-aware parens are out of scope
for this iteration (the simplified Show has no `showsPrec`).

### Bounded

Legal for `Enumeration` (no context) and `SingleProduct` (one `Bounded`
constraint per field type).

```haskell
-- enumeration
data Day = Mon | Tue | Wed
instance Bounded Day where
  minBound = Mon
  maxBound = Wed

-- single product
data P a b = P a b
instance (Bounded a, Bounded b) => Bounded (P a b) where
  minBound = P minBound minBound
  maxBound = P maxBound maxBound
```

### Enum

Legal only for `Enumeration` shape. Synthesises `fromEnum`, `toEnum`, `succ`,
`pred`.

```haskell
instance Enum Day where
  fromEnum Mon = 0
  fromEnum Tue = 1
  fromEnum Wed = 2
  toEnum 0 = Mon
  toEnum 1 = Tue
  toEnum 2 = Wed
  toEnum _ = error "Enum.toEnum: out of range"
  succ Mon = Tue
  succ Tue = Wed
  succ Wed = error "Enum.succ: bad argument"
  pred Mon = error "Enum.pred: bad argument"
  pred Tue = Mon
  pred Wed = Tue
```

### Newtype (stock-equivalence)

```haskell
newtype N a = MkN (Inner a) deriving Eq
```

Treated by `shape.zig` exactly as the equivalent
`data N a = MkN (Inner a) deriving Eq` (a `SingleProduct`). The same per-class
synthesisers run. For the five stock classes this is behaviourally identical
to GHC's newtype deriving; the distinction only matters for arbitrary
classes, which requires `coerce` (deferred).

## Prelude additions

Add to `lib/Prelude.hs`. Manual instances are written exactly the way derived
ones would render, fixing the spec the synthesiser must reproduce.

### Ord

```haskell
class Eq a => Ord a where
  compare :: a -> a -> Ordering
  (<)  :: a -> a -> Bool
  x < y = case compare x y of { LT -> True;  _  -> False }
  (<=) :: a -> a -> Bool
  x <= y = case compare x y of { GT -> False; _  -> True  }
  (>)  :: a -> a -> Bool
  x > y = case compare x y of { GT -> True;  _  -> False }
  (>=) :: a -> a -> Bool
  x >= y = case compare x y of { LT -> False; _  -> True  }

instance Ord Int where ...
instance Ord Bool where ...
instance Ord Char where compare x y = compare (charToInt x) (charToInt y)
instance Ord Ordering where ...
instance (Ord a) => Ord [a] where ...
instance (Ord a) => Ord (Maybe a) where ...
```

**Open verification item:** the existing monomorphic `<`, `<=`, `>`, `>=`
primops on `Int` may conflict with the new class methods of the same name.
Implementation must verify and resolve — likely by leaving the primops named
`ltInt`, `leInt`, etc., and routing class methods through them. To be
confirmed during plan writing.

### Bounded

```haskell
class Bounded a where
  minBound :: a
  maxBound :: a

instance Bounded Bool     where minBound = False; maxBound = True
instance Bounded Char     where ... -- platform Char range
instance Bounded Int      where ... -- Int64 range
instance Bounded Ordering where minBound = LT; maxBound = GT
```

### Enum

```haskell
class Enum a where
  succ :: a -> a
  pred :: a -> a
  fromEnum :: a -> Int
  toEnum :: Int -> a

instance Enum Int      where ...
instance Enum Bool     where ...
instance Enum Char     where ...
instance Enum Ordering where ...
```

### Export list

Extend Prelude's export list with: `Ord(..)`, `Bounded(..)`, `Enum(..)`,
`compare`, `(<)`, `(<=)`, `(>)`, `(>=)`, `minBound`, `maxBound`, `succ`,
`pred`, `fromEnum`, `toEnum`.

## Error handling and diagnostics

### New `DiagnosticCode` variants

```zig
deriving_unsupported_class,        // e.g. `deriving Functor`
deriving_shape_mismatch,           // e.g. `deriving Enum` on non-enumeration
deriving_empty_bounded,            // `deriving Bounded` on zero-constructor type
deriving_field_no_instance,        // wraps typechecker missing-instance with
                                   // deriving-aware text
deriving_standalone_type_mismatch, // malformed standalone deriving instance
```

### Two-stage error reporting

1. **Pre-synthesis** (in the deriving pass): class-name supportedness, shape
   eligibility, standalone-deriving form. Spans point at the offending class
   identifier in the `deriving (...)` clause.
2. **Post-synthesis** (in the typechecker): field-level missing instances
   (e.g. `data T = T (Int -> Int) deriving Eq`). The typechecker default
   error is `no instance for Eq (Int -> Int)`; when the surrounding instance
   was synthesised, the message is wrapped:
   *"Cannot derive `Eq (T)`: field of type `Int -> Int` has no `Eq`
   instance."*

To enable wrapping, extend `InstanceInfo` in `class_env.zig`:

```zig
pub const DerivingOrigin = struct {
    data_type_span: SourceSpan,
    class_name_span: SourceSpan,
};

pub const InstanceInfo = struct {
    // ... existing fields ...
    origin: ?DerivingOrigin = null,
};
```

The deriving pass populates `origin`; the typechecker checks it when emitting
missing-instance diagnostics for class constraints originating inside a
synthesised body.

### One-pass error aggregation

The `derive` pass processes all clauses even after one fails, so a single
compile run reports every undérivable clause. The typechecker similarly
continues after one missing-instance error within a synthesised body.

### No catch-all class dispatch

Per CLAUDE.md ("don't take 'kitchen sink' shortcuts"), the unsupported-class
path is explicit:

```zig
const stock = std.StaticStringMap(StockClass).initComptime(.{
    .{ "Eq",      .eq },
    .{ "Ord",     .ord },
    .{ "Show",    .show },
    .{ "Bounded", .bounded },
    .{ "Enum",    .enum_ },
});

switch (stock.get(class_name) orelse {
    diags.emit(.deriving_unsupported_class, class_name_span, ...);
    return error.NotDerivable;
}) {
    .eq      => return synthEqInstance(arena, data, span),
    .ord     => return synthOrdInstance(arena, data, span),
    .show    => return synthShowInstance(arena, data, span),
    .bounded => return synthBoundedInstance(arena, data, span),
    .enum_   => return synthEnumInstance(arena, data, span),
}
```

## Testing strategy

All tests use `std.testing.allocator` (or `ArenaAllocator` wrapping it) per
the zero-leak policy.

### 1. Unit tests in each `src/deriving/*.zig`

Build a `DataDecl` AST manually, call the synthesiser, pretty-print the
result, compare against a literal expected string. Covers every `DataShape`
branch per class.

### 2. Golden tests `tests/golden/deriving/`

End-to-end: an `.hs` input file with deriving clauses, paired with the
expected post-deriving-pass module dump. Catches AST construction
regressions across the full pipeline.

```
tests/golden/deriving/
├── eq_sum.hs                ├── eq_sum.expected
├── ord_enum.hs              ├── ord_enum.expected
├── show_records.hs          ├── show_records.expected
├── bounded_enum.hs          ├── bounded_enum.expected
├── enum_class.hs            ├── enum_class.expected
├── newtype_eq.hs            ├── newtype_eq.expected
└── unsupported_class.hs     └── unsupported_class.stderr
```

### 3. E2E behaviour tests `tests/e2e/deriving/`

Compile and run programs that exercise derived methods, check stdout.
Minimum coverage: one program per stock class, one newtype, one cross-feature
test (e.g. derived `Ord` consuming derived `Eq` superclass).

```haskell
-- tests/e2e/deriving/eq_runtime.hs
data Color = Red | Green | Blue deriving (Eq, Show)
main = do
  print (Red == Red)        -- True
  print (Red == Blue)       -- False
  print [Red, Green, Blue]  -- [Red,Green,Blue]
```

### 4. Diagnostic tests `tests/diagnostics/deriving/`

For each new `DiagnosticCode`, a fixture asserting code, span, and message
text.

### Test discovery

Add `_ = @import("deriving/deriving.zig");` (and per-class imports as needed)
to `src/root.zig` so `zig build test` picks up the new test blocks.

## Risks and open items

1. **Ord vs existing `<` primop on Int.** Need to verify how the existing
   monomorphic `<` primop coexists with a new `Ord Int` class method named
   `<`. Most likely the primops are renamed to `ltInt` etc. and the class
   method delegates. Verify during plan writing.
2. **`error` calls in synthesised `succ`/`pred`/`toEnum`.** Requires `error`
   to be in scope (it is, in current Prelude) and to terminate program
   execution cleanly under GRIN's lazy semantics.
3. **Context inference for polymorphic data types.** Need to walk constructor
   field types and collect every type variable that appears. Existing
   typechecker code probably has a helper; confirm during plan writing.
4. **Empty data type (`data Void`).** Derived `Eq`/`Ord` should produce
   instances with no equations (only reachable when scrutinee exists, which
   it cannot for `Void`). Verify pretty-printer and renamer handle an
   `InstanceDecl` with zero bindings.

## Follow-up issues to file before PR opens

- `coerce` primop + `Coercible` class + role system (prerequisite for full
  `deriving newtype` strategy for arbitrary classes).
- Full `Show` class with `showsPrec` and precedence-aware parens.
- Derived `Read`.
- Optimisation of `compare`'s cross-constructor dispatch (replace nested case
  on `conTag` with a primop or jump table).
- Support for record syntax in derived `Show`.

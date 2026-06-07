# Prelude regression suite (#759)

Every binding exported from `lib/Prelude.hs` is exercised by at least one
program in this directory. The suite runs via `prelude_test_runner.zig`
(part of `zig build test`); the runner format (sidecars, `.properties`
directives) is documented in `tests/hs_test_harness.zig`.

When adding an export to `lib/Prelude.hs`, add (or extend) a test here and
update this table.

| Export | Test |
|--------|------|
| `Bool(..)` | p001_bool |
| `not`, `(&&)`, `(\|\|)`, `otherwise` | p001_bool |
| `(+)`, `(-)`, `(*)`, `negate`, `abs`, `div`, `mod` | p002_arith |
| `signum`, `even`, `odd` | p002_arith |
| `(==)`, `(/=)`, `(<)`, `(>)`, `(<=)`, `(>=)`, `compare` | p003_compare |
| `max`, `min` | p003_compare |
| `Eq(..)`, `Ord(..)`, `Ordering(..)` | p003_compare |
| `id`, `const`, `flip`, `(.)`, `($)` | p004_combinators |
| `map`, `filter`, `(++)`, `head`, `tail`, `null`, `length` | p005_list_basic |
| `String` | p005_list_basic |
| `foldr`, `foldl`, `concat`, `take`, `drop` | p006_folds |
| `sum`, `product`, `replicate` | p006_folds |
| `Maybe(..)`, `Either(..)`, `maybe`, `fromMaybe`, `either` | p007_maybe_either |
| `putChar`, `putStr`, `putStrLn`, `print` | p008_io |
| `intToChar`, `charToInt` | p009_char |
| `intToDigit` | p009_char, p010_show |
| `Show(..)`, `show`, `showString`, `showLitChar` | p010_show |
| `showListWith`, `showListTail` | p010_show |
| `Enum(..)` (`succ`, `pred`, `toEnum`, `fromEnum`) | p011_enum_bounded |
| `enumFrom`, `enumFromTo`, `enumFromThen`, `enumFromThenTo` | p011_enum_bounded |
| `error` | p012_error |
| Prelude fn as HOF argument (regression) | p013_hof_prelude_arg (**xfail** — #764) |
| `Bounded(..)` (`minBound`, `maxBound`) | p014_bounded (**xfail** — #765) |

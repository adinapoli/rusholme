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
| `maximum`, `minimum`, `nub`, `sort`, `sortBy`, `foldl'` | p015_list_extras |
| `Eq`/`Ord` class defaults and the container instances (lists, `Maybe`, `Ordering`, tuples) | p016_eq_ord |
| `last`, `init`, `foldl1`, `foldr1`, `scanl`, `scanl1`, `scanr`, `scanr1` | p017_list_breadth |
| `concatMap`, `and`, `or`, `any`, `all`, `iterate`, `repeat`, `cycle` | p017_list_breadth |
| `splitAt`, `takeWhile`, `dropWhile`, `span`, `break`, `elem`, `notElem`, `lookup` | p017_list_breadth |
| `zip`, `zip3`, `zipWith`, `zipWith3`, `unzip`, `unzip3` | p017_list_breadth |
| `lines`, `words`, `unlines`, `unwords` | p017_list_breadth |
| `until` | p017_list_breadth |
| `gcd`, `lcm` | p017_list_breadth |
| partiality: `last`/`init`/`foldl1`/`foldr1`/`cycle` on `[]` | p018_last_empty, p019_init_empty, p020_foldl1_empty, p021_foldr1_empty, p022_cycle_empty |
| `gcd`/`lcm` zero-valued-argument identities (`gcd 0 0 = 0`, `lcm 0 0 = 0`) | p023_gcd_zero_zero |

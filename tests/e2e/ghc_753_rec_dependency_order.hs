-- Rec backpatch chain must run in dependency order, not source order (#753).
--
-- A `Rec` group (multi-binding `let`, where-clause group, or list-comp
-- `let`-qualifier) whose bindings are listed in a different order from
-- their dependency graph used to produce junk: the backpatch chain ran
-- in source order, so `c = a + b` read `a`/`b` while they were still
-- Unit placeholders.  GHC prints 30 / 33 / [3,6] here.

-- Case (a): where-clause group, dependent binding listed FIRST.
whereCase :: Int
whereCase = c
  where
    c = a + b -- depends on a, b — listed before both
    a = 10
    b = 20

-- Case (b): multi-binding let-in expression, dependent binding first.
letCase :: Int
letCase =
    let y = x + 11 -- depends on x — listed before it
        x = 22
    in y

-- Case (c): list-comp let-qualifier, bindings in non-dependent order.
listCompCase :: [Int]
listCompCase = [b | v <- [1, 2], let b = a + v; a = v * 2]

main :: IO ()
main = do
    print whereCase
    print letCase
    print listCompCase

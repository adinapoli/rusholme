-- List comprehension `let` qualifier end-to-end test (#734).
--
-- The `let` qualifier (Haskell 2010 §3.11) was previously rejected at parse
-- time because the layout processor did not open a layout context for a `let`
-- block appearing inside `[...]`.  These cases exercise:
--   * a single-binding let qualifier
--   * a let qualifier whose bound name is used by a following guard
--   * a let qualifier binding multiple names on one line (`;`-separated would
--     also work, but here we rely on layout closing at the `,`/`]`)
--   * two let qualifiers in the same comprehension

main :: IO ()
main = do
    print [y | x <- [1, 2, 3], let y = x * 2]
    print [y | x <- [1, 2, 3, 4], let y = x * x, y > 5]
    print [a + b | x <- [1, 2, 3], let a = x * 10, let b = x + 1]
    print [t | x <- [1, 2, 3], let s = x * x, let t = s + 1, t > 5]

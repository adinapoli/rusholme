-- List comprehension end-to-end test (#309).
--
-- Exercises three of the four desugaring forms from Haskell 2010 §3.11:
--   * generator with predicate
--   * multiple generators
--   * refutable pattern in generator (Just x <-)
--   * nested comprehensions
--   * inner generator shadowing the outer
--
-- The `let qualifier` form depends on layout-inside-brackets parsing and is
-- tracked separately.

main :: IO ()
main = do
    print [x | x <- [1, 2, 3, 4, 5], x > 2]
    print [x + y | x <- [1, 2, 3], y <- [10, 20], x /= 2]
    print [n | Just n <- [Just 1, Nothing, Just 2, Nothing, Just 3]]
    print [y * 2 | xs <- [[1, 2], [3, 4]], y <- xs]
    print [x | x <- [10, 20], x <- [1, 2, 3]]

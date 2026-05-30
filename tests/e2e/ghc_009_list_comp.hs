-- List comprehension end-to-end test (#309).
--
-- Exercises all four desugaring forms from Haskell 2010 §3.11:
--   * generator with predicate
--   * multiple generators
--   * refutable pattern in generator (Just x <-)
--   * nested comprehensions
--   * inner generator shadowing the outer
--   * let qualifier (#734): the `let` block lays out inside `[...]`
--   * let qualifier followed by a guard referencing the bound name

main :: IO ()
main = do
    print [x | x <- [1, 2, 3, 4, 5], x > 2]
    print [x + y | x <- [1, 2, 3], y <- [10, 20], x /= 2]
    print [n | Just n <- [Just 1, Nothing, Just 2, Nothing, Just 3]]
    print [y * 2 | xs <- [[1, 2], [3, 4]], y <- xs]
    print [x | x <- [10, 20], x <- [1, 2, 3]]
    print [y | x <- [1, 2, 3], let y = x * 2]
    print [y | x <- [1, 2, 3, 4], let y = x * x, y > 5]

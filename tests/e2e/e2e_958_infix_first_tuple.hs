module Main where

-- Regression test for #958: a tuple whose *first* component was an infix
-- application did not parse.  `(1 < 2, True)` failed while `((1 < 2), True)`
-- and `(True, 1 < 2)` were both fine.
--
-- The comma check after `(` runs against the application prefix, because
-- parsing a full expression up front would swallow the operator of a left
-- section `(x +)`.  The tuple is now also recognised after the infix
-- expression is complete.

pair :: Int -> Int -> (Bool, Bool)
pair x y = (x < y, x == y)

main :: IO ()
main = do
  print ((1 :: Int) < 2, True)
  print ((1 :: Int) + 2, (3 :: Int))
  print ((1 :: Int) == 2, False, (3 :: Int) * 4)
  -- Precedence inside the first component must be unaffected.
  print ((1 :: Int) + 2 * 3, (4 :: Int))
  -- Backtick operators take the same path.
  print ((10 :: Int) `div` 3, (10 :: Int) `mod` 3)
  -- Operators in later components already worked; pin them here too.
  print (True, (1 :: Int) < 2)
  -- Nested: an infix-first tuple inside another tuple, and inside a list.
  print (((1 :: Int) + 1, (2 :: Int)), (3 :: Int))
  print [((1 :: Int) < 2, True), ((3 :: Int) < 2, False)]
  -- Sections must still parse as sections rather than as tuple components.
  print (map ((1 :: Int) +) [1, 2, 3])
  print (map (+ (1 :: Int)) [1, 2, 3])
  print (pair 1 2)
  print (pair 2 2)
  -- A 3-tuple built entirely from comparisons.
  print ((1 :: Int) < 2, (2 :: Int) < 2, (3 :: Int) > 2)

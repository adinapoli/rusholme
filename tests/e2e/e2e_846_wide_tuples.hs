module Main where

-- Construction + function-argument pattern matching across arities 3..7.

sum3 :: (Int, Int, Int) -> Int
sum3 (a, b, c) = a + b + c

sum4 :: (Int, Int, Int, Int) -> Int
sum4 (a, b, c, d) = a + b + c + d

sum5 :: (Int, Int, Int, Int, Int) -> Int
sum5 (a, b, c, d, e) = a + b + c + d + e

sum6 :: (Int, Int, Int, Int, Int, Int) -> Int
sum6 (a, b, c, d, e, f) = a + b + c + d + e + f

sum7 :: (Int, Int, Int, Int, Int, Int, Int) -> Int
sum7 (a, b, c, d, e, f, g) = a + b + c + d + e + f + g

-- A function that builds a wide tuple, deconstructed with a `case`.
mk3 :: Int -> (Int, Int, Int)
mk3 x = (x, x + 1, x + 2)

caseSum :: Int
caseSum = case mk3 10 of
  (a, b, c) -> a + b + c

-- Nested tuples.
nested :: ((Int, Int), Int) -> Int
nested ((a, b), c) = a + b + c

main :: IO ()
main = do
  print (sum3 (1, 2, 3))
  print (sum4 (1, 2, 3, 4))
  print (sum5 (1, 2, 3, 4, 5))
  print (sum6 (1, 2, 3, 4, 5, 6))
  print (sum7 (1, 2, 3, 4, 5, 6, 7))
  print caseSum
  print (nested ((1, 2), 3))

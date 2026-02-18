-- GHC testsuite: list comprehensions
module Sc014ListComprehensions where

-- Basic comprehension
squares :: [Int] -> [Int]
squares xs = [x * x | x <- xs]

-- With guard
evens :: [Int] -> [Int]
evens xs = [x | x <- xs, even x]

-- Multiple generators
pairs :: [a] -> [b] -> [(a, b)]
pairs xs ys = [(x, y) | x <- xs, y <- ys]

-- With let binding
pythagorean :: Int -> [(Int, Int, Int)]
pythagorean n = [(a, b, c) | c <- [1..n]
                            , b <- [1..c]
                            , a <- [1..b]
                            , a*a + b*b == c*c]

-- Nested comprehension
matrix :: [[Int]] -> [[Int]]
matrix rows = [[rows !! i !! j | j <- [0..cols-1]] | i <- [0..rowCount-1]]
  where
    rowCount = length rows
    cols     = if null rows then 0 else length (head rows)

-- String as list
vowels :: String -> String
vowels s = [c | c <- s, c `elem` "aeiouAEIOU"]

-- Arithmetic sequence in comprehension
sumSquares :: Int -> Int
sumSquares n = sum [x*x | x <- [1..n]]

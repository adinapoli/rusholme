-- GHC testsuite: list syntax, arithmetic sequences, cons patterns
module Sc022ListSyntax where

-- Empty list
empty :: [a]
empty = []

-- List literals
nums :: [Int]
nums = [1, 2, 3, 4, 5]

-- Cons
cons :: a -> [a] -> [a]
cons x xs = x : xs

-- Nested list
matrix :: [[Int]]
matrix = [[1,2,3],[4,5,6],[7,8,9]]

-- Arithmetic sequences
oneTo10 :: [Int]
oneTo10 = [1..10]

odds :: [Int]
odds = [1,3..19]

downFrom :: [Int]
downFrom = [10,9..1]

infiniteFrom :: [Int]
infiniteFrom = [1..]

infiniteEvens :: [Int]
infiniteEvens = [0,2..]

-- String as list of Char
chars :: [Char]
chars = ['a', 'b', 'c']

-- Pattern matching on lists
safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe [a]
safeTail []     = Nothing
safeTail (_:xs) = Just xs

-- Multi-element cons pattern
firstThree :: [a] -> Maybe (a, a, a)
firstThree (a:b:c:_) = Just (a, b, c)
firstThree _         = Nothing

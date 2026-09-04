-- Prelude regression: maximum, minimum, sort, sortBy, nub, foldl' (#928).
--
-- These were all "variable not in scope"; the imports resolved, only the
-- bindings were absent.
module Main where

import Data.List

nums :: [Int]
nums = [3, 1, 4, 1, 5, 9, 2, 6]

descend :: Int -> Int -> Ordering
descend p q = compare q p

main :: IO ()
main = do
    print (maximum nums)
    print (minimum nums)
    print (maximum [7 :: Int])
    print (minimum "banana")
    print (nub [1, 2, 1, 3, 2, 4 :: Int])
    print (nub ([] :: [Int]))
    print (nub "mississippi")
    print (foldl' (+) 0 nums)
    print (foldl' (-) 0 [1, 2, 3 :: Int])
    -- Sorting: the empty list, a singleton, already ascending, already
    -- descending, and duplicates.  The natural merge sort takes a
    -- different path through `sequences` for each of the last two.
    print (sort ([] :: [Int]))
    print (sort [1 :: Int])
    print (sort nums)
    print (sort [1, 2, 3, 4, 5 :: Int])
    print (sort [5, 4, 3, 2, 1 :: Int])
    print (sort [2, 2, 1, 1, 3, 3 :: Int])
    print (sort "banana")
    print (sortBy descend nums)

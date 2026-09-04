module Main where

-- Regression test for #928: `maximum`, `minimum`, `sort`, `sortBy`, `nub` and
-- `foldl'` were all "variable not in scope".
--
-- The interesting one is `sortBy (comparing …)`, the shape most real code
-- uses, together with the stability `sort` documents: `sortBy` is a bottom-up
-- natural merge sort, so equal keys must come out in input order.

import Data.List
import Data.Ord
import Data.Tuple

pairs :: [(Int, String)]
pairs =
    [ (2, "two-a")
    , (1, "one-a")
    , (2, "two-b")
    , (1, "one-b")
    , (3, "three")
    , (1, "one-c")
    ]

main :: IO ()
main = do
    print (maximum [3, 1, 4, 1, 5, 9, 2, 6 :: Int])
    print (minimum [3, 1, 4, 1, 5, 9, 2, 6 :: Int])
    print (maximum "banana")
    print (minimum "banana")
    print (nub [1, 2, 1, 3, 2, 4 :: Int])
    print (nub "mississippi")
    print (foldl' (+) 0 [1, 2, 3, 4, 5 :: Int])
    print (sort [3, 1, 4, 1, 5, 9, 2, 6 :: Int])
    print (sort "the quick brown fox")
    -- The three shapes `sequences` distinguishes: a descending run, an
    -- ascending run, and runs that have to be merged pairwise more than once.
    print (sort [5, 4, 3, 2, 1 :: Int])
    print (sort [1, 2, 3, 4, 5 :: Int])
    print (sort [4, 5, 1, 2, 9, 8, 3, 3, 7, 6 :: Int])
    -- Stability: equal first components keep their input order.
    print (sortBy (comparing fst) pairs)
    -- Sorting by the String component would need `Ord [Char]`, which does
    -- not exist yet — tracked in
    -- https://github.com/adinapoli/rusholme/issues/952
    -- A descending sort through Down, which is what Data.Ord is for.
    print (sortBy (comparing (\p -> Down (fst p))) pairs)

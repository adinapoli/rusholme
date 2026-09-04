{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.List — pure list combinators.
--
-- Mirrors GHC's `base:Data.List`.  Imports from GHC.Base
-- (Bool/Int/Show, the comparison operators) and RHC.Prim is
-- transitive via GHC.Base.  No primops, no foreign decls.
module Data.List
    ( map, filter, (++), head, tail, null, length
    , foldr, foldl, foldl', concat, take, drop
    , reverse
    , sum, product, replicate
    , maximum, minimum
    , nub
    , sort, sortBy
    ) where

import GHC.Base
import Data.Function

infixr 5 ++

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter p []     = []
filter p (x:xs) = case p x of
    True  -> x : filter p xs
    False -> filter p xs

(++) :: [a] -> [a] -> [a]
(++) []     ys = ys
(++) (x:xs) ys = x : (++) xs ys

head :: [a] -> a
head (x:xs) = x
head []     = error "Data.List.head: empty list"

tail :: [a] -> [a]
tail (x:xs) = xs
tail []     = error "Data.List.tail: empty list"

null :: [a] -> Bool
null []    = True
null (x:xs) = False

length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

concat :: [[a]] -> [a]
concat []     = []
concat (x:xs) = (++) x (concat xs)

take :: Int -> [a] -> [a]
take n []     = []
take n (x:xs) = case n <= 0 of
    True  -> []
    False -> x : take (n - 1) xs

drop :: Int -> [a] -> [a]
drop n []     = []
drop n (x:xs) = case n <= 0 of
    True  -> x : xs
    False -> drop (n - 1) xs

sum :: [Int] -> Int
sum []     = 0
sum (x:xs) = x + sum xs

product :: [Int] -> Int
product []     = 1
product (x:xs) = x * product xs

replicate :: Int -> a -> [a]
replicate n x = case n <= 0 of
    True  -> []
    False -> x : replicate (n - 1) x

reverse :: [a] -> [a]
reverse = foldl (flip (:)) []

-- | A left fold that is meant to force the accumulator at each step.
--
-- The result is the same as `foldl`; only the space behaviour differs, and
-- that part is not yet real — forcing needs `seq` (or honoured bang
-- patterns), neither of which the compiler has.  The name is provided so
-- that idiomatic code compiles; see the tracking issue for the strict
-- version.
--
-- tracked in: https://github.com/adinapoli/rusholme/issues/954
foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' f z []     = z
foldl' f z (x:xs) = foldl' f (f z x) xs

-- | The largest element of a non-empty list.
--
-- `Prelude.max` is still monomorphic on `Int`, so the comparison goes
-- through `Ord`'s `(>)` directly rather than through `max`.
maximum :: Ord a => [a] -> a
maximum []     = error "Data.List.maximum: empty list"
maximum (x:xs) = maximumBySoFar x xs

maximumBySoFar :: Ord a => a -> [a] -> a
maximumBySoFar acc []     = acc
maximumBySoFar acc (y:ys)
    | y > acc   = maximumBySoFar y ys
    | otherwise = maximumBySoFar acc ys

-- | The smallest element of a non-empty list.
minimum :: Ord a => [a] -> a
minimum []     = error "Data.List.minimum: empty list"
minimum (x:xs) = minimumBySoFar x xs

minimumBySoFar :: Ord a => a -> [a] -> a
minimumBySoFar acc []     = acc
minimumBySoFar acc (y:ys)
    | y < acc   = minimumBySoFar y ys
    | otherwise = minimumBySoFar acc ys

-- | Remove duplicate elements, keeping the first occurrence of each.
--
-- O(n^2) by specification — `nub` only requires `Eq`, so there is nothing
-- to index the seen elements by.
nub :: Eq a => [a] -> [a]
nub xs = nubSeen xs []

elemIn :: Eq a => a -> [a] -> Bool
elemIn y []     = False
elemIn y (z:zs) = (y == z) || elemIn y zs

nubSeen :: Eq a => [a] -> [a] -> [a]
nubSeen [] seen = []
nubSeen (x:xs) seen
    | elemIn x seen = nubSeen xs seen
    | otherwise     = x : nubSeen xs (x:seen)

-- ── Sorting ─────────────────────────────────────────────────────────
--
-- Bottom-up natural merge sort, the algorithm GHC's `Data.List.sortBy`
-- uses: split the input into maximal ascending and descending runs, then
-- merge the runs pairwise until one is left.  Stable, O(n log n) in the
-- worst case and O(n) on input that is already sorted or reverse-sorted.
--
-- GHC threads the ascending run through a difference list to append in
-- O(1); we accumulate it reversed and reverse once per run instead, which
-- keeps every helper first-order.

merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge cmp []     bs     = bs
merge cmp as     []     = as
merge cmp (a:as) (b:bs) = case cmp a b of
    GT -> b : merge cmp (a:as) bs
    _  -> a : merge cmp as (b:bs)

mergePairs :: (a -> a -> Ordering) -> [[a]] -> [[a]]
mergePairs cmp (a:b:xs) = merge cmp a b : mergePairs cmp xs
mergePairs cmp xs       = xs

mergeAll :: (a -> a -> Ordering) -> [[a]] -> [a]
mergeAll cmp []     = []
mergeAll cmp (x:[]) = x
mergeAll cmp xs     = mergeAll cmp (mergePairs cmp xs)

-- A run that is still descending: `as` already holds the elements seen so
-- far in ascending order, because each one was larger than its successor.
descending :: (a -> a -> Ordering) -> a -> [a] -> [a] -> [[a]]
descending cmp a as []     = (a:as) : []
descending cmp a as (b:bs) = case cmp a b of
    GT -> descending cmp b (a:as) bs
    _  -> (a:as) : sequences cmp (b:bs)

-- A run that is still ascending: `as` holds it reversed.
ascending :: (a -> a -> Ordering) -> a -> [a] -> [a] -> [[a]]
ascending cmp a as []     = reverse (a:as) : []
ascending cmp a as (b:bs) = case cmp a b of
    GT -> reverse (a:as) : sequences cmp (b:bs)
    _  -> ascending cmp b (a:as) bs

sequences :: (a -> a -> Ordering) -> [a] -> [[a]]
sequences cmp (a:b:xs) = case cmp a b of
    GT -> descending cmp b (a:[]) xs
    _  -> ascending cmp b (a:[]) xs
sequences cmp xs = xs : []

-- | Sort with an explicit comparison.  Stable: equal elements keep their
-- relative order.
sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp xs = mergeAll cmp (sequences cmp xs)

-- | Sort into ascending order.  Stable.
sort :: Ord a => [a] -> [a]
sort xs = sortBy (\p q -> compare p q) xs

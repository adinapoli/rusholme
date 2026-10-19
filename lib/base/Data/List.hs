{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.List — pure list combinators.
--
-- Mirrors GHC's `base:Data.List`.  Imports from GHC.Base
-- (Bool/Int/Show, the comparison operators) and RHC.Prim is
-- transitive via GHC.Base.  No primops, no foreign decls.
--
-- Laziness caveat (#913): applications nested in argument positions are
-- evaluated eagerly by this runtime, so `concatMap` inherits `concat`'s
-- divergence on infinite lists, even though `map`/`filter`/`scanl`/`zip`
-- stay productive.  See the note on `concatMap`.
module Data.List
    ( map, filter, (++), head, tail, null, length
    , last, init
    , foldr, foldl, foldl', concat, concatMap, take, drop
    , foldl1, foldr1
    , scanl, scanl1, scanr, scanr1
    , and, or, any, all
    , iterate, repeat, cycle
    , takeWhile, dropWhile, span, break, splitAt
    , elem, notElem, lookup
    , zip, zip3, zipWith, zipWith3, unzip, unzip3
    , lines, words, unlines, unwords
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

nubSeen :: Eq a => [a] -> [a] -> [a]
nubSeen [] seen = []
nubSeen (x:xs) seen
    | elem x seen = nubSeen xs seen
    | otherwise   = x : nubSeen xs (x:seen)

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

-- ── List access ─────────────────────────────────────────────────────

-- | The last element of a non-empty list.
last :: [a] -> a
last []     = error "Data.List.last: empty list"
last (x:xs) = case xs of
    []    -> x
    (_:_) -> last xs

-- | Everything but the last element of a non-empty list.
init :: [a] -> [a]
init []     = error "Data.List.init: empty list"
init (x:xs) = case xs of
    []    -> []
    (_:_) -> x : init xs

-- ── Folds ───────────────────────────────────────────────────────────

-- | `foldl` over a non-empty list, using its first element as the seed.
foldl1 :: (a -> a -> a) -> [a] -> a
foldl1 f []     = error "Data.List.foldl1: empty list"
foldl1 f (x:xs) = foldl f x xs

-- | `foldr` over a non-empty list, using its last element as the seed.
foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 f []     = error "Data.List.foldr1: empty list"
foldr1 f (x:xs) = case xs of
    []    -> x
    (_:_) -> f x (foldr1 f xs)

-- | `map` a list-valued function and concatenate the results.
--
-- Diverges on an infinite input: `concat`'s recursion
-- (`(++) xs (concat xss)`) puts the recursive call in an argument
-- position, which this runtime evaluates eagerly (#913).  Finite inputs
-- are unaffected.
concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f xs = concat (map f xs)

-- | Like `foldl`, but keeping every intermediate accumulator.  The result
-- always begins with the seed, so it is one longer than the input.
scanl :: (b -> a -> b) -> b -> [a] -> [b]
scanl f z xs = z : scanlRest f z xs

scanlRest :: (b -> a -> b) -> b -> [a] -> [b]
scanlRest f z []     = []
scanlRest f z (x:xs) = scanl f (f z x) xs

-- | `scanl` seeded with the list's first element.
scanl1 :: (a -> a -> a) -> [a] -> [a]
scanl1 f []     = []
scanl1 f (x:xs) = scanl f x xs

-- | Like `foldr`, keeping every intermediate accumulator.  The result
-- always ends with the seed.
scanr :: (a -> b -> b) -> b -> [a] -> [b]
scanr f z []     = z : []
scanr f z (x:xs) = scanrStep f (scanr f z xs) x

-- The recursive result is never empty, so the head is always available;
-- the `[]` equation only satisfies the exhaustiveness checker.
scanrStep :: (a -> b -> b) -> [b] -> a -> [b]
scanrStep f []     x = error "Data.List.scanr: impossible empty accumulator"
scanrStep f (q:qs) x = f x q : q : qs

-- | `scanr` seeded with the list's last element.
scanr1 :: (a -> a -> a) -> [a] -> [a]
scanr1 f []     = []
scanr1 f (x:xs) = case xs of
    []    -> x : []
    (_:_) -> scanrStep f (scanr1 f xs) x

-- ── Predicates over lists ───────────────────────────────────────────

-- | True when every element is True.  True for the empty list.
and :: [Bool] -> Bool
and []     = True
and (b:bs) = b && and bs

-- | True when any element is True.  False for the empty list.
or :: [Bool] -> Bool
or []     = False
or (b:bs) = b || or bs

-- | True when the predicate holds for every element.
any :: (a -> Bool) -> [a] -> Bool
any p xs = or (map p xs)

-- | True when the predicate holds for at least one element.
all :: (a -> Bool) -> [a] -> Bool
all p xs = and (map p xs)

-- ── Building lists ──────────────────────────────────────────────────

-- | `iterate f x` is the infinite list `[x, f x, f (f x), ...]`.
iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

-- | An infinite list of one repeated element.
repeat :: a -> [a]
repeat x = x : repeat x

-- | An infinite repetition of a non-empty list.
--
-- The recursive call sits in a cons tail rather than as an argument to
-- `(++)`: a nested application in a lazy argument position is still
-- evaluated eagerly (#913), which turns the `(++)` spelling into an
-- infinite loop.
cycle :: [a] -> [a]
cycle []     = error "Data.List.cycle: empty list"
cycle (x:xs) = cycleFrom (x:xs) (x:xs)

cycleFrom :: [a] -> [a] -> [a]
cycleFrom orig []     = cycleFrom orig orig
cycleFrom orig (x:xs) = x : cycleFrom orig xs

-- ── Slicing ─────────────────────────────────────────────────────────

-- | The longest prefix whose elements all satisfy the predicate.
takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile p [] = []
takeWhile p (x:xs)
    | p x       = x : takeWhile p xs
    | otherwise = []

-- | The remainder after `takeWhile` with the same predicate.
dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile p [] = []
dropWhile p (x:xs)
    | p x       = dropWhile p xs
    | otherwise = x : xs

-- | `(takeWhile p xs, dropWhile p xs)`.
span :: (a -> Bool) -> [a] -> ([a], [a])
span p xs = (takeWhile p xs, dropWhile p xs)

-- | `span` with the predicate negated.
break :: (a -> Bool) -> [a] -> ([a], [a])
break p xs = span (\x -> not (p x)) xs

-- | `(take n xs, drop n xs)`.
splitAt :: Int -> [a] -> ([a], [a])
splitAt n xs = (take n xs, drop n xs)

-- ── Searching ───────────────────────────────────────────────────────

-- | Is the element a member of the list?
elem :: Eq a => a -> [a] -> Bool
elem y []     = False
elem y (z:zs) = (y == z) || elem y zs

-- | The negation of `elem`.
notElem :: Eq a => a -> [a] -> Bool
notElem y xs = not (elem y xs)

-- | Look a key up in an association list.
lookup :: Eq a => a -> [(a, b)] -> Maybe b
lookup k [] = Nothing
lookup k ((a, b):ps)
    | k == a    = Just b
    | otherwise = lookup k ps

-- ── Zipping ─────────────────────────────────────────────────────────

-- | Pair up elements, stopping at the shorter list.
zip :: [a] -> [b] -> [(a, b)]
zip []     ys     = []
zip xs     []     = []
zip (x:xs) (y:ys) = (x, y) : zip xs ys

zip3 :: [a] -> [b] -> [c] -> [(a, b, c)]
zip3 (x:xs) (y:ys) (z:zs) = (x, y, z) : zip3 xs ys zs
zip3 _      _      _      = []

-- | `zip` generalised over the combining function.
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f []     ys     = []
zipWith f xs     []     = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys

zipWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
zipWith3 f (x:xs) (y:ys) (z:zs) = f x y z : zipWith3 f xs ys zs
zipWith3 f _      _      _      = []

-- | The inverse of `zip`.
unzip :: [(a, b)] -> ([a], [b])
unzip ps = (map fstPair ps, map sndPair ps)

fstPair :: (a, b) -> a
fstPair (a, _) = a

sndPair :: (a, b) -> b
sndPair (_, b) = b

unzip3 :: [(a, b, c)] -> ([a], [b], [c])
unzip3 ts = (map fstTriple ts, map sndTriple ts, map thdTriple ts)

fstTriple :: (a, b, c) -> a
fstTriple (a, _, _) = a

sndTriple :: (a, b, c) -> b
sndTriple (_, b, _) = b

thdTriple :: (a, b, c) -> c
thdTriple (_, _, c) = c

-- ── Strings ─────────────────────────────────────────────────────────
--
-- `lines`/`words` follow GHC's handling of separators: `lines` treats the
-- newline as a terminator (so a trailing newline adds no empty last line,
-- but an embedded blank line does yield ""), while `words` treats runs of
-- whitespace as a separator and drops leading and trailing runs.

-- | Split a string at newlines.  The newline is a terminator, so a
-- trailing one adds no empty last line while an embedded blank line does
-- yield "".
lines :: String -> [String]
lines []       = []
lines (c : cs) = linesSplit (break isNewline (c : cs))

isNewline :: Char -> Bool
isNewline c = c == '\n'

linesSplit :: (String, String) -> [String]
linesSplit (l, [])     = l : []
linesSplit (l, (_:cs)) = l : lines cs

-- | Split a string into whitespace-separated words.
--
-- The separator set is exactly the ASCII whitespace GHC's `words` splits
-- on.  It is a local copy of `Data.Char.isSpace` on purpose: the REPL's
-- fixed boot set does not load Data.Char and its per-module compilation
-- does not resolve imports, so a `Data.List` importing Data.Char fails to
-- load and is silently dropped, taking `(++)` with it (#973).
words :: String -> [String]
words s = wordsAfterSpace (dropWhile isSpaceChar s)

wordsAfterSpace :: String -> [String]
wordsAfterSpace []       = []
wordsAfterSpace (c : cs) = wordsSplit (break isSpaceChar (c : cs))

wordsSplit :: (String, String) -> [String]
wordsSplit (w, rest) = w : words rest

-- Same ASCII set as `Data.Char.isSpace`; kept local so Data.List does not
-- reorder the boot modules (see #973).
isSpaceChar :: Char -> Bool
isSpaceChar c = elem c (' ' : '\t' : '\n' : '\r' : '\f' : '\v' : [])

-- | Join lines, appending a newline after each.
unlines :: [String] -> String
unlines []       = []
unlines (l : ls) = (++) l ('\n' : unlines ls)

-- | Join words with single spaces between them.
unwords :: [String] -> String
unwords []       = []
unwords (w : ws) = case ws of
    []    -> w
    (_:_) -> (++) w (' ' : unwords ws)

-- Bench: sequential list filtering (sieve of Eratosthenes).
--
-- Inspired by the Benchmarks Game "nsieve" benchmark.
-- Builds a list of integers, then repeatedly filters out
-- composites by removing multiples of each prime found.
-- Different from knucleotide (BST): this is sequential
-- marking/filtering on a flat linear structure. Tests the
-- runtime's ability to handle many intermediate lists and
-- the allocation/deallocation pattern of filter operations.

data List = Nil | Cons Int List

-- Build list [lo..hi].
range :: Int -> Int -> List
range lo hi = if lo > hi then Nil else Cons lo (range (lo + 1) hi)

-- Remove multiples of p from the list.
sieveStep :: Int -> List -> List
sieveStep _ Nil = Nil
sieveStep p (Cons x xs) =
  if mymod x p == 0 then sieveStep p xs
  else Cons x (sieveStep p xs)

-- Sieve: keep first element, filter its multiples from the rest.
sieve :: List -> List
sieve Nil = Nil
sieve (Cons p xs) = Cons p (sieve (sieveStep p xs))

-- Count elements in a list.
countList :: List -> Int -> Int
countList Nil acc = acc
countList (Cons _ xs) acc = countList xs (acc + 1)

-- Integer modulus: a mod b (for positive a, b).
mymod :: Int -> Int -> Int
mymod a b = if a < b then a else mymod (a - b) b

main = putStrLn (show (countList (sieve (range 2 2000)) 0))
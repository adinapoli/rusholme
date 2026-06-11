-- Bench: higher-order function chains (closure allocation overhead).
--
-- Applies chains of map and fold operations to a custom list.
-- Unlike all existing benchmarks which use direct recursion,
-- this passes functions as arguments, creating and invoking
-- closures at each step. Tests the runtime's closure allocation
-- and application overhead. The chain involves partially applied
-- functions (e.g., addN 3) which capture environment values,
-- exercising a different allocation surface than simple Cons
-- cells.

data List = Nil | Cons Int List

-- Map: applies f to each element.
myMap :: (Int -> Int) -> List -> List
myMap _ Nil = Nil
myMap f (Cons x xs) = Cons (f x) (myMap f xs)

-- Fold left with accumulator.
myFoldl :: (Int -> Int -> Int) -> Int -> List -> Int
myFoldl _ acc Nil = acc
myFoldl f acc (Cons x xs) = myFoldl f (f acc x) xs

-- Add n to x (partially applied as addN 3, addN 1, etc.).
addN :: Int -> Int -> Int
addN n x = x + n

-- Add two integers (used as fold function).
add :: Int -> Int -> Int
add x y = x + y

-- Build list [lo..hi].
range :: Int -> Int -> List
range lo hi = if lo > hi then Nil else Cons lo (range (lo + 1) hi)

-- Sum all elements of a list.
sumList :: List -> Int -> Int
sumList Nil acc = acc
sumList (Cons x xs) acc = sumList xs (acc + x)

-- Run n chain iterations: map (addN 3) . map (addN 1) then fold.
-- Each iteration feeds the result of the previous map back in,
-- preventing CSE. The partially applied (addN k) closures test
-- closure allocation + application overhead.
runChain :: Int -> List -> Int -> Int
runChain 0 xs acc = acc + sumList xs 0
runChain n xs acc =
  let step1 = myMap (addN 3) xs
      step2 = myMap (addN 1) step1
      total = myFoldl add 0 step2
  in runChain (n - 1) step2 (acc + total)

main = putStrLn (show (runChain 100 (range 1 3000) 0))
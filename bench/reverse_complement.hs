-- Bench: string/list manipulation (pattern matching overhead).
--
-- Inspired by the Benchmarks Game "reverse-complement" benchmark.
-- Reverses a list and complements each element (swaps 0↔1, 2↔3).
-- Exercises pattern matching on small ADTs, list traversal, and
-- allocation of a new list. Good for measuring per-element overhead
-- of pattern matching + allocation.

data Base = A | T | C | G

data BList = BNil | BCons Base BList

complement :: Base -> Base
complement A = T
complement T = A
complement C = G
complement G = C

-- Reverse a list (accumulator style).
myreverse :: BList -> BList -> BList
myreverse BNil acc = acc
myreverse (BCons x xs) acc = myreverse xs (BCons x acc)

-- Complement each element.
compAll :: BList -> BList
compAll BNil = BNil
compAll (BCons x xs) = BCons (complement x) (compAll xs)

-- Build a DNA-like list of alternating bases.
buildDNA :: Int -> BList
buildDNA 0 = BNil
buildDNA n = BCons (baseMod n) (buildDNA (n - 1))

baseMod :: Int -> Base
baseMod n = case mymod n 4 of
              0 -> A
              1 -> T
              2 -> C
              _ -> G

mymod :: Int -> Int -> Int
mymod a b = if a < b then a else mymod (a - b) b

-- Count elements in the list.
countBases :: BList -> Int -> Int
countBases BNil acc = acc
countBases (BCons _ xs) acc = countBases xs (acc + 1)

-- Reverse-complement the DNA list.
loop :: Int -> Int
loop 0 = 0
loop n = countBases (compAll (myreverse (buildDNA 1000) BNil)) 0

main = putStrLn (show (loop 1))
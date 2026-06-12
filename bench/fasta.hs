-- Bench: string concatenation (append-heavy allocation).
--
-- Inspired by the Benchmarks Game "fasta" benchmark's line
-- wrapping. Builds many small string fragments and concatenates
-- them. In Haskell, repeated list concatenation is quadratic,
-- making this a good test of allocation patterns and the runtime's
-- ability to handle many small heap objects. We use a custom list
-- of characters to avoid depending on built-in String sugar.

data CharList = CNil | CCons Int CharList

-- Append two character lists.
append :: CharList -> CharList -> CharList
append CNil ys = ys
append (CCons c cs) ys = CCons c (append cs ys)

-- Build a "line" of n copies of a character code.
buildLine :: Int -> Int -> CharList
buildLine 0 _ = CNil
buildLine n c = CCons c (buildLine (n - 1) c)

-- Concatenate k lines of width w.
concatLines :: Int -> Int -> Int -> CharList
concatLines 0 _ _ = CNil
concatLines k w c = append (buildLine w c) (concatLines (k - 1) w c)

-- Count characters in a CharList.
countChars :: CharList -> Int
countChars CNil = 0
countChars (CCons _ cs) = 1 + countChars cs

main = putStrLn (show (countChars (concatLines 50 60 65)))
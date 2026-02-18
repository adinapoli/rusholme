-- GHC testsuite: mutually recursive bindings in where clauses
module Sc026WhereMutualRecursion where

-- Mutually recursive top-level
isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n - 1)

isOdd :: Int -> Bool
isOdd 0 = False
isOdd n = isEven (n - 1)

-- Mutually recursive in where
collatz :: Int -> [Int]
collatz n = go n
  where
    go 1 = [1]
    go k
        | even k    = k : go (k `div` 2)
        | otherwise = k : go (3 * k + 1)

-- let with mutual recursion
test :: Int -> (Bool, Bool)
test n =
    let e = isEven' n
        o = isOdd' n
        isEven' 0 = True
        isEven' k = isOdd' (k - 1)
        isOdd' 0  = False
        isOdd' k  = isEven' (k - 1)
    in (e, o)

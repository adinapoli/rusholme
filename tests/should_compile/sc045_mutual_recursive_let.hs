-- GHC testsuite: mutually recursive let-bindings with type signatures
module Sc045MutualRecursiveLetWithSigs where

-- Mutually recursive let-bindings with type signatures
-- This tests issue #263: both functions have type signatures and call each other
evenOdd :: Int -> Bool -> Bool
evenOdd n m =
    let isEven :: Int -> Bool
        isEven 0 = True
        isEven x = isOdd x

        isOdd :: Int -> Bool
        isOdd 0 = False
        isOdd x = isEven x
    in isEven n || isOdd m

-- Three-way mutual recursion
triplet :: Int -> Bool
triplet n =
    let f :: Int -> Bool
        f 0 = g n
        f x = g x

        g :: Int -> Bool
        g 0 = h n
        g x = h x

        h :: Int -> Bool
        h 0 = f n
        h x = f x
    in f n

-- Mutually recursive pattern bindings with signatures
mutualPats :: Bool -> Bool
mutualPats b =
    let x :: Bool
        x = y

        y :: Bool
        y = x
    in x

-- Mixed: one with sig, one without
mixed :: Bool -> Bool
mixed b =
    let withSig x = withoutSig x
        withoutSig x = withSig x
    in withSig b

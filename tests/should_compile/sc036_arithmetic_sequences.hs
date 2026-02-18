-- GHC testsuite: arithmetic sequence expressions [e1..], [e1..e2], [e1,e2..e3]
module Sc036ArithmeticSequences where

-- Bounded increasing
upTo :: [Int]
upTo = [1..10]

-- Bounded with step
evens :: [Int]
evens = [2,4..20]

-- Bounded decreasing
countdown :: [Int]
countdown = [10,9..1]

-- Unbounded (infinite)
naturals :: [Int]
naturals = [0..]

-- Unbounded with step
odds :: [Int]
odds = [1,3..]

-- Float sequences
floatSeq :: [Double]
floatSeq = [0.0, 0.5 .. 2.0]

-- Char sequences
letters :: [Char]
letters = ['a'..'z']

-- Used in comprehension context
take5evens :: [Int]
take5evens = take 5 [2,4..]

-- Expression in bounds
fromN :: Int -> [Int]
fromN n = [n..]

rangeBetween :: Int -> Int -> [Int]
rangeBetween lo hi = [lo..hi]

module ListPatterns where

-- Empty list pattern
isEmpty :: [Int] -> Bool
isEmpty [] = True
isEmpty _  = False

-- Exact two-element list pattern: [a, b]
firstOfTwo :: [Int] -> Int
firstOfTwo [a, b] = a
firstOfTwo _      = 0

-- Single-element list pattern: [x]
singleton :: [Int] -> Int
singleton [x] = x
singleton _   = 0

-- sc051: multiple consecutive parenthesized patterns in function arguments
-- Tests fix for https://github.com/adinapoli/rusholme/issues/540
module Sc051 where

-- Two consecutive parenthesized cons patterns (the original failing case)
myZip :: [a] -> [b] -> [(a, b)]
myZip (a:as) (b:bs) = (a, b) : myZip as bs
myZip _      _      = []

-- Two consecutive constructor application patterns
myBoth :: Maybe a -> Maybe b -> (a, b)
myBoth (Just x) (Just y) = (x, y)
myBoth _        _        = undefined

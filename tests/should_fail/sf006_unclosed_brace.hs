-- Should fail: explicit brace not closed
module Sf006UnclosedBrace where

f :: Int -> Int
f x = let { y = x + 1
        in y

-- Should fail: let without in (at expression level)
module Sf015LetNoIn where

f :: Int -> Int
f x = let y = x + 1

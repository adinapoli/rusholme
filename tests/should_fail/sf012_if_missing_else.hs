-- Should fail: if-then without else
module Sf012IfMissingElse where

f :: Bool -> Int
f b = if b then 1

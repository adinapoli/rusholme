-- Should fail: double :: in type signature
module Sf013DoubleDcolon where

f :: Int :: String
f x = x

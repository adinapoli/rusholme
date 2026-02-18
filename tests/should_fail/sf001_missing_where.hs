-- Should fail: 'module ... where' missing the 'where' keyword
module Sf001MissingWhere

f :: Int -> Int
f x = x + 1

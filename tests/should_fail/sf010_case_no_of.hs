-- Should fail: case expression missing 'of'
module Sf010CaseNoOf where

f :: Maybe Int -> Int
f x = case x
    Nothing -> 0
    Just n  -> n

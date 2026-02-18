-- Should fail: class declaration missing the class name
module Sf008ClassNoName where

class where
    method :: Int -> Int

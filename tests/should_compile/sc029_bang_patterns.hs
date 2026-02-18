-- GHC testsuite: bang patterns (strictness annotation)
module Sc029BangPatterns where

-- Bang in function argument
strictAdd :: Int -> Int -> Int
strictAdd !x !y = x + y

-- Bang in let
strictLet :: Int -> Int
strictLet x =
    let !y = x + 1
    in y * 2

-- Bang in where
strictWhere :: Int -> Int
strictWhere x = y * 2
  where
    !y = x + 1

-- Bang in data constructor (strict field)
data StrictPair a b = SP !a !b

-- Bang in case alternative
strictCase :: Maybe Int -> Int
strictCase m = case m of
    Nothing -> 0
    Just !x -> x + 1

-- GHC testsuite: lambda expressions
module Sc009Lambda where

-- Simple lambda
double :: Int -> Int
double = \x -> x * 2

-- Multi-argument lambda
add :: Int -> Int -> Int
add = \x y -> x + y

-- Lambda in application
applyTwice :: (a -> a) -> a -> a
applyTwice f = \x -> f (f x)

-- Lambda with pattern (single variable only — full patterns need extension)
mapMaybe :: (a -> b) -> Maybe a -> Maybe b
mapMaybe f = \m -> case m of
    Nothing -> Nothing
    Just x  -> Just (f x)

-- Sections
increment :: [Int] -> [Int]
increment = map (+ 1)

halve :: [Double] -> [Double]
halve = map (/ 2)

prefix :: String -> [String] -> [String]
prefix p = map (p ++)

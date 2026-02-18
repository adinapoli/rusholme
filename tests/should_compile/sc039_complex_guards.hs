-- GHC testsuite: complex guard expressions including pattern guards
module Sc039ComplexGuards where

-- Multi-condition guards
classify :: Int -> Int -> String
classify x y
    | x > 0, y > 0 = "NE"
    | x < 0, y > 0 = "NW"
    | x < 0, y < 0 = "SW"
    | x > 0, y < 0 = "SE"
    | otherwise     = "origin or axis"

-- Guards using where definitions
bmiCategory :: Double -> Double -> String
bmiCategory weight height
    | bmi <= 18.5 = "underweight"
    | bmi <= 25.0 = "normal"
    | bmi <= 30.0 = "overweight"
    | otherwise   = "obese"
  where
    bmi = weight / height ^ 2

-- Guards in case
describeList :: [a] -> String
describeList xs = case xs of
    [] -> "empty"
    [_] -> "singleton"
    ys
        | length ys < 5  -> "short"
        | length ys < 20 -> "medium"
        | otherwise      -> "long"

-- Nested guards
safeOp :: Int -> Int -> String
safeOp x y
    | y == 0    = "division by zero"
    | x < 0     =
        if y < 0
            then "both negative"
            else "negative dividend"
    | otherwise = show (x `div` y)

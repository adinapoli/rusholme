-- GHC testsuite: case expressions, all forms
module Sc016CaseExpressions where

data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double

area :: Shape -> Double
area s = case s of
    Circle r      -> 3.14159 * r * r
    Rectangle w h -> w * h
    Triangle a b c ->
        let s' = (a + b + c) / 2
        in sqrt (s' * (s' - a) * (s' - b) * (s' - c))

-- Nested case
safeDiv :: Int -> Int -> Maybe Int
safeDiv x y = case y of
    0 -> Nothing
    _ -> case x `mod` y of
        0 -> Just (x `div` y)
        _ -> Nothing

-- Case with guards
classifyList :: [a] -> String
classifyList xs = case xs of
    []  -> "empty"
    [_] -> "singleton"
    _   -> "longer"

-- Case on tuple
both :: (Bool, Bool) -> String
both pair = case pair of
    (True,  True)  -> "both"
    (True,  False) -> "first only"
    (False, True)  -> "second only"
    (False, False) -> "neither"

-- Case with as-pattern
headAndTail :: [a] -> Maybe (a, [a])
headAndTail xs = case xs of
    []        -> Nothing
    all@(h:t) -> Just (h, t)

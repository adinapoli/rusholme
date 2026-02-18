-- GHC testsuite: comprehensive pattern matching
module Sc006PatternMatching where

-- Wildcard
alwaysTrue :: a -> Bool
alwaysTrue _ = True

-- Nested constructor patterns
data Tree a = Leaf | Node (Tree a) a (Tree a)

depth :: Tree a -> Int
depth Leaf = 0
depth (Node l _ r) = 1 + max (depth l) (depth r)

-- Literal patterns
classify :: Int -> String
classify 0 = "zero"
classify 1 = "one"
classify n
    | n < 0    = "negative"
    | n < 10   = "small"
    | otherwise = "large"

-- As-patterns
firstAndAll :: [a] -> Maybe (a, [a])
firstAndAll [] = Nothing
firstAndAll xs@(x:_) = Just (x, xs)

-- Tuple patterns
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

-- Nested patterns
nestedMaybe :: Maybe (Maybe Int) -> Int
nestedMaybe Nothing = 0
nestedMaybe (Just Nothing) = 1
nestedMaybe (Just (Just n)) = n

-- Guards
bmi :: Double -> String
bmi weight
    | weight < 18.5 = "Underweight"
    | weight < 25.0 = "Normal"
    | weight < 30.0 = "Overweight"
    | otherwise     = "Obese"

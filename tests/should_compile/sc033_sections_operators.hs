-- GHC testsuite: operator sections and backtick operators
module Sc033SectionsOperators where

-- Left sections
addOne :: [Int] -> [Int]
addOne = map (+ 1)

double :: [Int] -> [Int]
double = map (* 2)

appendBang :: [String] -> [String]
appendBang = map (++ "!")

-- Right sections
divByTwo :: [Int] -> [Int]
divByTwo = map (`div` 2)

subtractFrom10 :: [Int] -> [Int]
subtractFrom10 = map (10 -)

-- Operator as function (fully applied)
add :: Int -> Int -> Int
add = (+)

sub :: Int -> Int -> Int
sub = (-)

-- Backtick notation
divides :: Int -> Int -> Bool
n `divides` m = m `mod` n == 0

-- cons as section
prependZero :: [Int] -> [Int]
prependZero = (0 :)

-- Complex sections
clamp :: Int -> Int -> Int -> Int
clamp lo hi x = (max lo . min hi) x

-- flip via section
greet :: String -> String
greet = ("Hello, " ++)

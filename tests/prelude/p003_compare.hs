-- Prelude regression: (==), (/=), (<), (>), (<=), (>=), compare,
-- max, min, Eq(..), Ord(..), Ordering(..) (#759).
module Main where

main :: IO ()
main = do
    print (1 == 1)
    print (1 == 2)
    print (1 /= 2)
    print (1 /= 1)
    print (1 < 2)
    print (2 > 3)
    print (2 <= 2)
    print (3 >= 4)
    print (compare 1 2)
    print (compare 2 2)
    print (compare 3 2)
    print (max 3 7)
    print (min 3 7)
    print [LT, EQ, GT]

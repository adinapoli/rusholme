-- Prelude regression: Maybe(..), Either(..), maybe, fromMaybe, either (#759).
module Main where

inc :: Int -> Int
inc x = x + 1

dbl :: Int -> Int
dbl x = x * 2

nothing :: Maybe Int
nothing = Nothing

leftFour :: Either Int Int
leftFour = Left 4

rightFour :: Either Int Int
rightFour = Right 4

main :: IO ()
main = do
    print (Just 3)
    print nothing
    print (maybe 0 inc (Just 4))
    print (maybe 0 inc nothing)
    print (fromMaybe 9 (Just 1))
    print (fromMaybe 9 nothing)
    print leftFour
    print rightFour
    print (either inc dbl leftFour)
    print (either inc dbl rightFour)

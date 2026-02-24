module Tier1Patterns where

data Color = Red | Green | Blue

isRed :: Color -> Bool
isRed Red = True
isRed _   = False

describeNumber :: Int -> String
describeNumber 0 = "zero"
describeNumber 1 = "one"
describeNumber _ = "many"

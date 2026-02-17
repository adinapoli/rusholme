-- Pattern matching
module Ghc007PatternMatching where

data Maybe a = Nothing | Just a

maybeToInt :: Maybe Int -> Int
maybeToInt Nothing = 0
maybeToInt (Just x) = x

data Color = Red | Green | Blue

colorName :: Color -> String
colorName Red = "red"
colorName Green = "green"
colorName Blue = "blue"

-- Algebraic data types
module Ghc006ADT where

data Maybe a = Nothing | Just a

data Tree a = Leaf a | Branch (Tree a) (Tree a)

data Color = Red | Green | Blue

data Pair a b = Pair a b

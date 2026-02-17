-- Deriving clauses
module Ghc009Deriving where

data Maybe a = Nothing | Just a
  deriving (Eq, Show)

data Color = Red | Green | Blue
  deriving (Eq, Ord)

newtype Age = Age Int
  deriving (Show)

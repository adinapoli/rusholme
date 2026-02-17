-- GADT-style data declarations
module Ghc010Gadt where

data Expr a where
  Lit :: Int -> Expr Int
  Add :: Expr Int -> Expr Int -> Expr Int

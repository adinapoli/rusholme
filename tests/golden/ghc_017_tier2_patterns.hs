module Tier2Patterns where

data Tree a = Leaf | Node (Tree a) a (Tree a)

data Wrapper a = Wrap a

-- Nested constructor pattern
unwrapNode :: Tree Int -> Int
unwrapNode (Node _ x _) = x
unwrapNode Leaf         = 0

-- Deeply nested: Node (Node _ x _) _ _
leftValue :: Tree Int -> Int
leftValue (Node (Node _ x _) _ _) = x
leftValue _                       = 0

-- As-pattern
wrapOrDefault :: Wrapper Int -> Wrapper Int
wrapOrDefault w@(Wrap _) = w
wrapOrDefault _           = Wrap 0

-- Tuple pattern
sumPair :: (Int, Int) -> Int
sumPair (a, _) = a

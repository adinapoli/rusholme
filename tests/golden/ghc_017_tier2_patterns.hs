module Tier2Patterns where

-- This is a *pattern-matching* golden test; the element type is `Bool`
-- deliberately.  A bare integer literal would now desugar to `fromInteger`
-- (#140), which needs the `Num` class / `instance Num Int` in scope — and the
-- golden pipeline runs against the minimal synthetic env (`initBuiltins`),
-- which has no class environment.  `Bool` keeps the pattern shapes identical
-- while the default branch uses `False` instead of `0`.  Numeric-literal
-- support in the golden harness is tracked in #911.

data Tree a = Leaf | Node (Tree a) a (Tree a)

data Wrapper a = Wrap a

-- Nested constructor pattern
unwrapNode :: Tree Bool -> Bool
unwrapNode (Node _ x _) = x
unwrapNode Leaf         = False

-- Deeply nested: Node (Node _ x _) _ _
leftValue :: Tree Bool -> Bool
leftValue (Node (Node _ x _) _ _) = x
leftValue _                       = False

-- As-pattern
wrapOrDefault :: Wrapper Bool -> Wrapper Bool
wrapOrDefault w@(Wrap _) = w
wrapOrDefault _           = Wrap False

-- Tuple pattern
firstOfPair :: (Bool, Bool) -> Bool
firstOfPair (a, _) = a

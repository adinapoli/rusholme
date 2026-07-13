module Main where

-- Regression test for #842: a signature of shape `(a -> b) -> a -> a -> R`
-- with a class constraint on the argument-only variable `b` used to trigger a
-- spurious self-unification failure ("cannot unify T with T").  This exercises
-- both the library `comparing` (re-introduced to Data.Ord) and a locally
-- defined function of the same shape.

import Data.Ord (comparing)

-- Local function with the exact #842 shape.
byKey :: Ord b => (a -> b) -> a -> a -> Ordering
byKey f x y = compare (f x) (f y)

-- Projection whose result type (b = Int) differs from its argument type
-- (a = (Char, Int)) — the distinct-variable case at the heart of #842.
sndInt :: (Char, Int) -> Int
sndInt (_, n) = n

main :: IO ()
main = do
  print (comparing negate 5 3)                       -- compare (-5) (-3) = LT
  print (comparing sndInt ('a', 5) ('b', 3))         -- compare 5 3       = GT
  print (byKey negate 3 5)                           -- compare (-3) (-5) = GT

-- e2e: shared case-block cache dominance (#901).
--
-- The match compiler shares fallback subtrees (a DAG); the backend caches
-- their translated blocks.  Before #901 the cache was keyed by GRIN node
-- only, so re-entering a shared block from a context with a different
-- scrutinee binding used a non-dominating pre-forced SSA value — silently
-- wrong results (eqCoin Tails Tails was False).  Exercises the plain
-- function shape, the idiomatic hand-written Eq instance shape, and a
-- three-constructor variant.
module Main where

data Coin = Heads | Tails

eqCoin :: Coin -> Coin -> Bool
eqCoin Heads Heads = True
eqCoin Tails Tails = True
eqCoin _ _ = False

data Signal = Red | Amber | Green

instance Eq Signal where
  Red == Red = True
  Amber == Amber = True
  Green == Green = True
  _ == _ = False
  x /= y = not (x == y)

main :: IO ()
main = do
  print (eqCoin Heads Heads)
  print (eqCoin Heads Tails)
  print (eqCoin Tails Heads)
  print (eqCoin Tails Tails)
  print (Red == Red)
  print (Amber == Amber)
  print (Green == Green)
  print (Red == Green)
  print (Green == Amber)
  print (Amber /= Amber)
  print (Red /= Green)

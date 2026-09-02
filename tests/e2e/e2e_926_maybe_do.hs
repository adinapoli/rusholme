module Main where

-- #926: `do` at a non-IO monad.  The block is desugared against the `Monad`
-- dictionary, so the second one short-circuits at its failing middle step
-- instead of running the rest.

safeDiv :: Int -> Int -> Maybe Int
safeDiv _ 0 = Nothing
safeDiv a b = Just (div a b)

ok :: Maybe Int
ok = do
  x <- safeDiv 10 2
  y <- safeDiv x 1
  return (x + y)

failing :: Maybe Int
failing = do
  x <- safeDiv 10 2
  y <- safeDiv x 0
  return (x + y)

main :: IO ()
main = do
  print ok
  print failing

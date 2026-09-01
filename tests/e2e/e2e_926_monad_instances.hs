module Main where

-- #926: the Functor/Applicative/Monad hierarchy across every built-in
-- instance — Maybe, Either e, [] and IO.

pairs :: [Int]
pairs = do
  x <- 1 : 2 : []
  y <- 10 : 20 : []
  return (x + y)

eth :: Either Bool Int
eth = do
  x <- Right 1
  y <- Right 2
  return (x + y)

main :: IO ()
main = do
  print (fmap (\x -> x + (1 :: Int)) (Just 1))
  print (fmap (\x -> x + (1 :: Int)) (Right 1 :: Either Bool Int))
  print (Just (\x -> x + (1 :: Int)) <*> Just 1)
  print ((Left True :: Either Bool Int) >>= \x -> Right (x + (1 :: Int)))
  print (pure (3 :: Int) :: Maybe Int)
  print pairs
  print eth
  n <- return (7 :: Int)
  print n

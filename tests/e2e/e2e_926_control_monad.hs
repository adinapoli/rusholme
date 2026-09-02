module Main where

import Control.Monad

-- #926: the Control.Monad combinators.
--
-- `when`/`unless` are exercised only in the branch that runs their action:
-- the branch that discards it still evaluates the argument eagerly, which is
-- the pre-existing lazy-argument gap tracked in #913.

main :: IO ()
main = do
  forM_ (1 : 2 : 3 : []) print
  mapM_ putStrLn ("a" : "b" : [])
  when True (putStrLn "when")
  unless False (putStrLn "unless")
  sequence_ (putStrLn "s1" : putStrLn "s2" : [])
  void (return (99 :: Int))
  total <- foldM (\acc x -> return (acc + x)) (0 :: Int) (1 : 2 : 3 : [])
  print total

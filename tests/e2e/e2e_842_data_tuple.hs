module Main where

import Data.Tuple

main :: IO ()
main = do
  putStrLn (show (fst (42, 99)))
  putStrLn (show (snd (42, 99)))
  putStrLn (show (fst (swap (1, 2))))
  putStrLn (show (curry fst 10 20))
  putStrLn (show (uncurry (+) (3, 4)))

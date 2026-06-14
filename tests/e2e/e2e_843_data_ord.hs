module Main where

import Data.Ord

main :: IO ()
main = do
  putStrLn (show (clamp (0, 10) 7))
  putStrLn (show (clamp (0, 10) 15))
  putStrLn (show (clamp (0, 10) (-3)))
  putStrLn (show ((Down 5) < (Down 3)))
  putStrLn (show (compare (Down 1) (Down 2)))

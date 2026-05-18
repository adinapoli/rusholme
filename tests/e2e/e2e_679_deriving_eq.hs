module Main where

data Color = Red | Green | Blue deriving Eq

main :: IO ()
main = do
  print (Red == Red)
  print (Red == Green)
  print (Blue == Blue)

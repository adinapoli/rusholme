{-# LANGUAGE NoImplicitPrelude #-}
module Main where

foreign import prim "putStrLn" putStrLn :: String -> IO ()

($) :: (a -> b) -> a -> b
($) f a = f a
infixr 0 $

identity x = x

data List a
  = Nil
  | Cons

map_it :: (a -> b) -> List a -> List b
map_it f Nil = Nil
map_it f Cons = Cons

main :: IO ()
main = do
  putStrLn "Hello from Rusholme!"
  putStrLn "Nice"
  putStrLn "Job!"

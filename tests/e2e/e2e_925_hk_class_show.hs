module Main where

-- Regression test for #925: a user-defined higher-kinded class whose method
-- result is `show`n used to fail at link time with
-- `undefined reference to dict$Show_0` — the constraint on the method result
-- was emitted as a reference to a dictionary that was never defined.

class Container f where
  ctoL :: f a -> [a]

newtype Stack a = Stack [a]

instance Container Stack where
  ctoL (Stack xs) = xs

main :: IO ()
main = print (ctoL (Stack [1 :: Int]))

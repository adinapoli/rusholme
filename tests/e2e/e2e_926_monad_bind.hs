module Main where

-- First #926 deliverable: the bind operator is a real Monad class method in
-- scope, not a wired-in IO-only name.  This is the issue's reproducer.

safeDiv :: Int -> Int -> Maybe Int
safeDiv a b = Just (div a b)

main :: IO ()
main = print (safeDiv 10 2 >>= \x -> Just x)

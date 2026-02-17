-- Tuples
module Ghc015Tuples where

pair :: (Int, String)
pair = (42, "hello")

triple :: (Bool, Int, String)
triple = (True, 100, "world")

fst' :: (a, b) -> a
fst' (x, _) = x

snd' :: (a, b) -> b
snd' (_, y) = y

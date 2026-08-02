module Main where

-- Companion check for #925: the same dictionary-selection path must work for
-- a user-defined Functor-shaped class — a higher-kinded class parameter plus
-- method-local type variables (`a`, `b`) whose result is `show`n.

class F f where
  fmapF :: (a -> b) -> f a -> f b

instance F Maybe where
  fmapF _ Nothing  = Nothing
  fmapF g (Just x) = Just (g x)

main :: IO ()
main = print (fmapF (\x -> x + (1 :: Int)) (Just (1 :: Int)))

-- e2e: superclass contexts (#889).
--
-- Exercises the three pieces of superclass support:
--   1. Entailment: a polymorphic `Ord a =>` function calling `(==)` (an Eq
--      method) extracts the Eq dictionary from the Ord dictionary.
--   2. Multi-hop extraction: `Floating a =>` reaching `(/)` (Fractional)
--      and `(+)` (Num) through the Fractional -> Num chain.
--   3. User-defined class with a superclass context, instantiated and used
--      polymorphically through both its own and its superclass's methods.
--   4. User-module instance of a boot class with a superclass (Ord Fruit):
--      the superclass list comes from the GHC.Base interface and the local
--      Eq Fruit dictionary is embedded in the local Ord Fruit dictionary.
module Main where

ordered :: Ord a => a -> a -> String
ordered x y =
  if x == y
    then "equal"
    else case compare x y of
      LT -> "less"
      GT -> "greater"
      EQ -> "impossible"

class Eq a => Sized a where
  size :: a -> Int

instance Sized Int where
  size n = n

-- Uses (==) (superclass Eq of Sized) and size (own method) on the same dict.
sameSize :: Sized a => a -> a -> Bool
sameSize x y = x == y && size x == size y

-- sqrt is Floating's own; (/) needs Fractional (one hop); (+) needs Num
-- (two hops: Floating -> Fractional -> Num).
blend :: Floating a => a -> a
blend x = sqrt x + x / (x + x)

data Fruit = Apple | Banana

fruitRank :: Fruit -> Int
fruitRank Apple = 1
fruitRank Banana = 2

instance Eq Fruit where
  x == y = fruitRank x == fruitRank y
  x /= y = fruitRank x /= fruitRank y

instance Ord Fruit where
  compare x y = compare (fruitRank x) (fruitRank y)
  x < y = fruitRank x < fruitRank y
  x <= y = fruitRank x <= fruitRank y
  x > y = fruitRank x > fruitRank y
  x >= y = fruitRank x >= fruitRank y

main :: IO ()
main = do
  putStrLn (ordered (3 :: Int) 5)
  putStrLn (ordered (2.5 :: Double) 2.5)
  putStrLn (ordered 'z' 'a')
  print (sameSize (4 :: Int) 4)
  print (sameSize (4 :: Int) 5)
  print (blend (4.0 :: Double))
  putStrLn (ordered Banana Apple)
  putStrLn (ordered Apple Apple)

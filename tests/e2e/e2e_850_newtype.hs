module Main where

-- A `newtype` behaves like a single-constructor `data` type: construction,
-- pattern matching, polymorphic wrappers, and record-style (positional) use.

newtype Age = Age Int

getAge :: Age -> Int
getAge (Age n) = n

newtype Wrapper a = Wrapper a

unwrap :: Wrapper a -> a
unwrap (Wrapper x) = x

mapW :: (a -> b) -> Wrapper a -> Wrapper b
mapW f (Wrapper x) = Wrapper (f x)

-- Record-syntax newtype, used positionally (the auto-derived selector is a
-- separate, not-yet-implemented feature shared with `data` records).
newtype Celsius = Celsius { unCelsius :: Int }

addC :: Celsius -> Celsius -> Int
addC (Celsius a) (Celsius b) = a + b

-- Newtype wrapping a tuple payload.
newtype Pair = Pair (Int, Int)

sumPair :: Pair -> Int
sumPair (Pair (a, b)) = a + b

main :: IO ()
main = do
  print (getAge (Age 42))
  print (unwrap (Wrapper 99))
  print (unwrap (mapW (\x -> x + 1) (Wrapper 41)))
  print (addC (Celsius 20) (Celsius 5))
  print (sumPair (Pair (3, 4)))

-- Regression test for #962.  Helper.hs declares an `Ord` instance at exactly
-- the same line and column as `instance Ord Foo` below.  Instances were
-- matched on line and column alone, with no file, so `Ord Foo`'s superclass
-- slot took the evidence for `Eq (Wrap a)` — whose context is a dictionary
-- parameter that does not exist here — and the link failed with
-- `undefined reference to dict$Eq_0`.  Keep both instances on line 12.
module Main where

import Helper

data Foo = Foo Int
instance Ord Foo where
  compare (Foo x) (Foo y) = compare x y
  (<)  (Foo x) (Foo y) = x <  y
  (<=) (Foo x) (Foo y) = x <= y
  (>)  (Foo x) (Foo y) = x >  y
  (>=) (Foo x) (Foo y) = x >= y

instance Eq Foo where
  (==) (Foo x) (Foo y) = x == y
  (/=) (Foo x) (Foo y) = x /= y

main :: IO ()
main = do
  print (Foo 1 < Foo 2)
  print (Foo 2 < Foo 1)
  print (Wrap (1 :: Int) < Wrap 2)
  print (compare (Wrap 'b') (Wrap 'a'))

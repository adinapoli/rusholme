module Main where

-- Regression test for #951 and #952.
--
-- #951: `Eq` and `Ord` declared their methods with no defaults, so every
-- instance had to spell out all two / all seven.  Haskell 2010 §6.3.1–6.3.2
-- gives `Eq` a mutual default pair and derives the rest of `Ord` from
-- `compare`, and puts `max`/`min` on the class (they used to be monomorphic
-- `Int -> Int -> Int` functions).
--
-- #952: `Eq` existed only for `Int`, `Bool`, `Char`, `Double` and `Ord` only
-- for `Int`, `Char`, `Double`, so `"a" == "a"` and `(1,2) == (1,2)` both
-- failed with `no instance`.

import Data.List
import Data.Ord
import Data.Tuple

-- An instance defining only `(==)`, leaning on the `(/=)` default.
data OnlyEq = OnlyEq Int

instance Eq OnlyEq where
  (==) (OnlyEq x) (OnlyEq y) = x == y

-- An instance defining only `(/=)`, leaning on the `(==)` default.
data OnlyNe = OnlyNe Int

instance Eq OnlyNe where
  (/=) (OnlyNe x) (OnlyNe y) = x /= y

-- An `Ord` instance defining only `compare`; the four comparison operators
-- and `max`/`min` all come from the defaults.
data OnlyCompare = OnlyCompare Int

instance Eq OnlyCompare where
  (==) (OnlyCompare x) (OnlyCompare y) = x == y

instance Ord OnlyCompare where
  compare (OnlyCompare x) (OnlyCompare y) = compare x y

unwrap :: OnlyCompare -> Int
unwrap (OnlyCompare n) = n

-- Deriving must keep working now that the classes carry defaults.
data Colour = Red | Green | Blue deriving (Eq, Ord, Show)

main :: IO ()
main = do
  -- ── #951: class defaults ─────────────────────────────────────────
  print (OnlyEq 1 == OnlyEq 1)
  print (OnlyEq 1 /= OnlyEq 2)
  print (OnlyNe 1 == OnlyNe 1)
  print (OnlyNe 1 /= OnlyNe 2)
  print (OnlyCompare 1 < OnlyCompare 2)
  print (OnlyCompare 2 <= OnlyCompare 2)
  print (OnlyCompare 3 > OnlyCompare 1)
  print (OnlyCompare 1 >= OnlyCompare 4)
  print (unwrap (max (OnlyCompare 1) (OnlyCompare 2)))
  print (unwrap (min (OnlyCompare 1) (OnlyCompare 2)))
  -- `max`/`min` are `Ord` methods now, not `Int`-only functions.
  print (max (3 :: Int) 5)
  print (min 'a' 'b')
  print (max (2.5 :: Double) 1.5)
  print (max Red Blue)
  print (min Green Blue)

  -- ── #952: String / list ──────────────────────────────────────────
  print ("abc" == "abc")
  print ("ab" == "abc")
  print ("" == "")
  print (compare "ab" "abc")
  print (compare "b" "ab")
  print (compare "" "a")
  print ([[(1 :: Int)], [2]] == [[1], [2]])
  print (compare [[(1 :: Int)]] [[1], [2]])
  -- Through a higher-order function, so the dictionary travels.
  print (filter (\t -> t == "a") ["a", "b", "a"])
  -- `Data.List` over the new instances is the payoff (#928).
  print (sort ["pear", "apple", "fig"])
  print (nub ["a", "b", "a"])
  print (maximum ["pear", "apple", "fig"])

  -- ── #952: Maybe / Either / Ordering / Bool ───────────────────────
  print (Just (1 :: Int) == Just 1)
  print (Just (1 :: Int) == Nothing)
  print (compare Nothing (Just (1 :: Int)))
  print (compare (Just (2 :: Int)) (Just 1))
  print ((Left (1 :: Int) :: Either Int Bool) == Left 1)
  print (compare (Left (1 :: Int) :: Either Int Bool) (Right True))
  print (compare (Right True :: Either Int Bool) (Right False))
  print (compare LT GT)
  print (EQ /= GT)
  print (compare False True)
  print (max False True)

  -- ── #952: tuples, lexicographic ──────────────────────────────────
  print (((1 :: Int), (2 :: Int)) == ((1 :: Int), (2 :: Int)))
  print (compare ((1 :: Int), (2 :: Int)) ((1 :: Int), (3 :: Int)))
  print (compare ((2 :: Int), (0 :: Int)) ((1 :: Int), (9 :: Int)))
  print (compare ((1 :: Int), (2 :: Int), 'a') ((1 :: Int), (2 :: Int), 'b'))
  print (max ((1 :: Int), (9 :: Int)) ((2 :: Int), (0 :: Int)))
  print (((1 :: Int), 'a', True, "s", LT) == ((1 :: Int), 'a', True, "s", LT))
  -- Width 15, differing only in the last component.
  print (compare
          ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int), (11 :: Int), (12 :: Int), (13 :: Int), (14 :: Int), (15 :: Int))
          ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int), (11 :: Int), (12 :: Int), (13 :: Int), (14 :: Int), (16 :: Int)))
  -- Through a higher-order function again, at a tuple element type.
  print (filter (\t -> t == ((1 :: Int), 'a')) [((1 :: Int), 'a'), ((2 :: Int), 'b')])
  -- Sorting a list of tuples reaches `Ord` on both the list and the tuple,
  -- and must be stable on the tied first components.
  print (sort [((2 :: Int), 'b'), ((1 :: Int), 'z'), ((1 :: Int), 'a')])
  print (sortBy (comparing snd) [((2 :: Int), "b"), ((1 :: Int), "a")])

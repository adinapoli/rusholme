-- GHC testsuite: tuple types, unit, and tuple expressions
module Sc021TupleTypes where

-- Unit
unit :: ()
unit = ()

-- Pair
pair :: (Int, String)
pair = (42, "hello")

-- Triple
triple :: (Bool, Int, String)
triple = (True, 0, "world")

-- 4-tuple
quad :: (Int, Int, Int, Int)
quad = (1, 2, 3, 4)

-- Nested tuples
nested :: ((Int, Bool), (String, Double))
nested = ((1, True), ("hi", 3.14))

-- Tuple in type alias
type Coord = (Double, Double, Double)

origin3d :: Coord
origin3d = (0.0, 0.0, 0.0)

-- Tuple function type
applyPair :: (a -> b, a) -> b
applyPair (f, x) = f x

-- fst and snd style
proj1 :: (a, b, c) -> a
proj1 (x, _, _) = x

proj2 :: (a, b, c) -> b
proj2 (_, y, _) = y

proj3 :: (a, b, c) -> c
proj3 (_, _, z) = z

-- Tuple constructor as function
pairUp :: a -> b -> (a, b)
pairUp x y = (x, y)

-- Unary tuple (parenthesised, not actually a tuple)
notATuple :: Int
notATuple = (42)

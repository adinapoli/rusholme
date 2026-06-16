-- e2e_851: Derived Eq/Ord for constructors with fields.
--
-- Regression test for #851: deriving Eq/Ord on a constructor carrying
-- fields used to crash at runtime ("Non-exhaustive patterns in case").
-- The cause was that every node a deriving builder emits shares the one
-- `deriving (...)` source span, and the desugarer's dictionary-evidence
-- map is keyed by span — so the field comparison `x == y` (needing the
-- field's instance) and `(/=)`'s own `x == y` (needing the data type's
-- instance) collided, and the field comparison was handed the wrong
-- dictionary, dispatching on the wrong constructor.
--
-- Covers single-field, multi-field, and multi-constructor-with-fields.

data Age = Age Int deriving (Eq, Ord)

data Point = Point Int Int deriving (Eq, Ord)

data Mix = Nil | Cons Int deriving (Eq, Ord)

main :: IO ()
main = do
  -- single-field Eq
  putStrLn (case Age 1 == Age 1 of True -> "T"; False -> "F")  -- T
  putStrLn (case Age 1 == Age 2 of True -> "T"; False -> "F")  -- F
  -- multi-field Eq
  putStrLn (case Point 1 2 == Point 1 2 of True -> "T"; False -> "F")  -- T
  putStrLn (case Point 1 2 == Point 1 3 of True -> "T"; False -> "F")  -- F
  -- single-field Ord
  putStrLn (case compare (Age 1) (Age 2) of LT -> "LT"; EQ -> "EQ"; GT -> "GT")  -- LT
  -- multi-field Ord (lexicographic)
  putStrLn (case compare (Point 1 2) (Point 1 3) of LT -> "LT"; EQ -> "EQ"; GT -> "GT")  -- LT
  putStrLn (case compare (Point 2 0) (Point 1 9) of LT -> "LT"; EQ -> "EQ"; GT -> "GT")  -- GT
  -- multi-constructor with a field
  putStrLn (case Cons 5 == Cons 5 of True -> "T"; False -> "F")  -- T
  putStrLn (case Cons 5 == Nil of True -> "T"; False -> "F")     -- F
  putStrLn (case compare Nil (Cons 0) of LT -> "LT"; EQ -> "EQ"; GT -> "GT")  -- LT

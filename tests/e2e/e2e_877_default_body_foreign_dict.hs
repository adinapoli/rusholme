-- e2e: a class default method body resolves a *foreign* class's dictionary at
-- a concrete type (#877).
--
-- `rank`'s default body calls `compare` (an `Ord` method) on the `Int`s
-- returned by `measure`.  That `compare` is `Ord Int` and must dispatch
-- through the concrete `dict$Ord$Int`.  Before #877 the default body was not
-- type-checked, so no evidence was recorded for `compare` and it dispatched
-- through a garbage dictionary — a runtime "Non-exhaustive patterns" crash.
module Main where

class Measure a where
  measure :: a -> Int
  rank :: a -> a -> Ordering
  rank x y = compare (measure x) (measure y)

data Box = MkBox Int

instance Measure Box where
  measure (MkBox n) = n
  -- inherits the `rank` default

main :: IO ()
main = do
  print (rank (MkBox 3) (MkBox 5))
  print (rank (MkBox 5) (MkBox 5))
  print (rank (MkBox 9) (MkBox 2))

module Main where

-- Test: Bounded and Enum classes from the Prelude.
-- Exercises derived instances for a simple enumeration type.
-- Bounded Int is deferred (Negate not lowered, issue #212).
-- Standalone class method calls (minBound, maxBound, succ, etc.) on derived
-- types are deferred (dictionary-passing for standalone method calls on
-- derived instances not yet working; see follow-up issues).

data Color = Red | Green | Blue deriving (Eq, Show, Bounded, Enum)

main :: IO ()
main = do
  -- Enum: fromEnum maps constructors to indices
  print (fromEnum Red)
  print (fromEnum Green)
  print (fromEnum Blue)
  -- Enum: toEnum maps indices back
  print (toEnum 0 :: Color)
  print (toEnum 1 :: Color)
  print (toEnum 2 :: Color)

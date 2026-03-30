-- Regression test for issue #660:
-- A class with a default method implementation must not corrupt the name
-- resolution of subsequent class declarations.
--
-- Before the fix, the compiler would emit:
--   error[E002]: unbound variable 'show' in typechecker (renamer bug?)
-- for the 'show' method of the second class.
module Sc050ClassDefaultMethod where

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  (/=) x y = (==) x y

class Show a where
  show :: a -> String

-- Using 'show' from the second class in a constrained function
-- confirms it was correctly registered by the renamer/typechecker.
showIt :: Show a => a -> String
showIt x = show x

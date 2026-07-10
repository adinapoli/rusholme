module Main where

-- #873 (epic #845): overlapping instances with a bare type-variable catch-all
-- head. `Describe a` (an OVERLAPPABLE catch-all) shares no outermost head
-- constructor with the specific `Describe Int` / `Describe Bool` instances, so
-- codegen must give the catch-all dictionary a stable slot distinct from each
-- specific one (previously it was keyed on the target type's constructor and
-- never found, producing an undefined-dictionary link error).

class Describe a where
  describe :: a -> Int

-- Bare type-variable catch-all: matches any type, overridden where a more
-- specific instance exists.
instance {-# OVERLAPPABLE #-} Describe a where
  describe _ = 0

instance Describe Int where
  describe _ = 1

instance Describe Bool where
  describe _ = 2

main :: IO ()
main = do
  print (describe (5 :: Int))   -- 1  specific Int wins over the catch-all
  print (describe True)         -- 2  specific Bool wins over the catch-all
  print (describe 'x')          -- 0  catch-all (Char has no specific instance)

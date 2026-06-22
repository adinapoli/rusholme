module Main where

-- {-# OVERLAPPING #-} / {-# OVERLAPPABLE #-} instance pragmas (#872, epic #845).
-- A strictly more specific instance overrides a general one when the overlap
-- pragmas permit it; an unmarked, non-overlapping match still resolves
-- normally.

class Describe a where
  describe :: a -> String

instance Describe Bool where
  describe _ = "bool"

instance Describe Char where
  describe _ = "char"

-- General list instance.
instance Describe a => Describe [a] where
  describe _ = "list"

-- More specific instance, marked OVERLAPPING: wins over `Describe [a]`
-- for `[Bool]`.
instance {-# OVERLAPPING #-} Describe [Bool] where
  describe _ = "list of bool"

-- Second class exercising OVERLAPPABLE on the general instance instead.
class Tag a where
  tag :: a -> Int

instance Tag Char where
  tag _ = 9

instance {-# OVERLAPPABLE #-} Tag a => Tag [a] where
  tag _ = 1

instance Tag [Bool] where
  tag _ = 2

main :: IO ()
main = do
  putStrLn (describe True)        -- bool          (concrete instance)
  putStrLn (describe 'x')         -- char          (concrete instance)
  putStrLn (describe [True])      -- list of bool  (OVERLAPPING wins)
  putStrLn (describe "ab")        -- list          ([Char], no overlap)
  print (tag [True])              -- 2             (OVERLAPPABLE general pruned)
  print (tag "ab")                -- 1             ([Char], only general matches)

-- e2e: superclass dictionaries in class default-method bodies (#898).
--
-- A default method body calling a *superclass* method over the class type
-- variable: `same x y = x == y` inside `class Eq a => Labeled a` needs the
-- Eq dictionary extracted from the Labeled dictionary parameter of the
-- default binding.  Also exercises a two-hop chain (Grandchild -> Child ->
-- Eq) and an instance that overrides one default but inherits the other.
module Main where

class Eq a => Labeled a where
  label :: a -> String
  same :: a -> a -> Bool
  same x y = x == y
  tag :: a -> a -> String
  tag x y =
    if same x y
      then label x
      else "differs"

data Coin = Heads | Tails

instance Eq Coin where
  Heads == Heads = True
  Tails == Tails = True
  _ == _ = False
  x /= y = not (x == y)

-- Inherits both defaults.
instance Labeled Coin where
  label Heads = "heads"
  label Tails = "tails"

data Dice = Dice Int

instance Eq Dice where
  Dice a == Dice b = a == b
  x /= y = not (x == y)

-- Overrides `same`, inherits `tag` (whose default calls the overridden
-- `same` through the dictionary).
instance Labeled Dice where
  label (Dice n) = "dice"
  same (Dice a) (Dice b) = a == b || a + b == 7

-- Two-hop chain: Deep's default body calls (==), Eq reached via Mid.
class Eq a => Mid a where
  midName :: a -> String

class Mid a => Deep a where
  deepEq :: a -> a -> Bool
  deepEq x y = x == y

instance Mid Coin where
  midName _ = "mid-coin"

instance Deep Coin

main :: IO ()
main = do
  print (same Heads Heads)
  print (same Heads Tails)
  putStrLn (tag Heads Heads)
  putStrLn (tag Heads Tails)
  print (same (Dice 3) (Dice 4))
  putStrLn (tag (Dice 3) (Dice 4))
  putStrLn (tag (Dice 2) (Dice 2))
  print (deepEq Tails Tails)
  print (deepEq Heads Tails)

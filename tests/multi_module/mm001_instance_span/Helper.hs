-- Regression fixture for #962: instances used to be identified by line and
-- column alone, with no file, so the `Ord` instance below could be mistaken
-- for the one at the same position in Main.hs.
--
-- Both `instance Ord` declarations MUST start on line 12, column 1.  Every
-- method is written out so the fixture does not depend on class defaults.
module Helper (Wrap (..)) where

data Wrap a = Wrap a


instance Ord a => Ord (Wrap a) where
  compare (Wrap x) (Wrap y) = compare x y
  (<)  (Wrap x) (Wrap y) = x <  y
  (<=) (Wrap x) (Wrap y) = x <= y
  (>)  (Wrap x) (Wrap y) = x >  y
  (>=) (Wrap x) (Wrap y) = x >= y

instance Eq a => Eq (Wrap a) where
  (==) (Wrap x) (Wrap y) = x == y
  (/=) (Wrap x) (Wrap y) = x /= y

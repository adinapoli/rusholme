-- #765: nullary class-method CAFs apply their dictionary evidence, and
-- imported non-builtin types (Ordering) used in signatures resolve to the
-- unique their instances were registered under.
--
-- Also covers #712: standalone `minBound`/`maxBound` on a user-defined
-- type with derived instances (the remaining broken case there shared the
-- nullary-CAF root cause).
module Main where

data Color = Red | Green | Blue deriving (Show, Eq, Ord, Enum, Bounded)

loColor :: Color
loColor = minBound

hiColor :: Color
hiColor = maxBound

loBool :: Bool
loBool = minBound

hiBool :: Bool
hiBool = maxBound

loOrd :: Ordering
loOrd = minBound

hiOrd :: Ordering
hiOrd = maxBound

-- An Ordering used directly in a type annotation must also resolve.
mid :: Ordering
mid = EQ

main :: IO ()
main = do
    print loBool
    print hiBool
    print loOrd
    print hiOrd
    print mid
    print (compare (3 :: Int) 2)
    print (minBound :: Color)
    print (maxBound :: Color)
    print loColor
    print hiColor
    print (succ Red)
    print (pred Blue)
    print (fromEnum Green)
    print (toEnum 2 :: Color)

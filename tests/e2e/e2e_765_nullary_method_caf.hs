-- #765: nullary class-method CAFs apply their dictionary evidence, and
-- imported non-builtin types (Ordering) used in signatures resolve to the
-- unique their instances were registered under.
module Main where

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

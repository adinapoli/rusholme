-- Prelude regression: Bounded(..) — minBound, maxBound (#759).
--
-- Regression for #765: nullary class-method CAFs (`loBool = minBound`)
-- now apply their dictionary evidence, and imported non-builtin types
-- (`Ordering`) resolve to the unique their instances were registered
-- under, so `Show`/`Bounded Ordering` are found.
module Main where

loBool :: Bool
loBool = minBound

hiBool :: Bool
hiBool = maxBound

loOrd :: Ordering
loOrd = minBound

hiOrd :: Ordering
hiOrd = maxBound

main :: IO ()
main = do
    print loBool
    print hiBool
    print loOrd
    print hiOrd

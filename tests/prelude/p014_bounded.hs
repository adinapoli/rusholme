-- Prelude regression: Bounded(..) — minBound, maxBound (#759).
--
-- xfail: nullary class-method CAFs miscompile — Bool segfaults at
-- runtime, Ordering fails to compile with a bogus "no instance for
-- `Show Ordering`" error.  Tracked in #765.
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

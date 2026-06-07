-- Prelude regression: Enum(..) (succ, pred, toEnum, fromEnum),
-- enumFrom, enumFromTo, enumFromThen, enumFromThenTo (#759).
--
-- NOTE: Bounded(..) (minBound/maxBound) lives in p014_bounded.hs (xfail)
-- because nullary class-method CAFs currently miscompile — tracked in #765.
module Main where

charC :: Char
charC = toEnum 67

main :: IO ()
main = do
    print (succ 3)
    print (pred 3)
    print (fromEnum True)
    print charC
    print (enumFromTo 1 5)
    print (enumFromThenTo 1 3 9)
    print (take 3 (enumFrom 5))
    print (take 3 (enumFromThen 4 6))

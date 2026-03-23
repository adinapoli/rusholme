-- e2e_factorial: Recursive factorial with print
--
-- Tests that show/print works correctly on results of recursive
-- functions, which previously segfaulted when large results like
-- 5040 passed the heap-pointer alignment heuristic (issue #624).

module Factorial where

factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)

main :: IO ()
main = do
    print (factorial 0)
    print (factorial 1)
    print (factorial 5)
    print (factorial 7)
    print (factorial 10)

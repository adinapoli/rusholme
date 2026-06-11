-- Bench: tight arithmetic loop (GCD computation).
--
-- Inspired by the Benchmarks Game "pidigits" spigot algorithm's
-- inner GCD loop. Runs Euclid's GCD algorithm many times over
-- pairs of integers. Pure integer arithmetic with no heap
-- allocation whatsoever. Measures raw codegen quality for tight
-- arithmetic loops and recursive calls.

mygcd :: Int -> Int -> Int
mygcd a 0 = a
mygcd a b = mygcd b (mymod a b)

mymod :: Int -> Int -> Int
mymod a b = if a < b then a else mymod (a - b) b

-- Run GCD on many pairs.
sumGcds :: Int -> Int -> Int
sumGcds 0 _ = 0
sumGcds n k = mygcd n k + sumGcds (n - 1) (k + 1)

main = putStrLn (show (sumGcds 2000 1))
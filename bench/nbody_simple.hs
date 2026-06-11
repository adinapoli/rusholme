-- Bench: deep recursion with accumulation (stack stress).
--
-- Inspired by the Benchmarks Game "n-body" simulation's inner
-- loop. Computes a simple numerical recurrence (Newton's method
-- for integer square root) many times in a tight loop. Stresses
-- integer arithmetic, recursive calls, and accumulator passing
-- without heap allocation. Good for measuring call overhead.

isqrt :: Int -> Int -> Int
isqrt n x = if x * x <= n && (x + 1) * (x + 1) > n then x
            else isqrt n ((x + mydiv n x) `mydiv` 2)

mydiv :: Int -> Int -> Int
mydiv a b = if b == 0 then 0 else mydivHelper (if a < 0 then -a else a) (if b < 0 then -b else b) 0

mydivHelper :: Int -> Int -> Int -> Int
mydivHelper a b q = if a < b then q else mydivHelper (a - b) b (q + 1)

-- Sum of isqrt(i) for i in [1..n]
sumSqrt :: Int -> Int -> Int
sumSqrt acc 0 = acc
sumSqrt acc n = sumSqrt (acc + isqrt n 1) (n - 1)

main = putStrLn (show (sumSqrt 0 5000))
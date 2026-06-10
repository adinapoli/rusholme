-- Bench: pure compute, no heap allocation.
--
-- Naive recursive Fibonacci. Bumps the call stack but never calls
-- `rts_alloc`. Isolates the cost of function calls + integer
-- arithmetic from anything GC-related; a useful control against
-- the alloc-heavy benches.

fib :: Int -> Int
fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)

main = putStrLn (show (fib 30))

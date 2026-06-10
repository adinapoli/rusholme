-- Bench: arithmetic / recursion baseline.
--
-- Tail-style recursion over an Int range. Stresses call overhead
-- (every step is a function call) without allocating heap nodes
-- on the hot path. Useful as a control against the alloc-heavy
-- benches: divergence here points at codegen quality, not at GC.

sumTo :: Int -> Int -> Int
sumTo acc 0 = acc
sumTo acc n = sumTo (acc + n) (n - 1)

main = putStrLn (show (sumTo 0 50000))

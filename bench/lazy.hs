-- Bench: call-by-need thunk evaluation (laziness overhead).
--
-- Inspired by the Benchmarks Game benchmarks that rely on lazy
-- evaluation. Creates deeply nested let-bindings where most are
-- never forced, testing the runtime's ability to skip evaluation
-- of unused thunks. Also tests that *used* thunks are evaluated
-- correctly and only once (sharing). Stresses the thunk machinery
-- rather than raw compute.

data List = Nil | Cons Int List

-- Build a long list of lazy computations. Each element is the
-- sum of the previous two (like Fibonacci) reduced mod 10^9+7 so
-- the values never overflow (rhc Int wraps at 63 bits vs GHC's 64,
-- see issue #813), computed via let-bindings evaluated lazily.
lazyFibList :: Int -> Int -> Int -> List
lazyFibList a b 0 = Nil
lazyFibList a b n = Cons a (lazyFibList b (mod (a + b) 1000000007) (n - 1))

-- Sum only the even-indexed elements (forcing half the thunks).
sumEveryOther :: List -> Int -> Int
sumEveryOther Nil _ = 0
sumEveryOther (Cons x xs) 0 = x + sumEveryOther xs 1
sumEveryOther (Cons _ xs) 1 = sumEveryOther xs 0

-- Deep let-nesting: chains of let-bindings that are mostly unused.
deepLet :: Int -> Int
deepLet 0 = 42
deepLet n = let unused = deepLet (n - 1)  -- never forced
                used   = n
            in used + deepLet (n - 1)

main = putStrLn (show (sumEveryOther (lazyFibList 0 1 2000) 0 + deepLet 500))
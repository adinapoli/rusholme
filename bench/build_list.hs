-- Bench: allocation-heavy list build + traversal.
--
-- Builds a long Cons list, then folds it. Every Cons cell is a
-- heap allocation, so the inner loop is dominated by `rts_alloc`.
-- Under `--rts=immix` this exercises the block allocator + the
-- per-tag pointer-mask tracer (#779) + the shadow-stack root
-- discipline (#780) + the opportunistic defrag pass (#73) when
-- it is opted in.

data List a = Nil | Cons a (List a)

range :: Int -> Int -> List Int
range lo hi = if lo > hi then Nil else Cons lo (range (lo + 1) hi)

sumList :: List Int -> Int
sumList Nil = 0
sumList (Cons x xs) = x + sumList xs

main = putStrLn (show (sumList (range 1 5000)))

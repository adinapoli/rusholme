-- Test 327: PrimOp / GC integration.
--
-- Exercises the chain of guarantees in decision 0327:
--   * PrimOp arguments are rooted by the caller's shadow stack.
--   * Comparison + arithmetic PrimOps emit inline IR with no
--     mid-call safepoint, so they cannot drop a live root.
--   * Allocating PrimOps (Bool boxing from comparisons, String
--     primops, Pure-ConstTagNode constructors) route through
--     `rts_alloc` and survive auto-collect under --rts=immix.
--
-- The program builds a long list, then folds it through a
-- comparison-heavy predicate. Under --rts=immix the block budget
-- overflows mid-build, so auto-collect fires while the partial list
-- AND the comparison's PrimOp arguments are on the shadow stack.
-- Wrong rooting either crashes or returns garbage.

data List a = Nil | Cons a (List a)

range :: Int -> Int -> List Int
range lo hi = if lo > hi then Nil else Cons lo (range (lo + 1) hi)

isEven :: Int -> Bool
isEven n = mod n 2 == 0

countEvens :: List Int -> Int
countEvens Nil = 0
countEvens (Cons x xs) =
  if isEven x
    then 1 + countEvens xs
    else countEvens xs

main = putStrLn (show (countEvens (range 1 1500)))

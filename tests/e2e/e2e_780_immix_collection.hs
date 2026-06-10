-- Test 780: Immix GC exercises collection across multiple allocation
-- sites while live roots remain reachable through the shadow stack.
--
-- Building a long list under --rts=immix forces block-budget overflow
-- and triggers auto-collection while the recursive build is still on
-- the stack. The collector must follow shadow-stack roots to keep the
-- partial list alive; if rooting is broken the program either
-- segfaults during the recursive build or returns garbage.

data List a = Nil | Cons a (List a)

range :: Int -> Int -> List Int
range lo hi = if lo > hi then Nil else Cons lo (range (lo + 1) hi)

sumList :: List Int -> Int
sumList Nil = 0
sumList (Cons x xs) = x + sumList xs

main = putStrLn (show (sumList (range 1 2000)))

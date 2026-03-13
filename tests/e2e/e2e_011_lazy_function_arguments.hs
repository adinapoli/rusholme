-- e2e_011: Lazy function arguments
--
-- Tests that function arguments are not eagerly evaluated (call-by-need semantics).
-- `unused` is a user-defined function that would recurse infinitely if
-- evaluated.  `myConst` ignores its second argument, so `unused` should
-- never be forced — the program should print "hello" and exit normally.

myConst :: b -> a -> b
myConst x _ = x

unused :: a -> b
unused x = unused x

main = putStrLn (myConst "hello" (unused 0))

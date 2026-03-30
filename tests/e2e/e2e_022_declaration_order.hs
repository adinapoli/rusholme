-- Regression test for issue #566: declaration order must not affect inference.
-- f calls g which is defined later. Both have type signatures.
f :: Int -> Int
f x = g (x + 1)

g :: Int -> Int
g x = x * 2

main = print (f 5)

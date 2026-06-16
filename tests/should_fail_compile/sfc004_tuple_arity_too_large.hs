-- #848: a tuple of arity > 7 is not yet supported end-to-end. The compiler
-- must cleanly reject it rather than silently miscompile.
--
-- Under `rhc build` (full Prelude) this reports the clear diagnostic
-- "tuples of arity greater than 7 are not yet supported …". This harness
-- runs without the Prelude, so it only asserts that compilation fails (any
-- diagnostic), guarding against a silent miscompile or crash.
sum8 :: (Int, Int, Int, Int, Int, Int, Int, Int) -> Int
sum8 (a, b, c, d, e, f, g, h) = a + b + c + d + e + f + g + h

main :: IO ()
main = print (sum8 (1, 2, 3, 4, 5, 6, 7, 8))

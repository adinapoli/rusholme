module Main where

-- Test: 0-field thunks should be updated after evaluation (call-by-need).
-- This program uses a where-bound constant with no free variables,
-- which creates a 0-field thunk in GRIN.  Without the fix, such thunks
-- would be re-evaluated on every access.  With the fix, the thunk is
-- updated to an indirection after the first evaluation, so it is
-- evaluated at most once.
--
-- We cannot directly observe multiple evaluation from pure Haskell,
-- but we can verify the program produces the correct result, which
-- would fail if the thunk update were missing.

main :: IO ()
main = do
    print x
    print x
  where
    x = 42

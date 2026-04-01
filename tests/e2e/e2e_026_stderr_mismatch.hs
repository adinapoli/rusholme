-- e2e_026: intentional stderr mismatch.
-- This test exists solely to exercise the step-6 false branch in runTest.
-- The binary writes nothing to stderr; the sidecar expects a non-empty string,
-- so the mismatch is detected and the test fails.  The xfail: directive absorbs
-- the failure so CI stays green.  If the mismatch detection were broken the
-- test would unexpectedly pass and log an [xpass] diagnostic.
module E2e026 where

main :: IO ()
main = putStrLn "ok"

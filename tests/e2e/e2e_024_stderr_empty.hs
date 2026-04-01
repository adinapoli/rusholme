-- e2e_024: verify that a program with an expected .stderr sidecar passes
-- when the compiled binary produces no stderr output.
module E2e024 where

main :: IO ()
main = putStrLn "no stderr"

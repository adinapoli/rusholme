-- e2e_025: verify that the inline `stderr:` properties directive works
-- when the compiled binary produces no stderr output.
module E2e025 where

main :: IO ()
main = putStrLn "inline stderr check"

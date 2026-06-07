-- Prelude regression: error (#759).
--
-- The program must terminate with a non-zero exit code and report the
-- message on stderr; nothing may reach stdout after the error fires.
module Main where

main :: IO ()
main = do
    putStrLn "before"
    error "boom"

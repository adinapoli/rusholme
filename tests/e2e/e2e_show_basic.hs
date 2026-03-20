-- e2e_show_basic: Basic Show typeclass instances
--
-- Tests Show instances for Int, Bool, and Char.

module ShowBasic where

main :: IO ()
main = do
    putStrLn (show 42)
    putStrLn (show True)
    putStrLn (show False)
    putStrLn (show 'a')
    putStrLn (show 0)
    putStrLn (show 123)

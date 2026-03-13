-- e2e_011: foreign import prim
--
-- Tests that foreign import prim declarations correctly bind Haskell
-- names to GRIN primitive operations and produce working executables.

foreign import prim "putStrLn" myPutStrLn :: String -> IO ()

main = myPutStrLn "Hello from foreign import prim"

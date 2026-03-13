-- e2e_011: foreign import prim
--
-- Tests that foreign import prim declarations correctly bind Haskell
-- names to GRIN primitive operations and produce working executables.
--
-- NOTE: putStrLn is conceptually an RTS call (foreign import ccall),
-- not a true PrimOp. It works here because the LLVM backend's
-- PrimOpMapping dispatches it as a libcall. Once foreign import ccall
-- is implemented (#536), this should migrate to use ccall instead.

foreign import prim "putStrLn" myPutStrLn :: String -> IO ()

main = myPutStrLn "Hello from foreign import prim"

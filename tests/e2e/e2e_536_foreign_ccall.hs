-- foreign import ccall to RTS functions (#536).
--
-- `foreign import ccall` binds a Haskell name directly to a C-calling-
-- convention RTS symbol. This is layer 2 of the FFI architecture:
--   1. foreign import prim   — GRIN PrimOps → LLVM instructions
--   2. foreign import ccall  — RTS functions → C calls (this test)
--   3. Haskell wrappers in Prelude.hs over either
{-# LANGUAGE NoImplicitPrelude #-}

foreign import ccall "rts_putStrLn" cPutStrLn :: String -> IO ()
foreign import ccall "rts_putStr" cPutStr :: String -> IO ()
foreign import ccall "rts_putChar" cPutChar :: Char -> IO ()

main :: IO ()
main = do
    cPutStrLn "hello from ccall"
    cPutStr "no newline, "
    cPutStrLn "then one"
    cPutChar 'x'
    cPutChar '\n'

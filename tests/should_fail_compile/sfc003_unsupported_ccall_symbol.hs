{-# LANGUAGE NoImplicitPrelude #-}
module Sfc003UnsupportedCcallSymbol where

-- This should fail during desugaring (#536): `rts_bogus` is not one of
-- the RTS symbols the backend has a ccall signature descriptor for.

foreign import ccall "rts_bogus" cBogus :: Int -> IO ()

main :: IO ()
main = cBogus 42

-- Test 047: foreign import prim declarations
-- Verifies that the parser accepts the `foreign import prim` syntax
-- for binding Haskell names to GRIN primitive operations.

{-# LANGUAGE NoImplicitPrelude #-}
module ForeignImportPrimTest where

foreign import prim "add_Int" primAddInt :: Int -> Int -> Int

foreign import prim "putStrLn" primPutStrLn :: String -> IO ()

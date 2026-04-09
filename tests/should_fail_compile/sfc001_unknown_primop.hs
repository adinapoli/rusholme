{-# LANGUAGE NoImplicitPrelude #-}
module Sfc001UnknownPrimop where

-- This should fail during desugaring because "bogus_primop" is not
-- a recognised primitive operation.

foreign import prim "bogus_primop" primBogus :: Int -> Int

main :: IO ()
main = primBogus 42

{-# LANGUAGE NoImplicitPrelude #-}
module Sfc002UnboundVariable where

-- This should fail during renaming because "undefined_function" is not
-- in scope.

main :: IO ()
main = undefined_function 42

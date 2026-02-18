-- GHC testsuite: default declarations
module Sc025DefaultDecl where

default (Int, Double)

-- Numeric default resolution
-- GHC uses this when a numeric literal is ambiguous

-- A plain numeric function
twice :: Num a => a -> a
twice x = x + x

-- Another numeric op
square :: Num a => a -> a
square x = x * x

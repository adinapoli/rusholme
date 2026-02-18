-- Should fail: lambda missing the -> arrow
module Sf009LambdaNoArrow where

f :: Int -> Int
f = \x x

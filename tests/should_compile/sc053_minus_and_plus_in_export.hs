-- sc053: (-) and (+) in module export list
-- Regression test for https://github.com/adinapoli/rusholme/issues/538
--
-- Larger realistic case: multiple operators including (-) exported together.
-- Prefix negate in expressions must not be affected.

module MinusPlusExport ( (-), (+), negate ) where

negate :: Int -> Int
negate x = -x

add :: Int -> Int -> Int
add x y = x + y

subtract_ :: Int -> Int -> Int
subtract_ x y = x - y

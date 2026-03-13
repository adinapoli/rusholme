-- e2e_013: Prelude arithmetic functions
--
-- Tests (+), (-), (*), negate, abs, div, mod from the Prelude.
-- Self-contained with NoImplicitPrelude. Since we cannot use show/print
-- (no type classes yet), we test by comparing results with primEqInt
-- and printing "ok" or "FAIL".

{-# LANGUAGE NoImplicitPrelude #-}

foreign import prim "putStrLn" putStrLn :: String -> IO ()
foreign import prim "add_Int"  primAddInt  :: Int -> Int -> Int
foreign import prim "sub_Int"  primSubInt  :: Int -> Int -> Int
foreign import prim "mul_Int"  primMulInt  :: Int -> Int -> Int
foreign import prim "neg_Int"  primNegInt  :: Int -> Int
foreign import prim "abs_Int"  primAbsInt  :: Int -> Int
foreign import prim "quot_Int" primQuotInt :: Int -> Int -> Int
foreign import prim "rem_Int"  primRemInt  :: Int -> Int -> Int
foreign import prim "eq_Int"   primEqInt   :: Int -> Int -> Bool

data Bool = False | True

(+) :: Int -> Int -> Int
(+) = primAddInt
infixl 6 +

(-) :: Int -> Int -> Int
(-) = primSubInt
infixl 6 -

(*) :: Int -> Int -> Int
(*) = primMulInt
infixl 7 *

negate :: Int -> Int
negate = primNegInt

abs :: Int -> Int
abs = primAbsInt

div :: Int -> Int -> Int
div = primQuotInt

mod :: Int -> Int -> Int
mod = primRemInt

(==) :: Int -> Int -> Bool
(==) = primEqInt
infix 4 ==

check :: String -> Bool -> IO ()
check label True  = putStrLn label
check label False = putStrLn "FAIL"

main :: IO ()
main = do
    check "add"    (2 + 3 == 5)
    check "sub"    (10 - 4 == 6)
    check "mul"    (3 * 7 == 21)
    check "negate" (negate 5 == (0 - 5))
    check "abs"    (abs (0 - 42) == 42)
    check "div"    (div 17 5 == 3)
    check "mod"    (mod 17 5 == 2)

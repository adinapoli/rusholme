-- e2e_014: Prelude comparison functions
--
-- Tests (==), (/=), (<), (>), (<=), (>=) from the Prelude.
-- Self-contained with NoImplicitPrelude.

{-# LANGUAGE NoImplicitPrelude #-}

foreign import prim "putStrLn" putStrLn :: String -> IO ()
foreign import prim "eq_Int"   primEqInt :: Int -> Int -> Bool
foreign import prim "ne_Int"   primNeInt :: Int -> Int -> Bool
foreign import prim "lt_Int"   primLtInt :: Int -> Int -> Bool
foreign import prim "le_Int"   primLeInt :: Int -> Int -> Bool
foreign import prim "gt_Int"   primGtInt :: Int -> Int -> Bool
foreign import prim "ge_Int"   primGeInt :: Int -> Int -> Bool

data Bool = False | True

(==) :: Int -> Int -> Bool
(==) = primEqInt
infix 4 ==

(/=) :: Int -> Int -> Bool
(/=) = primNeInt
infix 4 /=

(<) :: Int -> Int -> Bool
(<) = primLtInt
infix 4 <

(>) :: Int -> Int -> Bool
(>) = primGtInt
infix 4 >

(<=) :: Int -> Int -> Bool
(<=) = primLeInt
infix 4 <=

(>=) :: Int -> Int -> Bool
(>=) = primGeInt
infix 4 >=

showBool :: Bool -> String
showBool True  = "True"
showBool False = "False"

main :: IO ()
main = do
    -- equality
    putStrLn (showBool (5 == 5))
    putStrLn (showBool (5 == 3))
    -- inequality
    putStrLn (showBool (5 /= 3))
    putStrLn (showBool (5 /= 5))
    -- less than
    putStrLn (showBool (3 < 5))
    putStrLn (showBool (5 < 3))
    -- greater than
    putStrLn (showBool (5 > 3))
    putStrLn (showBool (3 > 5))
    -- less or equal
    putStrLn (showBool (3 <= 5))
    putStrLn (showBool (5 <= 5))
    putStrLn (showBool (5 <= 3))
    -- greater or equal
    putStrLn (showBool (5 >= 3))
    putStrLn (showBool (5 >= 5))
    putStrLn (showBool (3 >= 5))

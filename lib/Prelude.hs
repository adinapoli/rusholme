{-# LANGUAGE NoImplicitPrelude #-}
module Prelude
    ( Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    , not, (&&), (||), otherwise
    , (+), (-), (*), negate, abs, div, mod
    , (==), (/=), (<), (>), (<=), (>=)
    , id, const, flip, (.), ($)
    , head, tail, null, length
    , map, filter, foldr, foldl
    , (++), reverse, concat
    , take, drop
    , maybe, fromMaybe, either
    , putStrLn, putStr
    , error
    ) where

-- ========================================================================
-- PrimOp imports
-- ========================================================================

foreign import prim "add_Int"   primAddInt   :: Int -> Int -> Int
foreign import prim "sub_Int"   primSubInt   :: Int -> Int -> Int
foreign import prim "mul_Int"   primMulInt   :: Int -> Int -> Int
foreign import prim "neg_Int"   primNegInt   :: Int -> Int
foreign import prim "abs_Int"   primAbsInt   :: Int -> Int
foreign import prim "quot_Int"  primQuotInt  :: Int -> Int -> Int
foreign import prim "rem_Int"   primRemInt   :: Int -> Int -> Int
foreign import prim "eq_Int"    primEqInt    :: Int -> Int -> Bool
foreign import prim "ne_Int"    primNeInt    :: Int -> Int -> Bool
foreign import prim "lt_Int"    primLtInt    :: Int -> Int -> Bool
foreign import prim "le_Int"    primLeInt    :: Int -> Int -> Bool
foreign import prim "gt_Int"    primGtInt    :: Int -> Int -> Bool
foreign import prim "ge_Int"    primGeInt    :: Int -> Int -> Bool
foreign import prim "putStrLn"  primPutStrLn :: String -> IO ()
foreign import prim "putStr"    primPutStr   :: String -> IO ()
foreign import prim "error"     primError    :: String -> a

-- ========================================================================
-- Data types
-- ========================================================================

data Bool = False | True

data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

data Ordering = LT | EQ | GT

type String = [Char]

-- ========================================================================
-- Fixity declarations
-- ========================================================================

infixl 6 +, -
infixl 7 *, `div`, `mod`
infix  4 ==, /=, <, >, <=, >=
infixr 3 &&
infixr 2 ||
infixr 9 .
infixr 0 $
infixr 5 ++

-- ========================================================================
-- Identity and const
-- ========================================================================

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

-- ========================================================================
-- Error
-- ========================================================================

error :: String -> a
error = primError

-- ========================================================================
-- IO wrappers
-- ========================================================================

putStrLn :: String -> IO ()
putStrLn = primPutStrLn

putStr :: String -> IO ()
putStr = primPutStr

-- ========================================================================
-- Boolean functions
-- ========================================================================

not :: Bool -> Bool
not True  = False
not False = True

(&&) :: Bool -> Bool -> Bool
True  && x = x
False && _ = False

(||) :: Bool -> Bool -> Bool
True  || _ = True
False || x = x

otherwise :: Bool
otherwise = True

-- ========================================================================
-- Arithmetic (monomorphic on Int, pending type classes #531)
-- ========================================================================

(+) :: Int -> Int -> Int
(+) = primAddInt

(-) :: Int -> Int -> Int
(-) = primSubInt

(*) :: Int -> Int -> Int
(*) = primMulInt

negate :: Int -> Int
negate = primNegInt

abs :: Int -> Int
abs = primAbsInt

div :: Int -> Int -> Int
div = primQuotInt

mod :: Int -> Int -> Int
mod = primRemInt

-- ========================================================================
-- Comparison (monomorphic on Int, pending type classes #531)
-- ========================================================================

(==) :: Int -> Int -> Bool
(==) = primEqInt

(/=) :: Int -> Int -> Bool
(/=) = primNeInt

(<) :: Int -> Int -> Bool
(<) = primLtInt

(>) :: Int -> Int -> Bool
(>) = primGtInt

(<=) :: Int -> Int -> Bool
(<=) = primLeInt

(>=) :: Int -> Int -> Bool
(>=) = primGeInt

-- ========================================================================
-- Higher-order combinators
-- ========================================================================

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

($) :: (a -> b) -> a -> b
f $ x = f x

-- ========================================================================
-- List functions
-- ========================================================================

head :: [a] -> a
head (x:_) = x

tail :: [a] -> [a]
tail (_:xs) = xs

null :: [a] -> Bool
null []    = True
null (_:_) = False

length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ []     = []
filter p (x:xs) = if p x then x : filter p xs else filter p xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

(++) :: [a] -> [a] -> [a]
(++) []     ys = ys
(++) (x:xs) ys = x : (++) xs ys

reverse :: [a] -> [a]
reverse xs = revAcc xs []

revAcc :: [a] -> [a] -> [a]
revAcc []     acc = acc
revAcc (x:xs) acc = revAcc xs (x : acc)

concat :: [[a]] -> [a]
concat []       = []
concat (xs:xss) = (++) xs (concat xss)

take :: Int -> [a] -> [a]
take _ []     = []
take n (x:xs) = if n <= 0 then [] else x : take (n - 1) xs

drop :: Int -> [a] -> [a]
drop _ []     = []
drop n xxs = if n <= 0 then xxs else case xxs of { (_:xs) -> drop (n - 1) xs; [] -> [] }

-- ========================================================================
-- Maybe / Either functions
-- ========================================================================

maybe :: b -> (a -> b) -> Maybe a -> b
maybe n _ Nothing  = n
maybe _ f (Just x) = f x

fromMaybe :: a -> Maybe a -> a
fromMaybe d Nothing  = d
fromMaybe _ (Just x) = x

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right y) = g y

{-# LANGUAGE NoImplicitPrelude #-}
module Prelude
    ( Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    , not, (&&), (||), otherwise
    , (+), (-), (*), negate, abs, div, mod
    , (==), (/=), (<), (>), (<=), (>=)
    , id, const, flip, (.), ($)
    , map, filter, (++), head, tail, null, length
    , foldr, foldl, concat, take, drop
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
($) f x = f x

-- ========================================================================
-- List functions
-- ========================================================================

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter p []     = []
filter p (x:xs) = case p x of
    True  -> x : filter p xs
    False -> filter p xs

(++) :: [a] -> [a] -> [a]
(++) []     ys = ys
(++) (x:xs) ys = x : (++) xs ys

head :: [a] -> a
head (x:xs) = x

tail :: [a] -> [a]
tail (x:xs) = xs

null :: [a] -> Bool
null []    = True
null (x:xs) = False

length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

concat :: [[a]] -> [a]
concat []     = []
concat (x:xs) = (++) x (concat xs)

take :: Int -> [a] -> [a]
take n []     = []
take n (x:xs) = case n <= 0 of
    True  -> []
    False -> x : take (n - 1) xs

drop :: Int -> [a] -> [a]
drop n []     = []
drop n (x:xs) = case n <= 0 of
    True  -> x : xs
    False -> drop (n - 1) xs

-- ========================================================================
-- Maybe / Either
-- ========================================================================

maybe :: b -> (a -> b) -> Maybe a -> b
maybe n f Nothing  = n
maybe n f (Just x) = f x

fromMaybe :: a -> Maybe a -> a
fromMaybe d Nothing  = d
fromMaybe d (Just x) = x

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x)  = f x
either f g (Right y) = g y

-- ========================================================================
-- Polymorphic functions still blocked:
--   - reverse: uses (:) as higher-order value, needs constructor closures (#386)
--   - zip, unzip: needs tuple codegen (#571)
--   - fst, snd: needs tuple codegen (#571)
--   - show, read: needs dictionary-passing codegen (#569)
-- ========================================================================

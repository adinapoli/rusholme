{-# LANGUAGE NoImplicitPrelude #-}
module Prelude
    ( Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    , not, (&&), (||), otherwise
    , (+), (-), (*), negate, abs, div, mod
    , (==), (/=), (<), (>), (<=), (>=)
    , map, filter, foldr, foldl
    , head, tail, null, length
    , (++), reverse, concat
    , take, drop, zip
    , id, const, (.), ($), flip, fst, snd
    , maybe, fromMaybe, either
    , putStrLn, putStr
    , error
    ) where

-- ========================================================================
-- PrimOp imports
-- ========================================================================

-- Arithmetic
foreign import prim "add_Int"   primAddInt   :: Int -> Int -> Int
foreign import prim "sub_Int"   primSubInt   :: Int -> Int -> Int
foreign import prim "mul_Int"   primMulInt   :: Int -> Int -> Int
foreign import prim "neg_Int"   primNegInt   :: Int -> Int
foreign import prim "abs_Int"   primAbsInt   :: Int -> Int
foreign import prim "quot_Int"  primQuotInt  :: Int -> Int -> Int
foreign import prim "rem_Int"   primRemInt   :: Int -> Int -> Int

-- Comparison
foreign import prim "eq_Int"    primEqInt    :: Int -> Int -> Bool
foreign import prim "ne_Int"    primNeInt    :: Int -> Int -> Bool
foreign import prim "lt_Int"    primLtInt    :: Int -> Int -> Bool
foreign import prim "le_Int"    primLeInt    :: Int -> Int -> Bool
foreign import prim "gt_Int"    primGtInt    :: Int -> Int -> Bool
foreign import prim "ge_Int"    primGeInt    :: Int -> Int -> Bool

-- IO
foreign import prim "putStrLn"  primPutStrLn :: String -> IO ()
foreign import prim "putStr"    primPutStr   :: String -> IO ()

-- Error / control
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
-- List functions
-- ========================================================================

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

head :: [a] -> a
head []    = error "Prelude.head: empty list"
head (x:_) = x

tail :: [a] -> [a]
tail []     = error "Prelude.tail: empty list"
tail (_:xs) = xs

null :: [a] -> Bool
null []    = True
null (_:_) = False

length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

(++) :: [a] -> [a] -> [a]
(++) []     ys = ys
(++) (x:xs) ys = x : (xs ++ ys)

reverse :: [a] -> [a]
reverse = foldl (flip (:)) []

concat :: [[a]] -> [a]
concat = foldr (++) []

take :: Int -> [a] -> [a]
take _ []     = []
take n (x:xs) = if n <= 0 then [] else x : take (n - 1) xs

drop :: Int -> [a] -> [a]
drop _ []     = []
drop n xs     = if n <= 0 then xs else drop (n - 1) (tail xs)

zip :: [a] -> [b] -> [(a, b)]
zip []     _      = []
zip _      []     = []
zip (a:as) (b:bs) = (a, b) : zip as bs

-- ========================================================================
-- Higher-order / misc
-- ========================================================================

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

($) :: (a -> b) -> a -> b
f $ x = f x

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

fst :: (a, b) -> a
fst (x, _) = x

snd :: (a, b) -> b
snd (_, y) = y

-- ========================================================================
-- Maybe / Either
-- ========================================================================

maybe :: b -> (a -> b) -> Maybe a -> b
maybe z _ Nothing  = z
maybe _ f (Just x) = f x

fromMaybe :: a -> Maybe a -> a
fromMaybe d Nothing  = d
fromMaybe _ (Just x) = x

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left  x) = f x
either _ g (Right y) = g y

-- ========================================================================
-- IO wrappers
-- ========================================================================

putStrLn :: String -> IO ()
putStrLn = primPutStrLn

putStr :: String -> IO ()
putStr = primPutStr

-- ========================================================================
-- Error
-- ========================================================================

error :: String -> a
error = primError

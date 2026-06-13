{-# LANGUAGE NoImplicitPrelude #-}
module Prelude
    ( -- Re-exported from GHC.Base
      Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    , not, (&&), (||), otherwise
    , (+), (-), (*), negate, abs, div, mod
    , max, min, signum, even, odd
    , (==), (/=), (<), (>), (<=), (>=), compare
    , putChar, putStr, putStrLn
    , error
    , intToChar, charToInt
    , Eq(..)
    , Ord(..)
    , Bounded(..)
    , Enum(..)
    , Show(..), showString, showLitChar, showListWith, showListTail
    , intToDigit
    , enumFrom, enumFromTo, enumFromThen, enumFromThenTo
    -- Re-exported from Data.Function
    , id, const, flip, (.), ($)
    -- Defined locally
    , map, filter, (++), head, tail, null, length
    , foldr, foldl, concat, take, drop
    , maybe, fromMaybe, either
    , reverse
    , print
    , sum, product, replicate
    ) where

import RHC.Prim
import Data.Function
import GHC.Base

-- ========================================================================
-- print depends on Show (in GHC.Base) and putStrLn (in GHC.Base).
-- ========================================================================

print :: Show a => a -> IO ()
print x = putStrLn (show x)

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
head []     = error "Prelude.head: empty list"

tail :: [a] -> [a]
tail (x:xs) = xs
tail []     = error "Prelude.tail: empty list"

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
-- More numeric and list utilities
-- ========================================================================

sum :: [Int] -> Int
sum []     = 0
sum (x:xs) = x + sum xs

product :: [Int] -> Int
product []     = 1
product (x:xs) = x * product xs

replicate :: Int -> a -> [a]
replicate n x = case n <= 0 of
    True  -> []
    False -> x : replicate (n - 1) x

reverse :: [a] -> [a]
reverse = foldl (flip (:)) []

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

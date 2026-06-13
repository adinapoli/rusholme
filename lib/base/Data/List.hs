{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.List — pure list combinators.
--
-- Mirrors GHC's `base:Data.List`.  Imports from GHC.Base
-- (Bool/Int/Show, the comparison operators) and RHC.Prim is
-- transitive via GHC.Base.  No primops, no foreign decls.
module Data.List
    ( map, filter, (++), head, tail, null, length
    , foldr, foldl, concat, take, drop
    , reverse
    , sum, product, replicate
    ) where

import GHC.Base
import Data.Function

infixr 5 ++

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
head []     = error "Data.List.head: empty list"

tail :: [a] -> [a]
tail (x:xs) = xs
tail []     = error "Data.List.tail: empty list"

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

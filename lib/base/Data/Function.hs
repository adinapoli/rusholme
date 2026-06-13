{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.Function — basic function combinators.
--
-- Mirrors GHC's `base:Data.Function`.  Pure, foreign-free, primop-free
-- — sits at the bottom of `base` because every other module wants
-- `id`/`const`/`(.)`/`($)`.
module Data.Function
    ( id
    , const
    , flip
    , (.)
    , ($)
    ) where

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

($) :: (a -> b) -> a -> b
($) f x = f x

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
    , until
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

-- | Apply a function until the predicate holds.
--
-- Haskell 2010 puts this in the Prelude; it belongs here with the other
-- combinators because it needs nothing but function application.  The
-- wildcard alternative (rather than `False`) keeps the case trivially
-- exhaustive: `otherwise` lives in GHC.Base, above this module.
until :: (a -> Bool) -> (a -> a) -> a -> a
until p f x = case p x of
    True -> x
    _    -> until p f (f x)

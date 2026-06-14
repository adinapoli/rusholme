{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.Tuple — pair accessors and combinators.
--
-- Mirrors GHC's `base:Data.Tuple` for the 2-tuple subset.  Wider
-- tuples (3-tuple, 4-tuple, …) are not yet exported here because
-- Rusholme's tuple syntax currently produces only `(a, b)`.  When
-- larger tuples land, add the obvious analogues alongside.
--
-- Pure Haskell, no primops, no foreign decls.
module Data.Tuple
    ( fst
    , snd
    , swap
    , curry
    , uncurry
    ) where

fst :: (a, b) -> a
fst (x, _) = x

snd :: (a, b) -> b
snd (_, y) = y

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (x, y) = f x y

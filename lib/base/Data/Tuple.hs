{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.Tuple — pair accessors and combinators.
--
-- Mirrors GHC's `base:Data.Tuple` for the 2-tuple subset.  The
-- compiler now wires tuples of arity 3..7 (construction, pattern
-- matching, codegen — see #846), but GHC's `Data.Tuple` only exports
-- the pair combinators below, so we match that surface here.
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

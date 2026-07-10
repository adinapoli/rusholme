{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.Ord — comparison utilities and the `Down` newtype wrapper.
--
-- Mirrors GHC's `base:Data.Ord` for the subset we can express today.
-- `Down` is declared as `data` (not `newtype`) — Rusholme's parser
-- does not yet accept `newtype`.  Runtime representation is one node
-- deeper than GHC's; semantics match.
--
module Data.Ord
    ( comparing
    , clamp
    , Down(..)
    ) where

import GHC.Base

-- | Compare two values by a projection, e.g. @sortBy (comparing snd)@.
-- Mirrors GHC's @base:Data.Ord.comparing@.
comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing p x y = compare (p x) (p y)

clamp :: Ord a => (a, a) -> a -> a
clamp p x = case x < fst' p of
    True  -> fst' p
    False -> case x > snd' p of
        True  -> snd' p
        False -> x
  where
    fst' (a, _) = a
    snd' (_, b) = b

data Down a = Down a

instance Eq a => Eq (Down a) where
    (==) (Down x) (Down y) = x == y
    (/=) (Down x) (Down y) = x /= y

instance Ord a => Ord (Down a) where
    compare (Down x) (Down y) = compare y x
    (<)  (Down x) (Down y) = x > y
    (<=) (Down x) (Down y) = x >= y
    (>)  (Down x) (Down y) = x < y
    (>=) (Down x) (Down y) = x <= y

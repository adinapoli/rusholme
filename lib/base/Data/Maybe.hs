{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.Maybe — Maybe combinators.
--
-- Mirrors GHC's `base:Data.Maybe`.  `Maybe` itself lives in GHC.Base
-- (it's a wired-in compiler-magic type); this module adds the
-- consumer functions.
module Data.Maybe
    ( maybe
    , fromMaybe
    ) where

import GHC.Base

maybe :: b -> (a -> b) -> Maybe a -> b
maybe n f Nothing  = n
maybe n f (Just x) = f x

fromMaybe :: a -> Maybe a -> a
fromMaybe d Nothing  = d
fromMaybe d (Just x) = x

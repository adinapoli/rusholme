{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.Either — Either combinator.
--
-- Mirrors GHC's `base:Data.Either`.  `Either` itself lives in GHC.Base.
module Data.Either
    ( either
    ) where

import GHC.Base

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x)  = f x
either f g (Right y) = g y

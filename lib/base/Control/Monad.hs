{-# LANGUAGE NoImplicitPrelude #-}
-- | Control.Monad — the monad combinators from Haskell 2010 §9.1 that
-- Rusholme can express today.
--
-- Mirrors GHC's `base:Control.Monad` for this subset.  Like `Data.Char`
-- and `Data.Ord` this is *not* part of the implicit Prelude: GHC requires
-- an explicit `import Control.Monad`, and so do we.
--
-- Layer in the boot stack: imports GHC.Base (for the Functor/Applicative/
-- Monad hierarchy) and is imported by nothing below it.
--
module Control.Monad
    ( mapM_
    , forM_
    , sequence_
    , when
    , unless
    , void
    , foldM
    ) where

import GHC.Base

-- These combinators are written against `return`, not `pure`.  That is the
-- Haskell 2010 spelling (§9.1 predates the Applicative/Monad proposal), and
-- `pure` reached through a *dictionary parameter* is currently miscompiled
-- for a higher-kinded class declared in another module.
-- tracked in: https://github.com/adinapoli/rusholme/issues/940
--
-- `when`/`unless` additionally depend on the discarded branch's argument not
-- being evaluated; nested-application arguments are still forced eagerly.
-- tracked in: https://github.com/adinapoli/rusholme/issues/913

-- | Apply a monadic action to every element, discarding the results.
mapM_ :: Monad m => (a -> m b) -> [a] -> m ()
mapM_ _ []       = return ()
mapM_ f (x : xs) = f x >> mapM_ f xs

-- | `mapM_` with the arguments flipped, for a trailing `do` block.
forM_ :: Monad m => [a] -> (a -> m b) -> m ()
forM_ xs f = mapM_ f xs

-- | Run every action in sequence, discarding the results.
sequence_ :: Monad m => [m a] -> m ()
sequence_ []       = return ()
sequence_ (x : xs) = x >> sequence_ xs

-- | Run the action only when the condition holds.
when :: Monad m => Bool -> m () -> m ()
when p s = case p of
    True  -> s
    False -> return ()

-- | Run the action unless the condition holds.
unless :: Monad m => Bool -> m () -> m ()
unless p s = case p of
    True  -> return ()
    False -> s

-- | Discard the result of an action.
void :: Monad m => m a -> m ()
void m = m >> return ()

-- | Left-associative monadic fold.
foldM :: Monad m => (b -> a -> m b) -> b -> [a] -> m b
foldM _ z []       = return z
foldM f z (x : xs) = f z x >>= \z' -> foldM f z' xs

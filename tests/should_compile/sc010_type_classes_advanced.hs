-- GHC testsuite: type classes with functional dependencies and default methods
module Sc010TypeClassesAdvanced where

-- Class hierarchy
class Eq a => Ord' a where
    compare' :: a -> a -> Ordering
    lt :: a -> a -> Bool
    lt x y = compare' x y == LT
    gt :: a -> a -> Bool
    gt x y = compare' x y == GT
    lte :: a -> a -> Bool
    lte x y = compare' x y /= GT
    gte :: a -> a -> Bool
    gte x y = compare' x y /= LT

-- Class with kind constraint (simple form)
class Functor' f where
    fmap' :: (a -> b) -> f a -> f b

class Functor' f => Applicative' f where
    pure'  :: a -> f a
    ap     :: f (a -> b) -> f a -> f b

class Applicative' m => Monad' m where
    bind   :: m a -> (a -> m b) -> m b
    return' :: a -> m a
    return' = pure'

-- Instance with where clause
instance Functor' Maybe where
    fmap' _ Nothing  = Nothing
    fmap' f (Just x) = Just (f x)

instance Applicative' Maybe where
    pure' = Just
    ap Nothing  _ = Nothing
    ap _ Nothing  = Nothing
    ap (Just f) (Just x) = Just (f x)

instance Monad' Maybe where
    bind Nothing  _ = Nothing
    bind (Just x) f = f x

-- Real-world style: expression evaluator with type classes
module Sc042GhcRealWorld002 where

class Eval f where
    eval :: f a -> a

data Const a = Const a
data Add   f = Add (f Int) (f Int)
data Mul   f = Mul (f Int) (f Int)
data IfZ   f = IfZ (f Int) (f Int) (f Int)

instance Eval Const where
    eval (Const x) = x

-- Monoid-style accumulation
class Alg f a where
    algebra :: f a -> a

data Fix f = In (f (Fix f))

cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg (In f) = alg (fmap (cata alg) f)

-- Annotated AST
data Annotated ann f a = Ann ann (f a)

getAnn :: Annotated ann f a -> ann
getAnn (Ann a _) = a

stripAnn :: Annotated ann f a -> f a
stripAnn (Ann _ f) = f

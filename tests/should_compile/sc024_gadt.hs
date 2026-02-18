-- GHC testsuite: GADT syntax
module Sc024Gadt where

-- Classic GADT expression
data Expr a where
    LitI  :: Int  -> Expr Int
    LitB  :: Bool -> Expr Bool
    Add   :: Expr Int  -> Expr Int  -> Expr Int
    Mul   :: Expr Int  -> Expr Int  -> Expr Int
    Eq    :: Eq a => Expr a -> Expr a -> Expr Bool
    If    :: Expr Bool -> Expr a -> Expr a -> Expr a

-- Phantom type GADT
data Proxy a where
    Proxy :: Proxy a

-- GADT with existential
data Showable where
    MkShowable :: Show a => a -> Showable

-- GADT with constraints on constructor
data SafeList a (n :: Nat) where
    Nil  :: SafeList a Zero
    Cons :: a -> SafeList a n -> SafeList a (Succ n)

data Nat = Zero | Succ Nat

-- GADT with multiple type variables
data Vec a b where
    VNil  :: Vec a ()
    VCons :: a -> Vec a b -> Vec a (a, b)

-- Eval for the expression GADT
eval :: Expr a -> a
eval (LitI n)   = n
eval (LitB b)   = b
eval (Add x y)  = eval x + eval y
eval (Mul x y)  = eval x * eval y
eval (Eq  x y)  = eval x == eval y
eval (If c t e) = if eval c then eval t else eval e

-- TestPrelude: Minimal Prelude for e2e testing without dependencies on
-- the full Prelude (M2 work tracked in #462). This module provides:
--   - Peano natural numbers
--   - Inductive lists
--   - Inductive pairs
--   - Basic FP combinators

module TestPrelude where

-- ────────────────────────────────────────────────────────────────────────
-- Peano Natural Numbers
-- ────────────────────────────────────────────────────────────────────────

data Nat = Zero | Succ Nat

natAdd :: Nat -> Nat -> Nat
natAdd Zero n = n
natAdd (Succ m) n = Succ (natAdd m n)

natMul :: Nat -> Nat -> Nat
natMul Zero _ = Zero
natMul (Succ m) n = natAdd n (natMul m n)

-- ────────────────────────────────────────────────────────────────────────
-- Inductive List
-- ────────────────────────────────────────────────────────────────────────

data List a = Nil | Cons a (List a)

listLength :: List a -> Nat
listLength Nil = Zero
listLength (Cons _ xs) = Succ (listLength xs)

listAppend :: List a -> List a -> List a
listAppend Nil ys = ys
listAppend (Cons x xs) ys = Cons x (listAppend xs ys)

-- NOTE: listReverse is intentionally omitted because nested where clauses
-- don't work correctly in Rusholme yet (variable scoping issue). This is a
-- known bug tracked separately.

-- ────────────────────────────────────────────────────────────────────────
-- Inductive Pairs
-- ────────────────────────────────────────────────────────────────────────

data Pair a b = Pair a b

pairFst :: Pair a b -> a
pairFst (Pair x _) = x

pairSnd :: Pair a b -> b
pairSnd (Pair _ y) = y

-- ────────────────────────────────────────────────────────────────────────
-- Basic FP Combinators
-- ────────────────────────────────────────────────────────────────────────

identity :: a -> a
identity x = x

compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

const :: a -> b -> a
const x _ = x

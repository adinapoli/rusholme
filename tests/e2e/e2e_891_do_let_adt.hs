-- e2e: do-block `let`-bound ADT values used later in the block (#891).
--
-- `inferLetDecl` (do-`LetStmt` path) pre-bound FunBind binders only in
-- the scoped env, never in `local_binders` — so any later *use* of the
-- binder panicked the desugarer's `.Var` arm ("Variable not found in
-- type definitions").  The `.Let` expression arm always registered its
-- binders; this exercises the do-statement path.
--
-- Covers: case-scrutinising a do-let ADT value, passing it to a
-- function, do-let Double-field ADT (the #884 find), a do-let helper
-- function used at two call sites, and chained do-lets referencing
-- earlier ones.
module Main where

data P = P Int Int

data V = V Double Double

sumP :: P -> Int
sumP (P a b) = a + b

main :: IO ()
main = do
  let p = P 1 2
  case p of
    P a b -> print (a + b)
  print (sumP p)
  let v = V 1.5 2.5
  case v of
    V x y -> print (x + y)
  let double n = n + n
  print (double 21)
  print (double 100)
  let q = P (sumP p) 10
  print (sumP q)

-- e2e_010: Lazy let bindings
--
-- Tests that let-bound variables with divergent RHS are not evaluated
-- when the body does not use them (call-by-need semantics).
-- Without lazy let, `loop` would be eagerly evaluated, causing an
-- infinite loop / stack overflow.

data Nat = Zero | Succ Nat

loop :: Nat -> Nat
loop x = loop x

main = let unused = loop Zero
       in putStrLn "ok"

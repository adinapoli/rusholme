-- Test 009: Lazy evaluation prevents infinite recursion
-- Tests that constructor arguments are not eagerly evaluated.
-- The 'double' function has a bug (recurses on x instead of decrementing),
-- causing infinite recursion.  But since Haskell is lazy, the inner thunk
-- is never forced because showP only matches one level deep.

data Nat = Zero | Succ Nat

double :: Nat -> Nat
double Zero = Zero
double (Succ x) = Succ (Succ (double x))

showP :: Nat -> String
showP Zero = "Zero"
showP (Succ _) = "Succ _"

main = putStrLn (showP (double (Succ Zero)))

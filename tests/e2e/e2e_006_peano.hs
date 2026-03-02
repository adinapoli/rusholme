-- Test 006: Peano numbers with arithmetic
-- Tests inductive data types with recursive functions

data Nat = Zero | Succ Nat

main = putStrLn (natToString (add (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))))

-- Convert Nat to decimal string (simplified: only handles 0-9)
natToString :: Nat -> String
natToString (Zero)       = "0"
natToString (Succ (Zero))   = "1"
natToString (Succ (Succ (Zero))) = "2"
natToString (Succ (Succ (Succ (Zero)))) = "3"
natToString (Succ (Succ (Succ (Succ (Zero))))) = "4"
natToString (Succ (Succ (Succ (Succ (Succ (Zero)))))) = "5"
natToString _ = "many"

-- Addition on Peano numbers: 2 + 3 = 5
add :: Nat -> Nat -> Nat
add (Zero)     n = n
add (Succ m) n = Succ (add m n)

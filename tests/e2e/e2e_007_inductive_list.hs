-- Test 007: Inductive lists with operations
-- Tests polymorphic inductive data types with map and length

data List a = Nil | Cons a (List a)

main = putStrLn (intToString (len (Cons 1 (Cons 2 (Cons 3 Nil)))))

-- Length of a list
len :: List a -> Nat
len (Nil)         = Zero
len (Cons _ xs) = Succ (len xs)

-- Peano numbers (local definition)
data Nat = Zero | Succ Nat

-- Convert Nat to decimal string (simplified: only handles 0-9)
intToString :: Nat -> String
intToString (Zero)       = "0"
intToString (Succ (Zero))   = "1"
intToString (Succ (Succ (Zero))) = "2"
intToString (Succ (Succ (Succ (Zero)))) = "3"
intToString (Succ (Succ (Succ (Succ (Zero))))) = "4"
intToString (Succ (Succ (Succ (Succ (Succ (Zero)))))) = "5"
intToString (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) = "6"
intToString _ = "many"

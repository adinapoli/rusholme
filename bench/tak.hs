-- Bench: extreme deep 3-way recursion (Takeuchi function).
--
-- The Takeuchi function tak(x,y,z) makes three recursive calls
-- per invocation when y < x, creating an enormous call tree.
-- Unlike fib (2-way branching) or sum_to (linear), this is
-- 3-way branching with deeply nested recursive calls that
-- themselves expand. Pure compute, no heap allocation. Isolates
-- the cost of deep call stack management and codegen for
-- non-trivial call patterns.

tak :: Int -> Int -> Int -> Int
tak x y z = if y < x
  then tak (tak (x - 1) y z) (tak (y - 1) z x) (tak (z - 1) x y)
  else z

main = putStrLn (show (tak 18 12 6))
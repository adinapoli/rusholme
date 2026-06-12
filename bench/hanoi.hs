-- Bench: multi-argument branching recursion (Towers of Hanoi).
--
-- Inspired by the classic Towers of Hanoi problem. Computes a
-- checksum of all moves: each move contributes (src + dst) to
-- the total. Unlike fib (2-way with 1 Int arg) or tak (3-way
-- with 3 Int args), this is 2-way branching with 4 arguments
-- (disk count + 3 pegs as Ints). The different argument count
-- exercises a different calling-convention surface. Also tests
-- non-tail recursion where neither recursive call is in tail
-- position (unlike fib where the + forces left-to-right
-- evaluation but both calls are non-tail).

-- Pegs represented as Ints: 1, 2, 3.
-- Checksum: sum of (src + dst) for every move.
hanoi :: Int -> Int -> Int -> Int -> Int
hanoi 0 _ _ _ = 0
hanoi n src dst aux =
  hanoi (n - 1) src aux dst + (src + dst) + hanoi (n - 1) aux dst src

main = putStrLn (show (hanoi 25 1 3 2))
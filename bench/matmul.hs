-- Bench: dense matrix-matrix multiplication (nested loops).
--
-- Inspired by the Benchmarks Game "spectral-norm" benchmark but
-- tests matrix-matrix multiply (not matrix-vector). Uses a flat
-- list representation for an N×N matrix in row-major order.
-- The inner loop computes dot products via index arithmetic.
-- Stresses triple-nested recursion with accumulator passing.
-- Different from spectral_norm which uses fixed-point arithmetic
-- with a sparse pattern.

data List = Nil | Cons Int List

-- Get element at 0-based index (returns 0 for out-of-bounds).
get :: Int -> List -> Int
get _ Nil = 0
get 0 (Cons x _) = x
get n (Cons _ xs) = get (n - 1) xs

-- Compute C[i][j] = sum_{k=0}^{n-1} A[i*n+k] * B[k*n+j]
dotProd :: Int -> Int -> Int -> Int -> Int -> List -> List -> Int
dotProd acc k i j n a b =
  if k >= n then acc
  else dotProd (acc + get (i * n + k) a * get (k * n + j) b) (k + 1) i j n a b

-- Build result matrix row by row.
-- i from 0 to n-1, j from 0 to n-1 (builds in order).
mulRows :: Int -> Int -> Int -> List -> List -> List
mulRows i j n a b =
  if i >= n then Nil
  else if j >= n then mulRows (i + 1) 0 n a b
  else Cons (dotProd 0 0 i j n a b) (mulRows i (j + 1) n a b)

-- Build a test matrix: M[i][j] = (i + j + 1) mod 10 + 1
buildMatrix :: Int -> Int -> Int -> List
buildMatrix i j n =
  if i >= n then Nil
  else if j >= n then buildMatrix (i + 1) 0 n
  else Cons (mymod (i + j + 1) 10 + 1) (buildMatrix i (j + 1) n)

-- Sum all elements of a list.
sumList :: List -> Int -> Int
sumList Nil acc = acc
sumList (Cons x xs) acc = sumList xs (acc + x)

-- Integer modulus (for positive a, b).
mymod :: Int -> Int -> Int
mymod a b = if a < b then a else mymod (a - b) b

-- Run matmul n times and accumulate checksum.
runMul :: Int -> Int -> List -> List -> Int -> Int
runMul 0 _ _ _ acc = acc
runMul iters n a b acc =
  let c = mulRows 0 0 n a b
  in runMul (iters - 1) n a b (acc + sumList c 0)

main = putStrLn (show (runMul 100 12 (buildMatrix 0 0 12) (buildMatrix 0 0 12) 0))
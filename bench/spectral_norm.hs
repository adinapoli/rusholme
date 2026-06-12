-- Bench: matrix-style nested loop computation (spectral-norm).
--
-- Inspired by the Benchmarks Game "spectral-norm" benchmark.
-- Computes the 1-norm of A * (A^T * v) where A_ij = 1 / (i + j + 1),
-- using repeated matrix-vector multiplication. Stresses nested
-- recursive loops and floating-point-like integer arithmetic.
-- We use a fixed-point representation (scaled by 2^12 = 4096)
-- to avoid needing Float/Double.

-- A_ij = 4096 / (i + j + 1) in fixed-point.
aElem :: Int -> Int -> Int
aElem i j = fpDiv 4096 (i + j + 1)

-- Integer division.
fpDiv :: Int -> Int -> Int
fpDiv a b = if b == 0 then 0 else fpDivHelper (if a < 0 then -a else a) (if b < 0 then -b else b) 0

fpDivHelper :: Int -> Int -> Int -> Int
fpDivHelper a b q = if a < b then q else fpDivHelper (a - b) b (q + 1)

-- Multiply A by vector v: (Av)_i = sum_j A_ij * v_j / 4096
multAv :: Int -> Int -> Int -> Int
multAv i j acc = if j >= 20 then acc
                else multAv i (j + 1) (acc + aElem i j * vec j `fpDiv` 4096)

-- Multiply A^T by vector v: (A^T v)_j = sum_i A_ij * v_i / 4096
multAtv :: Int -> Int -> Int -> Int
multAtv j i acc = if i >= 20 then acc
                 else multAtv j (i + 1) (acc + aElem i j * vec i `fpDiv` 4096)

-- The vector we're iterating on (all-1s scaled to fixed-point).
vec :: Int -> Int
vec i = 4096

-- Compute 1-norm of the result.
computeNorm :: Int -> Int -> Int
computeNorm i acc = if i >= 20 then acc
                   else computeNorm (i + 1) (acc + myabs (multAtv i 0 0))

myabs :: Int -> Int
myabs x = if x < 0 then -x else x

main = putStrLn (show (computeNorm 0 0))
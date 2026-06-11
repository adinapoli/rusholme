-- Bench: tight inner loop with integer arithmetic (compute-bound).
--
-- Inspired by the Benchmarks Game "mandelbrot" benchmark's
-- inner escape loop. For each of a grid of points, iterates
-- z = z² + c until |z| > 2 or max iterations. Pure Int arithmetic
-- using fixed-point representation (scaled by 2^16). Stresses
-- integer multiplication, addition, and loop control with no
-- heap allocation.

-- Mandelbrot iteration: returns 1 if the point escaped within
-- maxIter iterations, 0 otherwise. Coordinates are fixed-point
-- with 2^16 = 65536 as the unit.
mandel :: Int -> Int -> Int -> Int -> Int -> Int
mandel zr zi cr ci maxIter =
  if maxIter == 0 then 0
  else if zr * zr + zi * zi > 268435456 then 0  -- 4 * 65536^2
  else mandel (zr * zr `intDiv` 65536 - zi * zi `intDiv` 65536 + cr)
              (2 * zr * zi `intDiv` 65536 + ci)
              cr ci (maxIter - 1)

-- Integer division (truncating towards zero).
intDiv :: Int -> Int -> Int
intDiv a b = if b == 0 then 0 else intDivHelper (if a < 0 then -a else a) (if b < 0 then -b else b) 0

intDivHelper :: Int -> Int -> Int -> Int
intDivHelper a b q = if a < b then q else intDivHelper (a - b) b (q + 1)

-- Count how many of a 30x30 grid escape.
countEscapes :: Int -> Int -> Int
countEscapes row col =
  if row >= 30 then 0
  else if col >= 30 then countEscapes (row + 1) 0
  else countEscapes row (col + 1) + mandel 0 0 (col * 2184 - 26214) (row * 2184 - 26214) 50

main = putStrLn (show (countEscapes 0 0))
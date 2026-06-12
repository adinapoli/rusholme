-- Bench: backtracking search with pruning (N-Queens).
--
-- Counts the number of valid N-Queens placements. Unlike any
-- existing benchmark, this involves backtracking (early return
-- from recursion), building and discarding partial solutions,
-- and data-dependent control flow. Tests the runtime's ability
-- to efficiently handle non-uniform iteration where most
-- branches are pruned early.

data List = Nil | Cons Int List

-- Check if placing a queen at column c is safe given existing
-- placements. board stores column positions (newest row first).
-- offset is the row distance from the current row (starts at 1).
-- Returns 1 if safe, 0 if conflict.
noConflict :: Int -> List -> Int -> Int
noConflict _ Nil _ = 1
noConflict c (Cons q rest) offset =
  if c == q then 0
  else if c - offset == q then 0
  else if c + offset == q then 0
  else noConflict c rest (offset + 1)

-- Try placing a queen in columns [1..col] of the given row.
-- If safe, recurse to next row and try remaining columns.
tryColumns :: Int -> Int -> Int -> List -> Int
tryColumns 0 _ _ _ = 0
tryColumns col depth n board =
  if noConflict col board 1 == 1
  then tryColumns (col - 1) depth n board + solve (depth + 1) n (Cons col board)
  else tryColumns (col - 1) depth n board

-- Count valid placements starting from row depth.
solve :: Int -> Int -> List -> Int
solve depth n board =
  if depth == n then 1
  else tryColumns n depth n board

main = putStrLn (show (solve 0 12 Nil))
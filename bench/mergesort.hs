-- Bench: merge sort (comparison + allocation heavy).
--
-- Inspired by the Benchmarks Game benchmarks that require sorting.
-- Implements a simple merge sort on a custom list type. Exercises
-- comparison, recursive splitting, merging, and allocation of a
-- new sorted list. Good for measuring the overhead of creating
-- and destroying intermediate lists.

data List = Nil | Cons Int List

-- Merge two sorted lists.
merge :: List -> List -> List
merge Nil ys = ys
merge xs Nil = xs
merge (Cons x xs) (Cons y ys) =
  if x <= y then Cons x (merge xs (Cons y ys))
  else Cons y (merge (Cons x xs) ys)

-- Count elements.
mylen :: List -> Int -> Int
mylen Nil acc = acc
mylen (Cons _ xs) acc = mylen xs (acc + 1)

-- Take first n elements.
mytake :: Int -> List -> List
mytake 0 _ = Nil
mytake _ Nil = Nil
mytake n (Cons x xs) = Cons x (mytake (n - 1) xs)

-- Drop first n elements.
mydrop :: Int -> List -> List
mydrop 0 xs = xs
mydrop _ Nil = Nil
mydrop n (Cons _ xs) = mydrop (n - 1) xs

-- Merge sort.
sort :: List -> List
sort Nil = Nil
sort (Cons x Nil) = Cons x Nil
sort xs =
  let n = mylen xs 0
      half = mydiv n 2
  in merge (sort (mytake half xs)) (sort (mydrop half xs))

-- Integer division.
mydiv :: Int -> Int -> Int
mydiv a b = if b == 0 then 0 else mydivHelper (if a < 0 then -a else a) (if b < 0 then -b else b) 0

mydivHelper :: Int -> Int -> Int -> Int
mydivHelper a b q = if a < b then q else mydivHelper (a - b) b (q + 1)

-- Build a list of n elements (decreasing values).
buildList :: Int -> List
buildList 0 = Nil
buildList n = Cons n (buildList (n - 1))

-- Check if list is sorted (returns 1 if sorted, 0 otherwise).
isSorted :: List -> Int
isSorted Nil = 1
isSorted (Cons _ Nil) = 1
isSorted (Cons x rest) = isSortedFrom x rest

isSortedFrom :: Int -> List -> Int
isSortedFrom _ Nil = 1
isSortedFrom prev (Cons x xs) = if prev <= x then isSortedFrom x xs else 0

main = putStrLn (show (isSorted (sort (buildList 500))))
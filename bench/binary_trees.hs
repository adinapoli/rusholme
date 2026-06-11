-- Bench: allocation-heavy tree create + destroy (GC stress).
--
-- Inspired by the Benchmarks Game "binary-trees" benchmark.
-- Builds a balanced binary tree of depth N, then sums its leaf
-- values. Exercises short-lived allocation, pointer-chasing, and
-- the GC's ability to reclaim a deep, wide tree. Unlike tree_sum
-- (which builds once and folds), this allocates many small trees
-- in a loop, stressing the alloc/GC cycle more heavily.

data Tree = Leaf Int | Node Tree Tree

buildTree :: Int -> Tree
buildTree 0 = Leaf 1
buildTree n = Node (buildTree (n - 1)) (buildTree (n - 1))

sumTree :: Tree -> Int
sumTree (Leaf v)   = v
sumTree (Node l r)  = sumTree l + sumTree r

loop :: Int -> Int -> Int
loop acc 0 = acc
loop acc n = loop (acc + sumTree (buildTree 14)) (n - 1)

main = putStrLn (show (loop 0 3))
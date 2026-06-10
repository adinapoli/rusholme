-- Bench: deeper tree allocation + traversal.
--
-- Builds a balanced binary tree, then folds it. Per node carries
-- two pointer fields, so the GC tracer follows 2x more edges per
-- byte than `build_list`. Useful for separating "alloc rate" from
-- "pointer-chasing rate" in the bench results.

data Tree = Leaf | Node Int Tree Tree

build :: Int -> Int -> Tree
build _ 0 = Leaf
build seed depth =
  let n = seed + depth
  in Node n (build (n + 1) (depth - 1)) (build (n + 2) (depth - 1))

sumTree :: Tree -> Int
sumTree Leaf = 0
sumTree (Node v l r) = v + sumTree l + sumTree r

main = putStrLn (show (sumTree (build 1 14)))

-- Bench: nested data structures (rose tree traversal).
--
-- Inspired by the Benchmarks Game "pidigits" spigot algorithm's
-- use of nested state. Builds a rose tree (each node has a list
-- of children) and sums all node values. Stresses allocation of
-- nodes with variable-arity children and traversal patterns that
-- are less regular than binary trees.

data Rose = RoseNode Int Forest
data Forest = NilForest | ConsForest Rose Forest

-- Build a rose tree of given depth and branching factor.
buildRose :: Int -> Int -> Int -> Rose
buildRose _ 0 seed = RoseNode seed NilForest
buildRose bf depth seed =
  let children = buildForest bf (depth - 1) (seed + 1)
  in RoseNode seed children

buildForest :: Int -> Int -> Int -> Forest
buildForest 0 _ _ = NilForest
buildForest bf depth seed =
  ConsForest (buildRose bf depth seed) (buildForest (bf - 1) depth (seed + bf))

-- Sum all values in a rose tree.
sumRose :: Rose -> Int
sumRose (RoseNode v children) = v + sumForest children

sumForest :: Forest -> Int
sumForest NilForest = 0
sumForest (ConsForest r rest) = sumRose r + sumForest rest

main = putStrLn (show (sumRose (buildRose 3 8 0)))
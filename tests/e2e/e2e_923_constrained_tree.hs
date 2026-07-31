module Main where

-- Regression test for #923: a constructor with two parenthesised fields
-- (`Node (Tree a) a (Tree a)`) followed by a declaration carrying an
-- unparenthesised class context (`ins :: Ord a => …`).
--
-- The bare-context lookahead used to walk out of the constructor's field list
-- and find the *signature's* `=>`, concluding that the field list was a class
-- context.  The `data` declaration then failed to parse and was dropped by
-- error recovery, so the visible symptom was a cascade of "variable not in
-- scope: `Leaf`/`Node`" from the renamer.
--
-- This is the canonical Ord-constrained binary tree — the shape every
-- Data.Map/Data.Set/sort implementation has — so it stays as an end-to-end
-- guard rather than only a parser unit test.

data Tree a = Leaf | Node (Tree a) a (Tree a)

ins :: Ord a => a -> Tree a -> Tree a
ins x Leaf = Node Leaf x Leaf
ins x t@(Node l v r)
  | x < v = Node (ins x l) v r
  | x > v = Node l v (ins x r)
  | otherwise = t

toList :: Tree a -> [a]
toList Leaf = []
toList (Node l v r) = toList l ++ [v] ++ toList r

depth :: Tree a -> Int
depth Leaf = 0
depth (Node l _ r) = 1 + max (depth l) (depth r)

main :: IO ()
main = do
  print (toList (foldr ins Leaf [5, 3, 8, 1 :: Int]))
  -- Duplicates hit the `otherwise` guard and are dropped.
  print (toList (foldr ins Leaf [2, 2, 1 :: Int]))
  print (depth (foldr ins Leaf [3, 2, 1 :: Int]))

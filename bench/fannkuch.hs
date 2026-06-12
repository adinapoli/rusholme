-- Bench: prefix reversal counting (fannkuch-inspired).
--
-- Inspired by the Benchmarks Game "fannkuch-redux" benchmark.
-- Repeatedly reverses prefixes of a list to bring element 1 to
-- the front, counting how many steps it takes. Stresses pattern
-- matching, list manipulation, and recursive calls. Tests the
-- same inner loop as fannkuch-redux without needing full
-- permutation generation.

data List = Nil | Cons Int List

-- Reverse the first k elements of a list.
revFirst :: Int -> List -> List -> List
revFirst 0 acc rest = appendRev acc rest
revFirst _ acc Nil = appendRev acc Nil
revFirst n acc (Cons x xs) = revFirst (n - 1) (Cons x acc) xs

appendRev :: List -> List -> List
appendRev Nil rest = rest
appendRev (Cons x xs) rest = Cons x (appendRev xs rest)

-- Count flips: how many prefix reversals until 1 is at the front.
countFlips :: List -> Int
countFlips Nil = 0
countFlips (Cons 1 _) = 0
countFlips (Cons k xs) = 1 + countFlips (revFirst k Nil (Cons k xs))

-- Build a "worst case" permutation: [n, n-1, ..., 2, 1]
buildWorst :: Int -> List -> List
buildWorst 0 acc = acc
buildWorst n acc = buildWorst (n - 1) (Cons n acc)

-- Run the flip counter many times to stress the inner loop.
loop :: Int -> Int -> Int
loop acc 0 = acc
loop acc n = loop (acc + countFlips (buildWorst 10 Nil)) (n - 1)

main = putStrLn (show (loop 0 5000))
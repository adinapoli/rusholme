-- e2e_847: Lazy let/where pattern bindings desugar to selector bindings.
--
-- Regression test for #847: `let (a, b) = e` previously produced
-- undefined-reference linker errors because the bound variables were
-- never desugared into Core bindings.  Per Haskell 2010 §3.12 a pattern
-- binding desugars into a binding of the RHS plus one lazy selector per
-- bound variable, each re-matching the shared RHS thunk.

data Pair = Pair Int Int

-- 2-tuple in `let`
swapDiff :: (Int, Int) -> Int
swapDiff p =
  let (x, y) = p
  in x - y

-- 2-tuple in a `where` clause
fromWhere :: Int
fromWhere = a + b
  where (a, b) = (100, 7)

-- 3-tuple
tripleSum :: Int
tripleSum =
  let (a, b, c) = (1, 2, 3)
  in a + b + c

-- nested tuple pattern
nested :: Int
nested =
  let (a, (b, c)) = (10, (20, 30))
  in a + b + c

-- constructor pattern
fromPair :: Int
fromPair =
  let Pair p q = Pair 4 9
  in p * q

-- a non-terminating Int used to probe laziness of the selectors
loop :: Int -> Int
loop x = loop x

-- The second component diverges; a lazy selector must never force it.
lazyFst :: Int
lazyFst =
  let (a, _) = (42, loop 0)
  in a

main :: IO ()
main = do
  print (swapDiff (10, 20))  -- -10
  print fromWhere            -- 107
  print tripleSum            -- 6
  print nested               -- 60
  print fromPair             -- 36
  print lazyFst              -- 42

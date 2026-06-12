-- Bench: hash-table-like frequency counting (Map-like operations).
--
-- Inspired by the Benchmarks Game "k-nucleotide" benchmark.
-- Counts the frequency of small keys in a stream using a simple
-- association list (since Rusholme doesn't have Data.Map). Stresses
-- comparison, lookup, and update of a growing key-value store.

data Map = Empty | Node Int Int Map Map

-- Lookup: returns 0 if key not found. Named lookupTree to avoid
-- clashing with Prelude.lookup (GHC rejects the ambiguous use).
lookupTree :: Int -> Map -> Int
lookupTree _ Empty = 0
lookupTree k (Node k2 v left right) =
  if k < k2 then lookupTree k left
  else if k > k2 then lookupTree k right
  else v

-- Insert/update: increments value if key exists, inserts with 1 otherwise.
insert :: Int -> Map -> Map
insert k Empty = Node k 1 Empty Empty
insert k (Node k2 v left right) =
  if k < k2 then Node k2 v (insert k left) right
  else if k > k2 then Node k2 v left (insert k right)
  else Node k2 (v + 1) left right

-- Build a map from a sequence of keys.
buildMap :: Int -> Int -> Map
buildMap 0 _ = Empty
buildMap n seed = insert (keyGen seed) (buildMap (n - 1) (seed + 1))

-- Deterministic key generator: produces keys in [0..99].
keyGen :: Int -> Int
keyGen n = if n < 100 then n else keyGen (n - 100)

-- Sum all values in the map.
sumValues :: Map -> Int
sumValues Empty = 0
sumValues (Node _ v left right) = v + sumValues left + sumValues right

-- Sum the lookups of every key in [0..n-1], exercising the lookup
-- path (buildMap alone only exercises insert).
sumLookups :: Int -> Map -> Int
sumLookups 0 _ = 0
sumLookups n m = lookupTree (n - 1) m + sumLookups (n - 1) m

main =
  let m = buildMap 5000 0
  in putStrLn (show (sumValues m + sumLookups 100 m))
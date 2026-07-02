-- e2e: `Double` values stored in ADT constructor fields (#884).
--
-- A `Double` is a boxed `Float` node; constructor field slots are
-- uniformly boxed (pointer or tagged immediate), so a `Double` field
-- stores the node pointer and pattern-matching loads it back as a
-- pointer — never a raw f64 bit-pattern.
--
-- Covers: construct + match through a function boundary, arithmetic on
-- matched fields, reconstruction from matched fields (addV), mixed
-- Int/Double fields in one constructor, `Double` inside `Maybe`, a list
-- of Double-carrying values, and laziness (an unevaluated field thunk
-- forced after the match).
--
-- Output diffed against a fixed sidecar generated from GHC.
module Main where

data V = V Double Double

data Mixed = Mixed Int Double

mkV :: Double -> Double -> V
mkV x y = V x y

mag2 :: V -> Double
mag2 (V x y) = x * x + y * y

addV :: V -> V -> V
addV (V a b) (V c d) = V (a + c) (b + d)

-- Int and Double fields side by side in one node: the Int is a tagged
-- immediate, the Double a Float-node pointer — both live in plain
-- boxed slots.
describeMixed :: Mixed -> Double
describeMixed (Mixed n d) = case n > 0 of
  True  -> d * 2.0
  False -> d

fromJustV :: Maybe Double -> Double
fromJustV (Just d) = d
fromJustV Nothing  = 0.0

sumMags :: [V] -> Double
sumMags []     = 0.0
sumMags (v:vs) = mag2 v + sumMags vs

main :: IO ()
main = do
  print (mag2 (mkV 1.5 2.5))
  print (mag2 (addV (mkV 1.0 2.0) (mkV 3.0 4.0)))
  print (describeMixed (Mixed 4 2.5))
  print (fromJustV (Just 6.25))
  print (fromJustV Nothing)
  print (sumMags [mkV 1.0 0.0, mkV 0.0 2.0, mkV 3.0 4.0])
  -- Lazy field: the thunk (0.5 + 0.25) is stored unevaluated and
  -- forced only when the matched field is used.
  case V (0.5 + 0.25) 100.0 of
    V a b -> print (a * b)

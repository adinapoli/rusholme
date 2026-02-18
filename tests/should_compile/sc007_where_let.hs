-- GHC testsuite: where clauses and let expressions
module Sc007WhereLet where

-- where clause
circleArea :: Double -> Double
circleArea r = pi' * r * r
  where
    pi' = 3.14159265358979

-- Nested where
quadratic :: Double -> Double -> Double -> (Double, Double)
quadratic a b c = (x1, x2)
  where
    x1 = (-b + d) / (2 * a)
    x2 = (-b - d) / (2 * a)
    d  = sqrt discriminant
    discriminant = b * b - 4 * a * c

-- let expression
letExpr :: Int -> Int
letExpr n =
    let x = n + 1
        y = x * 2
        z = y - n
    in x + y + z

-- let in do
action :: IO ()
action = do
    let x = 42
        msg = "hello"
    return ()

-- where with type sigs
compute :: Int -> Int
compute n = go n 0
  where
    go :: Int -> Int -> Int
    go 0 acc = acc
    go k acc = go (k - 1) (acc + k)

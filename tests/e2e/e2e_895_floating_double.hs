-- e2e: `Floating` class + `instance Floating Double` (#895).
-- Transcendental primops lowered as libm calls (`double @sqrt(double)`
-- etc., linked with `-lm`); results re-boxed as Float nodes.
--
-- Values chosen to be bit-stable across libm implementations (exact
-- results or correctly-rounded well-known constants), so the sidecar
-- matches GHC on any platform.  `asinh`/`acosh`/`atanh` are deferred to
-- superclass-context support (#889).
module Main where
main :: IO ()
main = do
  print (sqrt 4.0)
  print (sqrt 2.0)
  print (2.0 ** 10.0)
  print (exp 0.0)
  print (log 1.0)
  print (logBase 2.0 8.0)
  print (pi :: Double)
  print (sin 0.0)
  print (cos 0.0)
  print (asin 1.0)
  print (tanh 0.0)
  print (cosh 0.0)
  print (sqrt (3.0 * 3.0 + 4.0 * 4.0))

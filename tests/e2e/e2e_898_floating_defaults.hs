-- e2e: H2010 default bodies for asinh/acosh/atanh (#898).
--
-- These class defaults live in lib/ghc-internal/GHC/Base.hs and call
-- Num/Fractional/Floating methods over the class type variable from inside
-- a default method body, so they exercise the superclass-dictionary
-- threading of #898 through the real Prelude.  GHC's `Floating Double`
-- instance overrides all three with libm calls, which can differ from the
-- log-based defaults in the last ulp — so the checks compare against
-- reference values with a tolerance instead of printing raw doubles.
module Main where

close :: Double -> Double -> Bool
close a b = abs (a - b) < 1.0e-12

main :: IO ()
main = do
  -- Exact cases: identical under both the defaults and libm.
  print (asinh 0.0)
  print (acosh 1.0)
  print (atanh 0.0)
  -- Tolerance checks against libm reference values.
  print (close (asinh 0.5) 0.48121182505960347)
  print (close (asinh 1.0) 0.881373587019543)
  print (close (asinh 2.0) 1.4436354751788103)
  print (close (asinh 10.0) 2.99822295029797)
  print (close (acosh 1.5) 0.9624236501192069)
  print (close (acosh 2.0) 1.3169578969248168)
  print (close (acosh 10.0) 2.993222846126381)
  print (close (atanh 0.5) 0.5493061443340549)
  print (close (atanh 0.9) 1.4722194895832204)
  print (close (atanh (negate 0.5)) (negate 0.5493061443340549))
  -- Identities: sinh (asinh x) == x etc., up to rounding.
  print (close (sinh (asinh 3.75)) 3.75)
  print (close (cosh (acosh 4.25)) 4.25)
  print (close (tanh (atanh 0.75)) 0.75)

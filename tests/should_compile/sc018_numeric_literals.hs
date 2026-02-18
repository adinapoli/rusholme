-- GHC testsuite: numeric literals (decimal, hex, octal, float)
module Sc018NumericLiterals where

decimal :: Int
decimal = 42

negative :: Int
negative = -17

hexadecimal :: Int
hexadecimal = 0xFF

hexLower :: Int
hexLower = 0xff

octal :: Int
octal = 0o77

float1 :: Double
float1 = 3.14

float2 :: Double
float2 = 2.718e0

float3 :: Double
float3 = 1.0e10

float4 :: Double
float4 = 1.5e-3

float5 :: Double
float5 = 0.5E2

-- Large numbers
big :: Integer
big = 123456789012345678901234567890

-- Negative float
negFloat :: Double
negFloat = -3.14

-- GHC testsuite: basic module header with export list
module Sc001ModuleHeader (
    -- * Types
    Foo(..),
    Bar,
    -- * Functions
    foo,
    bar,
    (+++)
) where

data Foo = MkFoo Int
data Bar = MkBar String

foo :: Foo -> Int
foo (MkFoo n) = n

bar :: Bar -> String
bar (MkBar s) = s

(+++) :: String -> String -> String
(+++) x y = x

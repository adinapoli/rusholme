-- Regression test for #543: Layout processor injects virtual tokens inside
-- parenthesized contexts. Per Haskell 2010 §2.7, layout rules should NOT
-- apply inside explicit delimiter pairs (parentheses, brackets).

module Sc049ExportListBlankLines (
    bar,
    baz,

    quux
) where

-- Export list with blank lines between items - should parse correctly
bar :: Int
bar = 1

baz :: String
baz = "hello"

quux :: Bool
quux = True
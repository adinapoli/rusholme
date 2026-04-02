-- sc052: (-) in module export list
-- Regression test for https://github.com/adinapoli/rusholme/issues/538
--
-- The `-` operator receives special lexer treatment (distinguishing prefix
-- negate from infix minus). This test ensures `(-)` is accepted in export
-- lists as per Haskell 2010 §5.2.

-- Minimal case: just (-)
module MinusExport ( (-) ) where

minus :: Int -> Int -> Int
minus x y = x - y

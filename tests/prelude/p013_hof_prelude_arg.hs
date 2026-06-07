-- Prelude regression: Prelude functions as higher-order arguments (#759).
--
-- xfail: passing a Prelude-defined function (odd, negate) as a HOF
-- argument segfaults at runtime — tracked in #764.  A user-defined
-- function with the same body works (see p005_list_basic.hs).
module Main where

main :: IO ()
main = do
    print (filter odd [1, 2, 3])
    print (map negate [1, 2, 3])

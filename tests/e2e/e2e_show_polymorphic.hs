-- e2e_show_polymorphic: Polymorphic Show instances
--
-- Tests the `Show [a]` instance with dictionary passing.
-- The nested list case `show [[4,5],[6]]` exercises `Show a => Show [a]`
-- where `a = [Int]`, requiring the instance to pass the `Show [Int]`
-- dictionary (which itself uses `Show Int`) — a genuine test of the
-- polymorphic dictionary-passing infrastructure.

module ShowPolymorphic where

main :: IO ()
main = do
    putStrLn (show [1, 2, 3])
    putStrLn (show [[4, 5], [6]])

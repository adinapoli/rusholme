-- Test 003: Do notation bug - Rusholme desugars do to Grin incorrectly
-- BUG: Do notation creates todo_do_1 but GRIN→LLVM can't resolve it
-- This is a known bug tracked in #464

main = do
  putStrLn "first"
  putStrLn "second"
  putStrLn "third"

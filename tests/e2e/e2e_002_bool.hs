-- Test 002: Inductive data types with multiple constructors
-- Simple Boolean-like type to test ADT parsing and pattern matching
-- NOTE: This test exposes a GRIN→LLVM codegen bug where function
-- names are mismatched between declaration and definition (showMyBool vs showMyBool.1)

data MyBool = MyFalse | MyTrue

main = putStrLn "true"

showMyBool :: MyBool -> String
showMyBool MyFalse = "false"
showMyBool MyTrue = "true"

-- Test 002: Inductive data types with multiple constructors
-- Uses standard Bool type (True/False) to test that user-defined types
-- can shadow Prelude built-in constructors without duplicate errors
-- NOTE: This test exposes a GRIN→LLVM codegen bug where function
-- names are mismatched between declaration and definition - tracked in #463

data MyBool = False | True

main = putStrLn "true"

showMyBool :: MyBool -> String
showMyBool False = "false"
showMyBool True = "true"

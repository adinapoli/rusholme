-- Test 005: Nested data types
-- Tests nested data constructor handling

data Inner = I1 | I2
data Outer = OInner Inner | OString String

main = putStrLn (showOuter (OString "nested"))

showOuter :: Outer -> String
showOuter (OInner I1) = "inner-1"
showOuter (OInner I2) = "inner-2"
showOuter (OString s) = s

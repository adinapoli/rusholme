-- e2e_011: Lazy function arguments
--
-- Tests that function arguments are not eagerly evaluated (call-by-need semantics).
-- Without lazy arguments, `error "unused"` would be evaluated immediately
-- when calling `const "hello" (error "unused")`, causing a runtime error.
-- With lazy arguments, the thunk is created but never forced because `const`
-- ignores its second argument.

const :: b -> a -> b
const x _ = x

main = putStrLn (const "hello" (error "unused"))

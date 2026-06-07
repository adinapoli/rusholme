-- Multi-binding `let` expression at value level (#747).
--
-- A `let` with two or more bindings is lowered through the `Rec` path in
-- the desugarer and GRIN translator (single-binding `let`s take the
-- `NonRec` workaround instead).  This test pins the regression independently
-- of list-comprehension layout (`#734`) — the multi-binding crash was first
-- noticed inside a list comprehension, but the root cause was in the `Rec`
-- lowering itself.  Expected behaviour:
--
--   * each binder gets its own `update` of the placeholder cell
--   * the placeholder cell is allocated with ≥1 field so the `update`
--     does not trip the `rts_store_field` index assertion
--
-- Both invariants are exercised by simply forcing every binder.  The
-- `let`-in expression form is used (rather than `do {let; ...}`) so the
-- test does not depend on the `do`-block desugarer's interaction with
-- let-bound names (see #566).
--
-- The "later binder references an earlier binder in the same group" case
-- (e.g. `let a = 1; b = a + 1`) is tracked separately in #753 and is
-- intentionally NOT exercised here.

twoBindings :: Int
twoBindings =
    let a = 1
        b = 2
    in a + b

threeBindings :: Int
threeBindings =
    let x = 10
        y = 20
        z = 30
    in x + y + z

main :: IO ()
main = do
    print twoBindings
    print threeBindings

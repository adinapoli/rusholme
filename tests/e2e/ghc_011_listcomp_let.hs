-- List comprehension `let` qualifier end-to-end test (#734, #747).
--
-- The `let` qualifier (Haskell 2010 §3.11) was previously rejected at parse
-- time because the layout processor did not open a layout context for a `let`
-- block appearing inside `[...]`.  These cases exercise:
--   * a single-binding let qualifier
--   * a let qualifier whose bound name is used by a following guard
--   * a let qualifier binding multiple names on one line (`;`-separated would
--     also work, but here we rely on layout closing at the `,`/`]`)
--   * two let qualifiers in the same comprehension
--   * a let qualifier binding multiple names that are all used in the body
--     (this was a separate crash even after #734 landed — the single-binding
--     `NonRec` codegen path worked, but the multi-binding `Rec` path
--     segfaulted at runtime because the placeholder heap cell was allocated
--     with 0 fields, so `rts_store_field(p, 0, ...)` tripped an assertion;
--     and a second bug dropped the `update` for the first binding when its
--     RHS was a simple `Return`.  Tracked in #747.)

main :: IO ()
main = do
    print [y | x <- [1, 2, 3], let y = x * 2]
    print [y | x <- [1, 2, 3, 4], let y = x * x, y > 5]
    print [a + b | x <- [1, 2, 3], let a = x * 10, let b = x + 1]
    print [t | x <- [1, 2, 3], let s = x * x, let t = s + 1, t > 5]
    -- Multi-binding let qualifier (regression test for #747). Previously
    -- segfaulted because (a) the unit-placeholder heap cell had 0 fields, so
    -- the subsequent `update` tripped an `index < n_fields` assertion in the
    -- RTS, and (b) the GRIN translator dropped the first binding's `update`
    -- when the RHS was a simple `Return`.  Expected: [5, 7] (a = x, b = x+1).
    print [a + b | x <- [1, 2, 3], let a = x; b = x + 1, a > 1]

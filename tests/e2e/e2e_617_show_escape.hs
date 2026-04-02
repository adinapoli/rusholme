-- e2e_617_show_escape: Show Char escape sequence handling
--
-- Tests that Show Char correctly escapes special characters instead of
-- emitting literal control characters. Covers the deliverables from issue #617.
--
-- Note: `show "string"` uses `Show [a]` (list format) rather than
-- a dedicated Show String instance; that is tracked separately.
-- `showString` can be called directly for double-quoted string output.

module ShowEscape where

main :: IO ()
main = do
    -- Plain printable character: no escaping needed
    putStrLn (show 'a')
    -- Backslash must be doubled
    putStrLn (show '\\')
    -- Single quote inside character literal
    putStrLn (show '\'')
    -- Common control characters
    putStrLn (show '\n')
    putStrLn (show '\t')
    putStrLn (show '\r')
    -- Double quote inside a character literal: showLitChar renders it
    -- literally ('"' is printable), so Show Char produces '"'
    putStrLn (show '"')
    -- Null character
    putStrLn (show '\0')
    -- showString produces double-quoted escaped output directly
    putStrLn (showString "hello\nworld")
    putStrLn (showString "a\tb")
    putStrLn (showString "back\\slash")
    putStrLn (showString "say \"hi\"")
    putStrLn (showString "abc")

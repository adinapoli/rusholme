-- e2e_show_nonascii_char: Show instance for non-ASCII characters
--
-- Tests that characters with codepoint > 127 are rendered as \<decimal>.

module ShowNonAsciiChar where

main :: IO ()
main = do
    putStrLn (show '\128')
    putStrLn (show '\233')

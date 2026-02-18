-- GHC testsuite: string and character literals, escape sequences
module Sc017StringCharLiterals where

-- Character literals
newline :: Char
newline = '\n'

tab :: Char
tab = '\t'

backslash :: Char
backslash = '\\'

singleQuote :: Char
singleQuote = '\''

nul :: Char
nul = '\NUL'

bell :: Char
bell = '\BEL'

-- Various escape sequences
escapes :: [Char]
escapes = ['\a', '\b', '\f', '\n', '\r', '\t', '\v']

-- Numeric escapes
charByNum :: Char
charByNum = '\65'  -- 'A'

charByHex :: Char
charByHex = '\x41' -- 'A'

charByOct :: Char
charByOct = '\o101' -- 'A'

-- String literals
hello :: String
hello = "Hello, World!"

multiEscape :: String
multiEscape = "tab:\there\nnewline"

-- String gap (backslash-whitespace-backslash continuation)
longString :: String
longString = "This is a very long \
             \string"

-- Empty string
empty :: String
empty = ""

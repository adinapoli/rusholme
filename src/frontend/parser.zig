//! Parsing of Haskell source code into AST.

pub const ParseError = error {
    UnexpectedToken,
    UnexpectedEOF,
    InvalidSyntax,
};

test "parser placeholder compiles" {
    _ = ParseError;
}

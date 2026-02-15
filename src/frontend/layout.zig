//! Haskell 2010 layout rule (indentation-based syntax).

pub const LayoutError = error {
    InconsistentIndentation,
    AmbiguousLayout,
};

test "layout placeholder compiles" {
    _ = LayoutError;
}

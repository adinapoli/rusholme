//! Runtime system for compiled Haskell programs.

pub const RuntimeError = error {
    OutOfMemory,
    StackOverflow,
    AssertionFailed,
};

test "runtime placeholder compiles" {
    _ = RuntimeError;
}

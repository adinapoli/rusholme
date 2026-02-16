//! Type checking module.

const std = @import("std");

pub const TypeError = error {
    UnificationFailure,
    TypeMismatch,
    MissingTypeAnnotation,
    InfiniteType,
};

test "TypeError enum variants compile" {
    // Just verify the error set type exists
    const info = @typeInfo(TypeError);
    _ = info;
}

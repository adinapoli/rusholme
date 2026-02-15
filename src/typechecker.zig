//! Type checking module.

pub const TypeError = error {
    UnificationFailure,
    TypeMismatch,
    MissingTypeAnnotation,
    InfiniteType,
};

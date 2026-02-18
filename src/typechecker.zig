//! Type checking module — public re-exports.
//!
//! This module is the external face of the typechecker pipeline stage.
//! Internal sub-modules live under `src/typechecker/`.

const std = @import("std");

pub const TypeError = error{
    UnificationFailure,
    TypeMismatch,
    MissingTypeAnnotation,
    InfiniteType,
};

// Sub-modules (re-exported for convenience via root.zig's `tc` namespace).
pub const htype = @import("typechecker/htype.zig");
pub const env = @import("typechecker/env.zig");
pub const unify = @import("typechecker/unify.zig");
pub const solver = @import("typechecker/solver.zig");
pub const infer = @import("typechecker/infer.zig");

test "TypeError enum variants compile" {
    const info = @typeInfo(TypeError);
    _ = info;
}

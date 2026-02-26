//! Thunk evaluator for LLVM-based runtime (issue #56/#384).
//!
//! This module implements thunk evaluation: forcing lazy values to WHNF
//! (Weak Head Normal Form).
//!
//! ## Evaluation strategy
//!
//! `rts_eval` implements the standard STG-style black-holing evaluation:
//!
//! ```
//! rts_eval(ptr):
//!   while true:
//!     switch ptr.tag:
//!       Ind       → ptr = ptr.data[0] (follow indirection)
//!       Blackhole → panic "<<loop>>"   (infinite loop detected)
//!       Thunk     → ptr.tag = Blackhole
//!                   result = ptr.fn_ptr(ptr.env)
//!                   ptr.tag = Ind
//!                   ptr.data[0] = result
//!                   return rts_eval(result)   (in case result is itself a thunk)
//!       _         → return ptr              (already WHNF)
//! ```
//!
//! The blackhole state prevents re-entrant evaluation of the same thunk,
//! which would otherwise spin forever.

const std = @import("std");
const node = @import("node.zig");

// ═══════════════════════════════════════════════════════════════════════
// Thunk Evaluation
// ═══════════════════════════════════════════════════════════════════════

/// Evaluate a node to WHNF (Weak Head Normal Form).
///
/// - Follows `Ind` chains to the final value.
/// - Forces `Thunk` nodes by calling their code pointer.
/// - Detects `Blackhole` (self-referential thunks) and panics.
/// - Returns all other node kinds unchanged.
///
/// This function is exported as `rts_eval` and called from LLVM-generated code.
pub export fn rts_eval(ptr_in: *node.Node) *node.Node {
    var ptr = ptr_in;

    while (true) {
        switch (ptr.tag) {
            // ── Indirection: follow the chain ──────────────────────────
            .Ind => {
                ptr = node.indTarget(ptr);
            },

            // ── Blackhole: self-referential thunk (infinite loop) ──────
            .Blackhole => {
                // This mirrors GHC's "<<loop>>" runtime error.
                @panic("<<loop>>: infinite loop detected during thunk evaluation");
            },

            // ── Thunk: force evaluation ────────────────────────────────
            .Thunk => {
                // Extract the thunk body before overwriting the tag.
                const fn_ptr = node.thunkFn(ptr);
                const env = node.thunkEnv(ptr);

                // Enter the blackhole state to detect re-entrant evaluation.
                ptr.tag = .Blackhole;

                // Force the thunk.
                const result = fn_ptr(env);

                // Update the node to an indirection pointing at the result.
                // This memoises the value so subsequent evaluations are O(1).
                ptr.data[0] = @intFromPtr(result);
                ptr.tag = .Ind;

                // The result might itself be a thunk — keep looping.
                ptr = result;
            },

            // ── Already in WHNF ───────────────────────────────────────
            else => return ptr,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

const heap = @import("heap.zig");

test "rts_eval exports C function" {
    const testing = std.testing;
    _ = testing;
}

test "evaluate non-thunk returns as-is" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    const result = rts_eval(n);

    try std.testing.expectEqual(n, result);
}

test "evaluate indirection follows chain" {
    heap.init();
    defer heap.deinit();

    const target = node.createInt(7);
    const ind = node.createInd(target);

    const result = rts_eval(ind);
    try std.testing.expectEqual(target, result);
    try std.testing.expectEqual(node.Tag.Int, result.tag);
}

test "evaluate double indirection follows chain" {
    heap.init();
    defer heap.deinit();

    const target = node.createInt(5);
    const ind2 = node.createInd(target);
    const ind1 = node.createInd(ind2);

    const result = rts_eval(ind1);
    try std.testing.expectEqual(target, result);
}

test "evaluate thunk forces and memoizes" {
    heap.init();
    defer heap.deinit();

    // Thunk that returns a freshly created Int(42) node.
    const ThunkHelper = struct {
        fn eval(env: *node.Node) callconv(.auto) *node.Node {
            _ = env;
            return node.createInt(42);
        }
    };

    const env = node.createUnit(); // empty environment
    const thunk = node.createThunk(ThunkHelper.eval, env);
    try std.testing.expectEqual(node.Tag.Thunk, thunk.tag);

    // Force the thunk.
    const result = rts_eval(thunk);
    try std.testing.expectEqual(node.Tag.Int, result.tag);

    // The thunk node itself should now be an Ind to the result.
    try std.testing.expectEqual(node.Tag.Ind, thunk.tag);
    try std.testing.expectEqual(result, node.indTarget(thunk));

    // A second call should follow the Ind without re-calling the thunk.
    const result2 = rts_eval(thunk);
    try std.testing.expectEqual(result, result2);
}

test "evaluate thunk returns self-evaluating value" {
    heap.init();
    defer heap.deinit();

    // Thunk that returns a Unit node (already WHNF after forcing).
    const ThunkHelper = struct {
        fn eval(env: *node.Node) callconv(.auto) *node.Node {
            _ = env;
            return node.createUnit();
        }
    };

    const thunk = node.createThunk(ThunkHelper.eval, node.createUnit());
    const result = rts_eval(thunk);
    try std.testing.expectEqual(node.Tag.Unit, result.tag);
    // Thunk becomes Ind after evaluation.
    try std.testing.expectEqual(node.Tag.Ind, thunk.tag);
}

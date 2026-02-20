//! Cycle detection for typechecker metavariable chains.
//!
//! Exposes a `MetaChainWalker` which uses Floyd's Tortoise and Hare algorithm
//! to safely traverse `HType` chains. Typecheckers use this whenever they must
//! follow a pointer chain of solved `MetaVar`s (`chase`, `tailPtr`, `bindPtr`).
//! If `step` returns an error, the chain contains a cycle, preventing an infinite loop.

const htype = @import("htype.zig");
const HType = htype.HType;

pub const CycleError = error{
    /// A cycle was detected in the metavariable chain.
    InfiniteTypeCycle,
};

/// Follows a chain of solved metavariables by value to the first unsolved one or non-Meta node.
/// Returns the final `HType`. Returns `CycleError.InfiniteTypeCycle` if a cycle is detected.
pub fn chaseValue(start: HType) CycleError!HType {
    var slow = start;
    var fast = start;

    while (true) {
        // Advance fast by 2 steps if possible
        if (fast == .Meta and fast.Meta.ref != null) {
            fast = fast.Meta.ref.?.*;
            if (fast == .Meta and fast.Meta.ref != null) {
                fast = fast.Meta.ref.?.*;
            }
        }

        // Advance slow by 1 step
        switch (slow) {
            .Meta => |mv| {
                if (mv.ref) |next| {
                    slow = next.*;

                    if (fast == .Meta and fast.Meta.ref != null and slow == .Meta and slow.Meta.id == fast.Meta.id) {
                        return CycleError.InfiniteTypeCycle;
                    }
                } else {
                    return slow; // unsolved
                }
            },
            else => return slow,
        }
    }
}

/// Follows a chain of solved metavariables by pointer to the first unsolved one.
/// The input node must be a `.Meta` node.
/// Returns the pointer to the final `HType`. Returns `CycleError.InfiniteTypeCycle` if a cycle is detected.
pub fn chasePtr(start: *HType) CycleError!*HType {
    var slow: *HType = start;
    var fast: *HType = start;

    while (true) {
        if (fast.* == .Meta and fast.Meta.ref != null) {
            fast = fast.Meta.ref.?;
            if (fast.* == .Meta and fast.Meta.ref != null) {
                fast = fast.Meta.ref.?;
            }
        }

        switch (slow.*) {
            .Meta => |mv| {
                if (mv.ref) |next| {
                    slow = next;

                    if (fast.* == .Meta and fast.Meta.ref != null and slow == fast) {
                        return CycleError.InfiniteTypeCycle;
                    }
                } else {
                    return slow; // unsolved
                }
            },
            else => unreachable,
        }
    }
}

const std = @import("std");
const testing = std.testing;

test "cycle_detection: chaseValue empty chain" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var supply = htype.MetaVarSupply{};
    const mv = supply.fresh();
    const node = HType{ .Meta = mv };

    const result = try chaseValue(node);
    try testing.expect(result == .Meta);
    try testing.expectEqual(mv.id, result.Meta.id);
}

test "cycle_detection: chaseValue cycle detected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var supply = htype.MetaVarSupply{};
    var node0 = HType{ .Meta = supply.fresh() };
    var node1 = HType{ .Meta = supply.fresh() };

    // Create a cycle: ?0 -> ?1 -> ?0
    node0.Meta.ref = &node1;
    node1.Meta.ref = &node0;

    const result = chaseValue(node0);
    try testing.expectError(CycleError.InfiniteTypeCycle, result);
}

test "cycle_detection: chasePtr empty chain" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var supply = htype.MetaVarSupply{};
    const mv = supply.fresh();
    var node = HType{ .Meta = mv };

    const result = try chasePtr(&node);
    try testing.expect(result == &node);
}

test "cycle_detection: chasePtr cycle detected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var supply = htype.MetaVarSupply{};
    var node0 = HType{ .Meta = supply.fresh() };
    var node1 = HType{ .Meta = supply.fresh() };

    // Create a cycle: ?0 -> ?1 -> ?0
    node0.Meta.ref = &node1;
    node1.Meta.ref = &node0;

    const result = chasePtr(&node0);
    try testing.expectError(CycleError.InfiniteTypeCycle, result);
}

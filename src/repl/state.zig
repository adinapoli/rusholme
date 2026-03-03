//! REPL State Management
//!
//! Accumulates bindings across REPL session iterations with incremental caching.

const std = @import("std");

// Simplified CompileUnit for MVP - stores raw program text
// In future, this would hold the parsed AST/compiled program
pub const CompileUnit = struct {
    source: []const u8,
};

// Simplified RuntimeState for MVP
pub const RuntimeState = struct {
    // Will hold heap and evaluation state in future iterations
    pub fn init(allocator: std.mem.Allocator) RuntimeState {
        _ = allocator;
        return .{};
    }

    pub fn deinit(self: *RuntimeState) void {
        _ = self;
    }
};

/// REPL session state
pub const ReplState = struct {
    allocator: std.mem.Allocator,
    bindings: std.StringHashMap(CompileUnit),
    compiled_cache: std.StringHashMap(*void), // Placeholder for GRIN program cache
    // Future: Add type_env when we have TypeEnv type available

    pub fn init(allocator: std.mem.Allocator) ReplState {
        return ReplState{
            .allocator = allocator,
            .bindings = std.StringHashMap(CompileUnit).init(allocator),
            .compiled_cache = std.StringHashMap(*void).init(allocator),
        };
    }

    pub fn deinit(self: *ReplState) void {
        self.bindings.deinit();
        self.compiled_cache.deinit();
    }

    pub fn addBinding(self: *ReplState, name: []const u8, unit: CompileUnit) !void {
        try self.bindings.put(name, unit);
    }

    pub fn getCompiled(self: *const ReplState, name: []const u8) ?*void {
        return self.compiled_cache.get(name);
    }
};

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "repl state init" {
    var state = try ReplState.init(testing.allocator);
    defer state.deinit();
}

//! Runtime value representation.
//!
//! This module defines the representation of values at runtime, including:
//! - Heap objects (constructors, closures, partial applications)
//! - Literal values (integers, floats, characters, strings)
//! - Unit and bottom values

const std = @import("std");
const Allocator = std.mem.Allocator;

// ── Runtime Value ───────────────────────────────────────────────────────

/// A runtime value in the GRIN evaluator.
///
/// Values are the result of evaluating GRIN expressions. They can be:
/// - Heap pointers (to constructors, closures, etc.)
/// - Literal values (unboxed integers, floats, etc.)
/// - Unit value
pub const Value = union(enum) {
    /// A pointer to a heap-allocated node.
    /// The index refers to a position in the Heap's nodes array.
    Ptr: u32,

    /// An unboxed integer.
    Int: i64,

    /// An unboxed floating-point number.
    Double: f64,

    /// An unboxed character.
    Char: u21,

    /// An unboxed boolean.
    Bool: bool,

    /// Unit value (result of IO () etc.).
    Unit: void,

    /// A heap-allocated string.
    /// The slice is owned by the heap/allocator.
    String: []const u8,

    /// A heap-allocated constructor node.
    /// Contains the constructor tag and field values.
    Con: ConNode,

    /// A closure/thunk (unevaluated computation).
    Closure: Closure,

    /// A partial application (function with some args applied).
    Partial: PartialApp,

    /// Bottom/undefined value. Used for error cases.
    Bottom: void,

    // ── Constructors ─────────────────────────────────────────────────────

    /// Create a unit value.
    pub const unit: Value = .{ .Unit = {} };

    /// Create a boolean value.
    pub fn fromBool(b: bool) Value {
        return .{ .Bool = b };
    }

    /// Create an integer value.
    pub fn fromInt(i: i64) Value {
        return .{ .Int = i };
    }

    /// Create a double value.
    pub fn fromDouble(d: f64) Value {
        return .{ .Double = d };
    }

    /// Create a character value.
    pub fn fromChar(c: u21) Value {
        return .{ .Char = c };
    }

    // ── Queries ───────────────────────────────────────────────────────────

    /// Check if this value is a heap pointer.
    pub fn isPtr(self: Value) bool {
        return self == .Ptr;
    }

    /// Check if this value is a literal (unboxed).
    pub fn isLiteral(self: Value) bool {
        return switch (self) {
            .Int, .Double, .Char, .Bool => true,
            else => false,
        };
    }

    /// Check if this value is unit.
    pub fn isUnit(self: Value) bool {
        return self == .Unit;
    }

    /// Get the value as a string, if it is one.
    pub fn asString(self: Value) ?[]const u8 {
        return switch (self) {
            .String => |s| s,
            else => null,
        };
    }

    /// Get the value as an integer, if it is one.
    pub fn asInt(self: Value) ?i64 {
        return switch (self) {
            .Int => |i| i,
            else => null,
        };
    }

    /// Get the value as a boolean, if it is one.
    pub fn asBool(self: Value) ?bool {
        return switch (self) {
            .Bool => |b| b,
            else => null,
        };
    }

    // ── Formatting ────────────────────────────────────────────────────────

    pub fn format(self: Value, w: *std.Io.Writer) std.Io.Writer.Error!void {
        switch (self) {
            .Ptr => |p| try w.print("Ptr({d})", .{p}),
            .Int => |i| try w.print("{d}", .{i}),
            .Double => |d| try w.print("{d}", .{d}),
            .Char => |c| try w.print("'{u}'", .{c}),
            .Bool => |b| try w.print("{}", .{b}),
            .Unit => try w.writeAll("()"),
            .String => |s| try w.print("\"{s}\"", .{s}),
            .Con => |con| {
                try w.print("Con({s}", .{con.tag});
                for (con.fields) |f| {
                    try w.writeAll(", ");
                    try f.format(w);
                }
                try w.writeAll(")");
            },
            .Closure => try w.writeAll("<closure>"),
            .Partial => |p| try w.print("Partial({d})", .{p.missing}),
            .Bottom => try w.writeAll("_|_"),
        }
    }
};

/// A heap-allocated constructor node.
pub const ConNode = struct {
    /// The constructor tag (e.g., "Just", "Cons", "True").
    tag: []const u8,

    /// The fields of the constructor.
    fields: []const Value,

    /// Source span for debugging (optional).
    span: ?SourceSpan = null,
};

/// A closure: an unevaluated computation.
pub const Closure = struct {
    /// The function to call when evaluated.
    func: []const u8,

    /// Captured environment (free variables).
    env: []const Value,
};

/// A partial application: a function with some arguments already applied.
pub const PartialApp = struct {
    /// The function being applied.
    func: []const u8,

    /// Arguments already applied.
    args: []const Value,

    /// Number of arguments still missing.
    missing: u32,
};

/// Source span (placeholder for now).
pub const SourceSpan = struct {
    start: u32,
    end: u32,
};

// ── Evaluation Error ─────────────────────────────────────────────────────

/// Errors that can occur during evaluation.
pub const EvalError = error{
    /// Heap allocation failed.
    OutOfMemory,

    /// Attempted to evaluate a non-function.
    NotAFunction,

    /// Wrong number of arguments.
    ArityMismatch,

    /// Pattern match failure.
    PatternMatchFailure,

    /// Unbound variable.
    UnboundVariable,

    /// Division by zero.
    DivisionByZero,

    /// User-level error (from `error#` primop).
    RuntimeError,

    /// Invalid operation for this value type.
    TypeError,

    /// IO error.
    IOError,

    /// Unimplemented feature.
    NotImplemented,
};

// ── Heap ─────────────────────────────────────────────────────────────────

/// A simple heap for allocating runtime values.
///
/// For M1, this is a simple bump allocator. Later milestones will
/// add proper garbage collection (Immix-style).
pub const Heap = struct {
    /// The underlying allocator.
    allocator: Allocator,

    /// All allocated nodes.
    nodes: std.ArrayList(Value),

    /// Initialize a new heap.
    pub fn init(allocator: Allocator) !Heap {
        return .{
            .allocator = allocator,
            .nodes = try std.ArrayList(Value).initCapacity(allocator, 64),
        };
    }

    /// Deallocate the heap.
    pub fn deinit(self: *Heap) void {
        // Free any owned strings
        for (self.nodes.items) |node| {
            switch (node) {
                .String => |s| self.allocator.free(s),
                .Con => |con| {
                    self.allocator.free(con.fields);
                    // Note: tag is expected to be static or owned elsewhere
                },
                .Closure => |cl| {
                    self.allocator.free(cl.env);
                },
                .Partial => |pa| {
                    self.allocator.free(pa.args);
                },
                else => {},
            }
        }
        self.nodes.deinit(self.allocator);
    }

    /// Allocate a value on the heap, returning a pointer to it.
    pub fn alloc(self: *Heap, value: Value) EvalError!Value {
        const idx: u32 = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, value);
        return .{ .Ptr = idx };
    }

    /// Read a value from the heap.
    pub fn get(self: Heap, ptr: u32) ?Value {
        if (ptr >= self.nodes.items.len) return null;
        return self.nodes.items[ptr];
    }

    /// Update a value on the heap (for lazy evaluation / blackholing).
    pub fn update(self: *Heap, ptr: u32, value: Value) bool {
        if (ptr >= self.nodes.items.len) return false;
        self.nodes.items[ptr] = value;
        return true;
    }
};

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

test "Value: integer" {
    const v = Value.fromInt(42);
    try testing.expectEqual(@as(i64, 42), v.Int);
    try testing.expect(v.isLiteral());
    try testing.expect(!v.isPtr());
}

test "Value: boolean" {
    const v = Value.fromBool(true);
    try testing.expect(v.Bool);
    try testing.expectEqual(@as(?bool, true), v.asBool());
}

test "Value: unit" {
    const v = Value.unit;
    try testing.expect(v.isUnit());
}

test "Heap: allocate and read" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();

    const ptr = try heap.alloc(.{ .Int = 42 });
    try testing.expect(ptr.isPtr());

    const retrieved = heap.get(ptr.Ptr);
    try testing.expect(retrieved != null);
    try testing.expectEqual(@as(i64, 42), retrieved.?.Int);
}

test "Heap: update" {
    var heap = try Heap.init(testing.allocator);
    defer heap.deinit();

    const ptr = try heap.alloc(.{ .Int = 42 });
    _ = heap.update(ptr.Ptr, .{ .Int = 99 });

    const retrieved = heap.get(ptr.Ptr);
    try testing.expectEqual(@as(i64, 99), retrieved.?.Int);
}

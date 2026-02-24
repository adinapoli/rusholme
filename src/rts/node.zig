//! Heap node representation for LLVM-based runtime (issue #56).
//!
//! Heap nodes are the fundamental unit of memory in the runtime.
//! They carry a tag (indicating the type) and field data.
//!
// tracked in: https://github.com/adinapoli/rusholme/issues/385

const std = @import("std");
const heap = @import("heap.zig");

// ═══════════════════════════════════════════════════════════════════════
// Node Tag Encoding
// ═══════════════════════════════════════════════════════════════════════

/// Node tags identify the type and structure of a heap node.
pub const Tag = enum(u64) {
    // ── Primitive Types ────────────────────────────────────────────────
    Unit = 0,        // () value
    Int = 1,         // Unboxed integer
    Char = 2,        // Unboxed character (byte)
    String = 3,      // String literal (pointer to bytes)

    // ── Thunks ─────────────────────────────────────────────────────────
    Thunk = 0x100,   // Lazy value (placeholder awaiting evaluation)

    // ── Function Closures ──────────────────────────────────────────────
    Closure = 0x200, // Function closure (code + environment)

    // ── User-defined ADTs ───────────────────────────────────────────────
    // These start at 0x1000 and are generated per type constructor
    Data = 0x1000,
};

// ═══════════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════════

pub fn createUnit() *Node {
    const node = heap.allocator().create(Node) catch @panic("OOM");
    node.* = .{ .tag = .Unit, .data = [_]u64{0} ** 8 };
    return node;
}

pub fn createInt(value: i64) *Node {
    const node = heap.allocator().create(Node) catch @panic("OOM");
    node.* = .{ .tag = .Int, .data = [_]u64{0} ** 8 };
    @memcpy(std.mem.asBytes(&node.data[0]), std.mem.asBytes(&value));
    return node;
}

pub fn createChar(value: u8) *Node {
    const node = heap.allocator().create(Node) catch @panic("OOM");
    node.* = .{ .tag = .Char, .data = [_]u64{0} ** 8 };
    node.data[0] = value;
    return node;
}

pub fn createString(ptr: [*]const u8) *Node {
    const node = heap.allocator().create(Node) catch @panic("OOM");
    node.* = .{ .tag = .String, .data = [_]u64{0} ** 8 };
    node.data[0] = @intFromPtr(ptr);
    return node;
}

// ═══════════════════════════════════════════════════════════════════════
// Heap Node Structure
// ═══════════════════════════════════════════════════════════════════════

/// A heap node represents a value in the runtime.
/// It consists of a tag indicating the type, followed by field data.
pub const Node = extern struct {
    /// Tag identifying the node type.
    tag: Tag,

    // For M1, we use simple field storage
    // Full ADT support will be added with GRIN expression codegen
    data: [8]u64 align(1),
};

// ═══════════════════════════════════════════════════════════════════════
// Runtime Allocation Functions
// ═══════════════════════════════════════════════════════════════════════

/// Allocate a heap node with the given tag.
/// This is called `rts_alloc` from LLVM.
export fn rts_alloc(tag: u64) *Node {
    const node = heap.allocator().create(Node) catch @panic("OOM");
    node.tag = @enumFromInt(tag);
    node.data = [_]u64{0} ** 8;
    return node;
}

/// Store node fields after allocation.
/// Called after rts_alloc to initialize the node.
export fn rts_store(node: *Node, fields: [*]const u64, field_count: usize) void {
    // Copy fields into the node
    for (0..@min(field_count, 8)) |i| {
        node.data[i] = fields[i];
    }
}

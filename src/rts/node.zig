//! Heap node representation for LLVM-based runtime.
//!
//! Heap nodes are the fundamental unit of memory in the runtime.
//! Each node carries a tag (identifying its type/constructor) followed
//! immediately in memory by a variable-length array of 64-bit field slots.
//!
//! ## Field Encoding
//!
//! Field slots are 64-bit integers that encode GRIN values:
//!   - `*Node` child pointers  → stored as `@intFromPtr(child)` (a non-null address)
//!   - Unboxed integers        → stored as the raw i64 bit-pattern (@bitCast)
//!   - Unboxed characters      → stored as the raw u8 value (zero-extended)
//!   - String literals         → stored as `@intFromPtr(ptr_to_bytes)` (same as pointer)
//!
//! The tag determines how fields are interpreted — the runtime never needs to
//! distinguish scalars from pointers at the field level without knowing the
//! node's type.
//!
//! ## Layout
//!
//!   ┌──────────────┬────────────────┬───────────────────────────────────────┐
//!   │  tag (u64)   │ n_fields (u32) │ _pad (u32) │ field[0] … field[N-1]   │
//!   └──────────────┴────────────────┴───────────────────────────────────────┘
//!
//! The header is 16 bytes; each field is 8 bytes (u64).
//! Nodes are allocated via `rts_alloc(tag, n_fields)` which uses the heap
//! arena to allocate exactly `@sizeOf(Node) + n_fields * 8` bytes.
//!
//! ## Primitive types
//!
//! Unit  — n_fields=0, no field slots needed.
//! Int   — n_fields=1, field[0] holds the i64 value (@bitCast to u64).
//! Char  — n_fields=1, field[0] holds the u8 value (zero-extended).
//! String— n_fields=1, field[0] holds the `[*]const u8` pointer as a usize.
//!
//! ## User-defined ADTs
//!
//! Constructor with k fields → n_fields=k.  Each field slot holds either a
//! `*Node` pointer (for sub-expressions) or an unboxed scalar value,
//! depending on the constructor's type.
//!
//! ## ABI note
//!
//! The LLVM codegen currently allocates nodes via `malloc` with its own
//! layout (`{ i64 tag, ptr field0, … }`) and does not yet call `rts_alloc`.
//! Unifying the layouts is tracked in:
//!   https://github.com/adinapoli/rusholme/issues/422

const std = @import("std");
const heap = @import("heap.zig");

// ═══════════════════════════════════════════════════════════════════════
// Node Tag Encoding
// ═══════════════════════════════════════════════════════════════════════

/// Node tags identify the type and structure of a heap node.
pub const Tag = enum(u64) {
    // ── Primitive Types ────────────────────────────────────────────────
    Unit = 0,        // () value — n_fields = 0
    Int = 1,         // Unboxed integer — n_fields = 1, field[0] = i64 bits
    Char = 2,        // Unboxed character — n_fields = 1, field[0] = u8
    String = 3,      // String literal — n_fields = 1, field[0] = ptr

    // ── Thunks ─────────────────────────────────────────────────────────
    Thunk = 0x100,   // Lazy value (placeholder awaiting evaluation)
                     // field[0] = fn_ptr as usize, field[1] = *Node env

    // ── Function Closures ──────────────────────────────────────────────
    // tracked in: https://github.com/adinapoli/rusholme/issues/386
    Closure = 0x200, // Function closure (code + environment)

    // ── User-defined ADTs ───────────────────────────────────────────────
    // Tags for user-defined constructors start at 0x1000.
    // Each unique constructor gets its own discriminant.
    Data = 0x1000,
};

// ═══════════════════════════════════════════════════════════════════════
// Heap Node Structure
// ═══════════════════════════════════════════════════════════════════════

/// A heap node represents a value in the runtime.
///
/// The node header occupies `@sizeOf(Node)` bytes.  Immediately following
/// the header in memory are `n_fields` 64-bit field slots.  Access them
/// via the `fields(node)` helper — do NOT index `node.data` directly.
pub const Node = extern struct {
    /// Tag identifying the node type and how fields are interpreted.
    tag: Tag,

    /// Number of field slots that follow the header in memory.
    n_fields: u32,

    /// Explicit padding to make the header 16 bytes on all targets.
    _pad: u32 = 0,
};

// ═══════════════════════════════════════════════════════════════════════
// Field Access
// ═══════════════════════════════════════════════════════════════════════

/// Return a slice of the `n_fields` field slots that follow `node` in memory.
///
/// The caller must not access slots beyond `node.n_fields`.
pub fn fields(node: *Node) []u64 {
    const base: [*]u64 = @ptrCast(@alignCast(
        @as([*]u8, @ptrCast(node)) + @sizeOf(Node),
    ));
    return base[0..node.n_fields];
}

/// Return a const slice of the field slots (read-only access).
pub fn fieldsConst(node: *const Node) []const u64 {
    const base: [*]const u64 = @ptrCast(@alignCast(
        @as([*]const u8, @ptrCast(node)) + @sizeOf(Node),
    ));
    return base[0..node.n_fields];
}

// ═══════════════════════════════════════════════════════════════════════
// Primitive Node Helpers
// ═══════════════════════════════════════════════════════════════════════

/// Allocate a Unit node.  Unit carries no fields.
pub fn createUnit() *Node {
    const n = allocNode(1);
    n.* = .{ .tag = .Unit, .n_fields = 0 };
    return n;
}

/// Allocate an Int node holding `value`.
pub fn createInt(value: i64) *Node {
    const n = allocNode(1);
    n.* = .{ .tag = .Int, .n_fields = 1 };
    fields(n)[0] = @bitCast(value);
    return n;
}

/// Allocate a Char node holding `value`.
pub fn createChar(value: u8) *Node {
    const n = allocNode(1);
    n.* = .{ .tag = .Char, .n_fields = 1 };
    fields(n)[0] = value;
    return n;
}

/// Allocate a String node holding a pointer to bytes.
pub fn createString(ptr: [*]const u8) *Node {
    const n = allocNode(1);
    n.* = .{ .tag = .String, .n_fields = 1 };
    fields(n)[0] = @intFromPtr(ptr);
    return n;
}

/// Allocate a Data node with the given tag discriminant and field values.
/// Each field value is a raw 64-bit slot (pointer-or-scalar as appropriate).
pub fn createData(disc: u64, field_vals: []const u64) *Node {
    const n_fields: u32 = @intCast(field_vals.len);
    const n = allocNode(n_fields);
    n.* = .{ .tag = @enumFromInt(disc), .n_fields = n_fields };
    @memcpy(fields(n), field_vals);
    return n;
}

// ═══════════════════════════════════════════════════════════════════════
// Typed Field Readers
// ═══════════════════════════════════════════════════════════════════════

/// Read the integer value from an Int node.
pub fn intValue(n: *const Node) i64 {
    std.debug.assert(n.tag == .Int and n.n_fields >= 1);
    return @bitCast(fieldsConst(n)[0]);
}

/// Read the character value from a Char node.
pub fn charValue(n: *const Node) u8 {
    std.debug.assert(n.tag == .Char and n.n_fields >= 1);
    return @intCast(fieldsConst(n)[0]);
}

/// Read the string pointer from a String node.
pub fn stringValue(n: *const Node) [*]const u8 {
    std.debug.assert(n.tag == .String and n.n_fields >= 1);
    return @ptrFromInt(fieldsConst(n)[0]);
}

/// Read the i-th field as a `*Node` pointer.
pub fn fieldNode(n: *const Node, i: u32) *Node {
    std.debug.assert(i < n.n_fields);
    return @ptrFromInt(fieldsConst(n)[i]);
}

// ═══════════════════════════════════════════════════════════════════════
// Internal Allocation
// ═══════════════════════════════════════════════════════════════════════

/// Allocate `@sizeOf(Node) + n_fields * @sizeOf(u64)` bytes from the heap
/// and return a `*Node` pointer to the header.
///
/// The returned node's tag and n_fields are NOT initialised — callers must
/// set them immediately.
fn allocNode(n_fields: u32) *Node {
    const total = @sizeOf(Node) + @as(usize, n_fields) * @sizeOf(u64);
    // Use Allocator.alignedAlloc with the Alignment enum expected by Zig 0.16-dev.
    const alignment: std.mem.Alignment = @enumFromInt(@as(std.math.Log2Int(usize), @intCast(std.math.log2(@alignOf(Node)))));
    const raw = heap.allocator().alignedAlloc(u8, alignment, total) catch @panic("OOM");
    return @ptrCast(raw.ptr);
}

// ═══════════════════════════════════════════════════════════════════════
// Runtime Allocation Functions (called from LLVM-generated code)
// ═══════════════════════════════════════════════════════════════════════

/// Allocate a heap node with the given tag and field count.
/// Called `rts_alloc` from LLVM-generated code.
///
/// The returned node has its tag and n_fields set; all field slots are
/// zeroed.  The caller must initialise fields via `rts_store_field`.
pub export fn rts_alloc(tag: u64, n_fields: u32) *Node {
    const n = allocNode(n_fields);
    n.* = .{ .tag = @enumFromInt(tag), .n_fields = n_fields };
    // Zero all field slots.
    for (fields(n)) |*f| f.* = 0;
    return n;
}

/// Store a single field value into a node at the given index.
/// Called `rts_store_field` from LLVM-generated code.
///
/// `value` is a 64-bit encoding of the field — either an integer scalar
/// (for Int/Char fields) or a pointer cast to u64 (for *Node fields).
pub export fn rts_store_field(n: *Node, index: u32, value: u64) void {
    std.debug.assert(index < n.n_fields);
    fields(n)[index] = value;
}

/// Bulk-initialise all fields from a caller-provided array.
/// Called `rts_store` from LLVM-generated code (backwards-compatible
/// with the previous fixed-array API).
///
/// Only `@min(field_count, n.n_fields)` slots are written.
pub export fn rts_store(n: *Node, field_vals: [*]const u64, field_count: usize) void {
    const count = @min(field_count, n.n_fields);
    for (0..count) |i| {
        fields(n)[i] = field_vals[i];
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "Node header is 16 bytes" {
    try std.testing.expectEqual(16, @sizeOf(Node));
}

test "alloc unit node" {
    heap.init();
    defer heap.deinit();

    const n = createUnit();
    try std.testing.expectEqual(Tag.Unit, n.tag);
    try std.testing.expectEqual(0, n.n_fields);
}

test "alloc integer node and read back" {
    heap.init();
    defer heap.deinit();

    const n = createInt(42);
    try std.testing.expectEqual(Tag.Int, n.tag);
    try std.testing.expectEqual(1, n.n_fields);
    try std.testing.expectEqual(42, intValue(n));
}

test "alloc negative integer node" {
    heap.init();
    defer heap.deinit();

    const n = createInt(-7);
    try std.testing.expectEqual(-7, intValue(n));
}

test "alloc character node and read back" {
    heap.init();
    defer heap.deinit();

    const n = createChar('A');
    try std.testing.expectEqual(Tag.Char, n.tag);
    try std.testing.expectEqual(1, n.n_fields);
    try std.testing.expectEqual('A', charValue(n));
}

test "alloc string node and read back" {
    heap.init();
    defer heap.deinit();

    const hello: [*]const u8 = "Hello";
    const n = createString(hello);
    try std.testing.expectEqual(Tag.String, n.tag);
    try std.testing.expectEqual(1, n.n_fields);
    try std.testing.expectEqual(hello, stringValue(n));
}

test "alloc data node with fields" {
    heap.init();
    defer heap.deinit();

    // Simulate a two-field ADT constructor (discriminant 0x1000).
    const child_a = createInt(10);
    const child_b = createInt(20);
    const field_vals = [_]u64{
        @intFromPtr(child_a),
        @intFromPtr(child_b),
    };
    const n = createData(0x1000, &field_vals);
    try std.testing.expectEqual(Tag.Data, n.tag);
    try std.testing.expectEqual(2, n.n_fields);
    try std.testing.expectEqual(child_a, fieldNode(n, 0));
    try std.testing.expectEqual(child_b, fieldNode(n, 1));
}

test "rts_alloc and rts_store_field" {
    heap.init();
    defer heap.deinit();

    const n = rts_alloc(1, 1); // Tag.Int, 1 field
    try std.testing.expectEqual(Tag.Int, n.tag);
    rts_store_field(n, 0, @bitCast(@as(i64, 99)));
    try std.testing.expectEqual(99, intValue(n));
}

test "rts_alloc and rts_store bulk" {
    heap.init();
    defer heap.deinit();

    const n = rts_alloc(0x1000, 2); // Tag.Data, 2 fields
    const vals = [_]u64{ 111, 222 };
    rts_store(n, &vals, 2);
    try std.testing.expectEqual(111, fields(n)[0]);
    try std.testing.expectEqual(222, fields(n)[1]);
}

test "unit node has zero fields slice" {
    heap.init();
    defer heap.deinit();

    const n = createUnit();
    try std.testing.expectEqual(0, fields(n).len);
}

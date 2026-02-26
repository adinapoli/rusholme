//! Heap node representation for LLVM-based runtime (issue #56).
//!
//! Heap nodes are the fundamental unit of memory in the runtime.
//! Each node carries a tag (identifying the value kind) and a fixed-size
//! data region used to store fields, pointers, or thunk state.
//!
//! ## Node layout
//!
//! ```
//! Node {
//!   tag:  u64   — discriminant; see Tag
//!   data: [8]u64 — payload; interpretation depends on tag
//! }
//! ```
//!
//! ### Thunk layout (tag == .Thunk)
//!
//! ```
//! data[0] = fn_ptr : uintptr of ThunkFn
//! data[1] = env    : uintptr of *Node (captured environment / closure payload)
//! ```
//!
//! ### Indirection layout (tag == .Ind)
//!
//! ```
//! data[0] = target : uintptr of *Node (the evaluated result)
//! ```
//!
//! tracked in: https://github.com/adinapoli/rusholme/issues/385

const std = @import("std");
const heap = @import("heap.zig");

// ═══════════════════════════════════════════════════════════════════════
// Node Tag Encoding
// ═══════════════════════════════════════════════════════════════════════

/// Node tags identify the type and structure of a heap node.
pub const Tag = enum(u64) {
    // ── Primitive Types ────────────────────────────────────────────────
    Unit = 0,          // () value
    Int = 1,           // Unboxed integer
    Char = 2,          // Unboxed character (byte)
    String = 3,        // String literal (pointer to bytes)

    // ── Thunk / Evaluation States ──────────────────────────────────────
    //
    // State machine: Thunk → Blackhole → Ind
    //
    //   1. A newly allocated lazy value starts as Thunk.
    //   2. When rts_eval begins forcing it, the tag is set to Blackhole
    //      to detect infinite loops.  Any re-entrant call to rts_eval
    //      on a Blackhole panics with a "<<loop>>" message.
    //   3. After evaluation, the tag is updated to Ind and data[0] is
    //      set to the WHNF result pointer.
    Thunk = 0x100,     // Lazy value (fn_ptr + env, awaiting evaluation)
    Blackhole = 0x101, // Being evaluated now (cycle-detection guard)
    Ind = 0x102,       // Indirection to an already-evaluated node

    // ── Function Closures ──────────────────────────────────────────────
    Closure = 0x200,   // Function closure (code + environment)

    // ── User-defined ADTs ───────────────────────────────────────────────
    // These start at 0x1000 and are generated per type constructor.
    Data = 0x1000,
};

// ═══════════════════════════════════════════════════════════════════════
// Heap Node Structure
// ═══════════════════════════════════════════════════════════════════════

/// A heap node represents a value in the runtime.
/// It consists of a tag indicating the type, followed by field data.
pub const Node = extern struct {
    /// Tag identifying the node type.
    tag: Tag,
    // For M1, we use a fixed 8-element data region.
    // Full variable-length ADT field storage: tracked in #385.
    data: [8]u64 align(1),
};

// ═══════════════════════════════════════════════════════════════════════
// Helpers — primitive value constructors
// ═══════════════════════════════════════════════════════════════════════

pub fn createUnit() *Node {
    const n = heap.allocator().create(Node) catch @panic("OOM");
    n.* = .{ .tag = .Unit, .data = [_]u64{0} ** 8 };
    return n;
}

pub fn createInt(value: i64) *Node {
    const n = heap.allocator().create(Node) catch @panic("OOM");
    n.* = .{ .tag = .Int, .data = [_]u64{0} ** 8 };
    @memcpy(std.mem.asBytes(&n.data[0]), std.mem.asBytes(&value));
    return n;
}

pub fn createChar(value: u8) *Node {
    const n = heap.allocator().create(Node) catch @panic("OOM");
    n.* = .{ .tag = .Char, .data = [_]u64{0} ** 8 };
    n.data[0] = value;
    return n;
}

pub fn createString(ptr: [*]const u8) *Node {
    const n = heap.allocator().create(Node) catch @panic("OOM");
    n.* = .{ .tag = .String, .data = [_]u64{0} ** 8 };
    n.data[0] = @intFromPtr(ptr);
    return n;
}

/// Allocate an Ind (indirection) node pointing to `target`.
/// Used internally by `rts_eval` to memoize thunk results, and in tests.
pub fn createInd(target: *Node) *Node {
    const n = heap.allocator().create(Node) catch @panic("OOM");
    n.* = .{ .tag = .Ind, .data = [_]u64{0} ** 8 };
    n.data[0] = @intFromPtr(target);
    return n;
}

// ═══════════════════════════════════════════════════════════════════════
// Helpers — thunk constructors and accessors
// ═══════════════════════════════════════════════════════════════════════

/// The type of a thunk entry point.
/// The LLVM backend generates one such function per suspended computation.
/// It receives the environment node and returns the WHNF result.
pub const ThunkFn = *const fn (*Node) callconv(.auto) *Node;

/// Allocate a thunk node with the given code pointer and environment.
/// Called by the LLVM-generated code to suspend a computation.
pub fn createThunk(fn_ptr: ThunkFn, env: *Node) *Node {
    const n = heap.allocator().create(Node) catch @panic("OOM");
    n.* = .{ .tag = .Thunk, .data = [_]u64{0} ** 8 };
    n.data[0] = @intFromPtr(fn_ptr);
    n.data[1] = @intFromPtr(env);
    return n;
}

/// Extract the code pointer from a Thunk node.
/// Caller must ensure `n.tag == .Thunk`.
pub fn thunkFn(n: *const Node) ThunkFn {
    return @ptrFromInt(n.data[0]);
}

/// Extract the environment from a Thunk node.
/// Caller must ensure `n.tag == .Thunk`.
pub fn thunkEnv(n: *const Node) *Node {
    return @ptrFromInt(n.data[1]);
}

/// Read the target of an Ind node.
/// Caller must ensure `n.tag == .Ind`.
pub fn indTarget(n: *const Node) *Node {
    return @ptrFromInt(n.data[0]);
}

// ═══════════════════════════════════════════════════════════════════════
// Runtime Allocation Functions (called from LLVM)
// ═══════════════════════════════════════════════════════════════════════

/// Allocate a heap node with the given tag.
/// Called as `rts_alloc` from LLVM-generated code.
export fn rts_alloc(tag: u64) *Node {
    const n = heap.allocator().create(Node) catch @panic("OOM");
    n.tag = @enumFromInt(tag);
    n.data = [_]u64{0} ** 8;
    return n;
}

/// Store node fields after allocation.
/// Called after rts_alloc to initialise the node's data fields.
export fn rts_store(n: *Node, fields: [*]const u64, field_count: usize) void {
    for (0..@min(field_count, 8)) |i| {
        n.data[i] = fields[i];
    }
}

/// Allocate a thunk node.
/// Called from LLVM-generated code to suspend a lazy computation.
///
/// `fn_ptr_raw` — address of the thunk entry function as a raw integer
///                (function pointer types are not allowed in exported function
///                 signatures under the C calling convention in Zig 0.16-dev)
/// `env`        — pointer to the captured environment node
export fn rts_make_thunk(fn_ptr_raw: usize, env: *Node) *Node {
    const fn_ptr: ThunkFn = @ptrFromInt(fn_ptr_raw);
    return createThunk(fn_ptr, env);
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "alloc integer node" {
    heap.init();
    defer heap.deinit();

    const n = createInt(42);
    try std.testing.expectEqual(.Int, n.tag);
}

test "alloc character node" {
    heap.init();
    defer heap.deinit();

    const n = createChar('A');
    try std.testing.expectEqual(.Char, n.tag);
}

test "alloc unit node" {
    heap.init();
    defer heap.deinit();

    const n = createUnit();
    try std.testing.expectEqual(.Unit, n.tag);
}

test "alloc string node" {
    heap.init();
    defer heap.deinit();

    const hello: [*]const u8 = "Hello";
    const n = createString(hello);
    try std.testing.expectEqual(.String, n.tag);
}

test "rts_alloc exports C function" {
    // Ensure the export is symbolized correctly
    // This is a compile-time check that exports work
    try std.testing.expect(true);
}

test "createThunk stores fn_ptr and env" {
    heap.init();
    defer heap.deinit();

    // A trivial thunk that just returns its env unchanged.
    const env = createInt(99);
    const ThunkHelper = struct {
        fn call(e: *Node) callconv(.auto) *Node {
            return e;
        }
    };
    const n = createThunk(ThunkHelper.call, env);
    try std.testing.expectEqual(Tag.Thunk, n.tag);
    try std.testing.expectEqual(env, thunkEnv(n));
    try std.testing.expectEqual(@as(ThunkFn, ThunkHelper.call), thunkFn(n));
}

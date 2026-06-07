//! GC-swappable heap for the Rusholme runtime (issues #56, #70).
//!
//! All runtime heap operations go through the `GcAllocator` interface so
//! that the GC strategy can be swapped without touching the rest of the
//! RTS ("Phase 1 → Phase 2 is a swap, not a rewrite" — DESIGN.md):
//!
//!   - Phase 1 (current): `ArenaGc` — `std.heap.ArenaAllocator`-backed,
//!     `free`/`collect` are no-ops, memory grows until program exit.
//!   - Phase 2: Immix mark-region GC (#71, #72, #73) implementing the
//!     same interface.
//!   - Phase 3: ASAP-style static deallocation (#74) on top of Immix.
//!
//! The interface mirrors the `std.mem.Allocator` `{ptr, vtable}` idiom and
//! additionally exposes `collect`, `stats`, and root registration —
//! the hooks a tracing collector needs but a plain allocator does not.
//! See docs/decisions/284-zig-gc-immix-reference.md for the design study.

const std = @import("std");

// ═══════════════════════════════════════════════════════════════════════
// Allocation Statistics
// ═══════════════════════════════════════════════════════════════════════

/// Counters reported by `GcAllocator.stats()`.
pub const AllocStats = struct {
    /// Total bytes handed out by `alloc` since initialisation.
    bytes_allocated: u64 = 0,
    /// Total bytes reclaimed (by `free` or collection). Always 0 for
    /// the arena, which only frees in bulk at `deinit`.
    bytes_freed: u64 = 0,
    /// Number of collection cycles performed. Always 0 for the arena.
    collections: u64 = 0,
};

// ═══════════════════════════════════════════════════════════════════════
// GcAllocator Interface
// ═══════════════════════════════════════════════════════════════════════

/// GC-swappable heap interface (#70).
///
/// A fat pointer over a concrete heap implementation, mirroring
/// `std.mem.Allocator`'s `{ptr, vtable}` design. The runtime is
/// parameterised over this interface exclusively — no RTS module
/// may call `std.heap` directly (the only exception is a concrete
/// implementation's own backing store).
pub const GcAllocator = struct {
    ptr: *anyopaque,
    vtable: *const VTable,

    pub const VTable = struct {
        /// Allocate `len` bytes at the given alignment.
        /// Returns null on out-of-memory.
        alloc: *const fn (ctx: *anyopaque, len: usize, alignment: std.mem.Alignment) ?[*]u8,

        /// Release one allocation. A bulk-freeing implementation
        /// (arena) treats this as a no-op.
        free: *const fn (ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment) void,

        /// Trigger a collection cycle. A non-collecting implementation
        /// (arena) treats this as a no-op.
        collect: *const fn (ctx: *anyopaque) void,

        /// Report allocation statistics.
        stats: *const fn (ctx: *anyopaque) AllocStats,

        /// Register a root slot: a location holding a heap pointer
        /// (encoded as u64, see node.zig field encoding) that a tracing
        /// collector must treat as live. No-op for the arena.
        addRoot: *const fn (ctx: *anyopaque, slot: *u64) void,

        /// Remove a previously registered root slot. No-op for the arena.
        removeRoot: *const fn (ctx: *anyopaque, slot: *u64) void,
    };

    pub fn alloc(self: GcAllocator, len: usize, alignment: std.mem.Alignment) error{OutOfMemory}![*]u8 {
        return self.vtable.alloc(self.ptr, len, alignment) orelse error.OutOfMemory;
    }

    pub fn free(self: GcAllocator, memory: []u8, alignment: std.mem.Alignment) void {
        self.vtable.free(self.ptr, memory, alignment);
    }

    pub fn collect(self: GcAllocator) void {
        self.vtable.collect(self.ptr);
    }

    pub fn stats(self: GcAllocator) AllocStats {
        return self.vtable.stats(self.ptr);
    }

    pub fn addRoot(self: GcAllocator, slot: *u64) void {
        self.vtable.addRoot(self.ptr, slot);
    }

    pub fn removeRoot(self: GcAllocator, slot: *u64) void {
        self.vtable.removeRoot(self.ptr, slot);
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Phase 1: Arena Implementation
// ═══════════════════════════════════════════════════════════════════════

/// Phase-1 heap: `std.heap.ArenaAllocator`-backed, no collection.
/// `free`, `collect`, and root registration are no-ops; all memory is
/// released in bulk by `deinit`.
pub const ArenaGc = struct {
    arena: std.heap.ArenaAllocator,
    stats_data: AllocStats,

    pub fn init(backing: std.mem.Allocator) ArenaGc {
        return .{
            .arena = std.heap.ArenaAllocator.init(backing),
            .stats_data = .{},
        };
    }

    pub fn deinit(self: *ArenaGc) void {
        self.arena.deinit();
    }

    /// View this arena through the GC-swappable interface.
    pub fn gcAllocator(self: *ArenaGc) GcAllocator {
        return .{
            .ptr = self,
            .vtable = &gc_vtable,
        };
    }

    /// View this arena as a generic `std.mem.Allocator`, routed through
    /// the same accounting as the `GcAllocator` interface (so stats stay
    /// accurate for callers that need the generic API, e.g. `dupeZ`).
    pub fn allocator(self: *ArenaGc) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &std_vtable,
        };
    }

    const gc_vtable = GcAllocator.VTable{
        .alloc = allocImpl,
        .free = freeImpl,
        .collect = collectImpl,
        .stats = statsImpl,
        .addRoot = addRootImpl,
        .removeRoot = removeRootImpl,
    };

    const std_vtable = std.mem.Allocator.VTable{
        .alloc = stdAlloc,
        .resize = std.mem.Allocator.noResize,
        .remap = std.mem.Allocator.noRemap,
        .free = stdFree,
    };

    fn allocImpl(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        const self: *ArenaGc = @ptrCast(@alignCast(ctx));
        const raw = self.arena.allocator().rawAlloc(len, alignment, @returnAddress()) orelse return null;
        self.stats_data.bytes_allocated += len;
        return raw;
    }

    fn freeImpl(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment) void {
        // Arena frees in bulk at deinit; individual frees are no-ops.
        _ = ctx;
        _ = memory;
        _ = alignment;
    }

    fn collectImpl(ctx: *anyopaque) void {
        // No collector in Phase 1.
        _ = ctx;
    }

    fn statsImpl(ctx: *anyopaque) AllocStats {
        const self: *ArenaGc = @ptrCast(@alignCast(ctx));
        return self.stats_data;
    }

    fn addRootImpl(ctx: *anyopaque, slot: *u64) void {
        // The arena never traces, so roots are irrelevant.
        _ = ctx;
        _ = slot;
    }

    fn removeRootImpl(ctx: *anyopaque, slot: *u64) void {
        _ = ctx;
        _ = slot;
    }

    // ── std.mem.Allocator adapter ──────────────────────────────────────

    fn stdAlloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        _ = ret_addr;
        return allocImpl(ctx, len, alignment);
    }

    fn stdFree(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        _ = ret_addr;
        freeImpl(ctx, memory, alignment);
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Global Heap State
// ═══════════════════════════════════════════════════════════════════════

/// Global heap state for the running program.
///
/// The concrete implementation is selected here at startup; everything
/// else in the RTS sees only `GcAllocator` / `std.mem.Allocator`.
const State = struct {
    var arena_gc: ArenaGc = undefined;
    var initialized: bool = false;

    fn get() *ArenaGc {
        if (!initialized) {
            arena_gc = ArenaGc.init(std.heap.page_allocator);
            initialized = true;
        }
        return &arena_gc;
    }
};

/// Initialize the heap allocator.
pub fn init() void {
    _ = State.get();
}

/// Cleanup the heap allocator.
pub fn deinit() void {
    if (State.initialized) {
        State.arena_gc.deinit();
        State.initialized = false;
    }
}

/// Get the global heap as a generic allocator (routed through the
/// GC-swappable interface's accounting).
pub fn allocator() std.mem.Allocator {
    return State.get().allocator();
}

/// Get the global heap through the GC-swappable interface.
pub fn gcAllocator() GcAllocator {
    return State.get().gcAllocator();
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "init/deinit heap" {
    init();
    defer deinit();

    // Should be able to get both views of the global heap.
    _ = allocator();
    _ = gcAllocator();
}

test "ArenaGc: alloc through GcAllocator interface" {
    var arena_gc = ArenaGc.init(std.testing.allocator);
    defer arena_gc.deinit();
    const gc_alloc = arena_gc.gcAllocator();

    const mem = try gc_alloc.alloc(64, .of(u64));
    _ = mem;
    try std.testing.expectEqual(@as(u64, 64), gc_alloc.stats().bytes_allocated);
}

test "ArenaGc: free is a no-op, gc is a no-op" {
    var arena_gc = ArenaGc.init(std.testing.allocator);
    defer arena_gc.deinit();
    const gc_alloc = arena_gc.gcAllocator();

    const mem = try gc_alloc.alloc(32, .of(u64));
    gc_alloc.free(mem[0..32], .of(u64));
    gc_alloc.collect();

    const s = gc_alloc.stats();
    try std.testing.expectEqual(@as(u64, 0), s.bytes_freed);
    try std.testing.expectEqual(@as(u64, 0), s.collections);
}

test "ArenaGc: root registration is callable (no-op)" {
    var arena_gc = ArenaGc.init(std.testing.allocator);
    defer arena_gc.deinit();
    const gc_alloc = arena_gc.gcAllocator();

    var slot: u64 = 0;
    gc_alloc.addRoot(&slot);
    gc_alloc.removeRoot(&slot);
}

test "ArenaGc: std.mem.Allocator adapter routes through interface" {
    var arena_gc = ArenaGc.init(std.testing.allocator);
    defer arena_gc.deinit();

    const a = arena_gc.allocator();
    const buf = try a.dupe(u8, "hello");
    try std.testing.expectEqualStrings("hello", buf);
    try std.testing.expect(arena_gc.gcAllocator().stats().bytes_allocated >= 5);
}

test "ArenaGc: allocated memory is writable and aligned" {
    var arena_gc = ArenaGc.init(std.testing.allocator);
    defer arena_gc.deinit();
    const gc_alloc = arena_gc.gcAllocator();

    const mem = try gc_alloc.alloc(128, .of(u64));
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr(mem) % @alignOf(u64));
    @memset(mem[0..128], 0xAA);
    try std.testing.expectEqual(@as(u8, 0xAA), mem[127]);
}

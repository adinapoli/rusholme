//! GC-swappable heap for the Rusholme runtime (issues #56, #70, #776).
//!
//! All runtime heap operations go through the `GcAllocator` interface so
//! that the GC strategy can be swapped without touching the rest of the
//! RTS ("Phase 1 → Phase 2 is a swap, not a rewrite" — DESIGN.md):
//!
//!   - Phase 1: `ArenaGc` — `std.heap.ArenaAllocator`-backed,
//!     `free`/`collect` are no-ops, memory grows until program exit.
//!   - Phase 2: Immix mark-region GC (#71, #72, #73) implementing the
//!     same interface.
//!   - Phase 3: ASAP-style static deallocation (#74) on top of Immix.
//!
//! The interface mirrors the `std.mem.Allocator` `{ptr, vtable}` idiom and
//! additionally exposes `collect`, `stats`, and root registration —
//! the hooks a tracing collector needs but a plain allocator does not.
//! See docs/decisions/284-zig-gc-immix-reference.md for the design study.
//!
//! ## Backend selection (#776)
//!
//! The active backend is selected at startup via `rts_set_backend`,
//! which generated `main()` calls before any allocation. The call is
//! emitted by the GRIN→LLVM backend driven by the `rhc build --rts=…`
//! flag — `arena` is the implicit default (no call emitted), so any
//! pre-#776 binary continues to use the arena.

const std = @import("std");
const immix = @import("immix.zig");

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

    /// Bump-chunk size for the inline-allocation fast path. Each chunk
    /// is carved from the backing arena and then bump-allocated through
    /// the shared `rts_immix_cursor`/`rts_immix_limit` globals, so the
    /// LLVM inline-alloc fast path (#798) works under `--rts=arena` too.
    /// Only one heap backend is active per process, so sharing the
    /// globals with Immix is safe.
    pub const BUMP_CHUNK: usize = 1 << 20;

    pub fn init(backing: std.mem.Allocator) ArenaGc {
        // Reset the shared bump window: a previous heap instance (e.g.
        // an earlier unit test) may have left the globals pointing into
        // memory that died with its backing arena.
        rts_immix_cursor = 0;
        rts_immix_limit = 0;
        return .{
            .arena = std.heap.ArenaAllocator.init(backing),
            .stats_data = .{},
        };
    }

    pub fn deinit(self: *ArenaGc) void {
        // Invalidate the bump window — the chunks die with the arena.
        rts_immix_cursor = 0;
        rts_immix_limit = 0;
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
        // Bump fast path through the shared cursor/limit globals —
        // mirrors what LLVM-generated inline allocations do, so RTS-side
        // and generated-code allocations interleave in the same chunk.
        if (@intFromEnum(alignment) <= 3 and len <= BUMP_CHUNK) {
            const padded = (len + 7) & ~@as(usize, 7);
            if (rts_immix_cursor + padded > rts_immix_limit) {
                // Refill: carve a fresh chunk from the backing arena.
                const chunk = self.arena.allocator().rawAlloc(BUMP_CHUNK, .@"8", @returnAddress()) orelse return null;
                rts_immix_cursor = @intFromPtr(chunk);
                rts_immix_limit = @intFromPtr(chunk) + BUMP_CHUNK;
            }
            const p: [*]u8 = @ptrFromInt(rts_immix_cursor);
            rts_immix_cursor += padded;
            self.stats_data.bytes_allocated += padded;
            return p;
        }
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
// Shadow-Stack ABI (issue #780)
// ═══════════════════════════════════════════════════════════════════════
//
// Precise root tracking for the Immix collector. The LLVM-generated
// backend cooperates with the collector by spilling every live `*Node`
// SSA value into a global shadow-stack buffer at the point of its
// definition. The mark phase walks the buffer linearly and treats every
// entry as a candidate heap root. Lifetime of each entry is bounded by a
// `save`/`restore` pair emitted at function entry / exit, so popping
// works in O(1) regardless of how many `*Node` values a function
// produced.
//
// Conventions for the codegen contract:
//
//   * Each function emits `%saved = call i32 @rts_shadow_save()` as
//     part of its entry sequence (immediately after `rts_set_backend`,
//     before any allocation can fire).
//   * Each `*Node` SSA value is pushed by `call void @rts_shadow_push(i64 ptrtoint(value to i64))`
//     immediately at its definition site.
//   * Every return is preceded by `call void @rts_shadow_restore(i32 %saved)`,
//     which atomically pops all slots the current frame produced.
//
// All three entry points are no-ops if the program runs under
// `--rts=arena`: arena has no collector, so backend codegen omits the
// emission entirely. The runtime functions are still callable from any
// backend and remain cheap, but skipping the emission keeps generated
// IR lean.

/// Maximum number of live `*Node` slots that may be tracked
/// simultaneously across the entire program. Sized to comfortably hold
/// deeply nested Haskell call stacks (1M slots × 8 bytes = 8 MB —
/// matches the default Linux user-stack ceiling). Programs that
/// exceed this cap need a growable buffer; tracked as a follow-up.
const SHADOW_CAP: usize = 1 << 20;

/// Backing storage for the shadow stack. Each cell holds either
/// `@intFromPtr(*Node)` or `0` (for slots that have been logically
/// reserved but not yet stored — the collector treats null entries as
/// dead roots via `isHeapPointer`).
///
/// Exported as a C-visible symbol so the LLVM backend can address the
/// buffer directly from generated code (#788) instead of routing
/// every push through the `rts_shadow_push` C ABI call.
pub export var rts_shadow_buffer: [SHADOW_CAP]u64 = [_]u64{0} ** SHADOW_CAP;

/// Index of the next free slot. Read by the collector during the mark
/// phase: every slot in `rts_shadow_buffer[0..rts_shadow_top]` is a
/// candidate root.
///
/// Exported (see `rts_shadow_buffer`) so generated code can read and
/// bump it inline rather than going through a C call.
pub export var rts_shadow_top: u32 = 0;

// ═══════════════════════════════════════════════════════════════════════
// Immix Bump-Cursor Mirror (issue #798)
// ═══════════════════════════════════════════════════════════════════════
//
// Generated code under `--rts=immix` takes the bump path inline: load
// the current cursor, add the padded allocation size, compare against
// the limit, and either branch to a slow-path `rts_alloc` call (hole
// exhausted) or commit the new cursor and fall through. To make that
// possible the cursor + limit live as known C-ABI globals.
//
// `ImmixGc` still owns the canonical state internally — these globals
// are a mirror, updated on every mutation of `ImmixGc.cursor` /
// `.limit`. Successful inline bumps write the new cursor back to the
// mirror; `ImmixGc` reads the mirror the next time it touches its own
// state (e.g. when scanning for the next hole). Under `--rts=arena`
// they stay at zero until the first allocation, which overflows the
// limit and lets the slow path refill.
//
// Under `--rts=arena` the SAME globals serve as the bump window over
// the arena's current chunk (see `ArenaGc.BUMP_CHUNK`) — only one heap
// backend is active per process, so the two uses never overlap.
pub export var rts_immix_cursor: usize = 0;
pub export var rts_immix_limit: usize = 0;

/// Push `value` onto the shadow stack. Called at every `*Node` SSA
/// definition in LLVM-generated code; `value` is `@intFromPtr(*Node)`.
/// Panics on overflow — programs that exhaust the static capacity must
/// either bump `SHADOW_CAP` or move to a growable buffer (a follow-up
/// optimisation, since the current capacity is generous in practice).
pub export fn rts_shadow_push(value: u64) callconv(.c) void {
    if (rts_shadow_top >= SHADOW_CAP) {
        @panic("Immix: shadow-stack capacity exceeded");
    }
    rts_shadow_buffer[rts_shadow_top] = value;
    rts_shadow_top += 1;
}

/// Snapshot the current shadow-stack height. Called at the entry of any
/// function that produces `*Node` values; the returned value must be
/// paired with a `rts_shadow_restore` before every return so the slots
/// pushed during the call are released atomically.
pub export fn rts_shadow_save() callconv(.c) u32 {
    return rts_shadow_top;
}

/// Restore the shadow-stack height to a previously-saved value. All
/// slots pushed since the matching `rts_shadow_save` become dead
/// (logically popped). Sets the slots to `0` so the next collection
/// does not visit stale pointers — this is cheap in practice because
/// the released range is small (a single function's `*Node` SSAs).
pub export fn rts_shadow_restore(saved: u32) callconv(.c) void {
    if (saved <= rts_shadow_top) {
        @memset(rts_shadow_buffer[saved..rts_shadow_top], 0);
        rts_shadow_top = saved;
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Global Heap State
// ═══════════════════════════════════════════════════════════════════════

/// Backend identity. The numeric values are part of the
/// `rts_set_backend` C ABI — keep them stable; new backends append.
pub const RtsBackend = enum(u32) {
    arena = 0,
    immix = 1,
};

/// Global heap state for the running program.
///
/// The concrete backend is selected lazily on first allocation. The
/// LLVM-generated `main()` calls `rts_set_backend` (when built with a
/// non-default `--rts`) before any allocation so the desired backend
/// is recorded before `State.ensureInit` runs.
const State = struct {
    var selected: RtsBackend = .arena;
    var initialized: bool = false;
    var arena_gc: ArenaGc = undefined;
    var immix_gc: immix.ImmixGc = undefined;

    fn ensureInit() void {
        if (initialized) return;
        switch (selected) {
            .arena => arena_gc = ArenaGc.init(std.heap.page_allocator),
            .immix => {
                immix_gc = immix.ImmixGc.init(std.heap.page_allocator);
                // Auto-collect is now safe to enable by default: the
                // backend emits precise shadow-stack roots at every
                // `*Node` SSA definition (issue #780), so the collector
                // sees every live root rather than relying on the old
                // conservative `@frameAddress` scan.
                immix_gc.setAutoCollect(true);
            },
        }
        initialized = true;
    }

    fn deinitImpl() void {
        if (!initialized) return;
        switch (selected) {
            .arena => arena_gc.deinit(),
            .immix => immix_gc.deinit(),
        }
        initialized = false;
    }
};

/// Select the runtime backend before the first allocation. Called by
/// LLVM-generated `main()` when the program was built with a non-
/// default `--rts`. Calling this after the heap has already been
/// initialised is a no-op for the matching backend and a fatal error
/// for a different backend (no live-swap support).
pub export fn rts_set_backend(value: u32) callconv(.c) void {
    const requested: RtsBackend = switch (value) {
        @intFromEnum(RtsBackend.arena) => .arena,
        @intFromEnum(RtsBackend.immix) => .immix,
        else => @panic("rts_set_backend: unknown backend id"),
    };
    if (State.initialized) {
        if (State.selected != requested) {
            @panic("rts_set_backend called after heap was initialised");
        }
        return;
    }
    State.selected = requested;
}

/// Initialize the heap allocator. Optional — the heap initialises
/// itself on first allocation. Provided so callers (tests, the WASM
/// reactor entry) can pre-warm the heap.
pub fn init() void {
    State.ensureInit();
}

/// Cleanup the heap allocator.
pub fn deinit() void {
    State.deinitImpl();
}

/// Get the global heap as a generic allocator (routed through the
/// GC-swappable interface's accounting).
pub fn allocator() std.mem.Allocator {
    State.ensureInit();
    return switch (State.selected) {
        .arena => State.arena_gc.allocator(),
        .immix => State.immix_gc.allocator(),
    };
}

/// Get the global heap through the GC-swappable interface.
pub fn gcAllocator() GcAllocator {
    State.ensureInit();
    return switch (State.selected) {
        .arena => State.arena_gc.gcAllocator(),
        .immix => State.immix_gc.gcAllocator(),
    };
}

/// Currently-selected backend. Useful for diagnostics and tests.
pub fn currentBackend() RtsBackend {
    return State.selected;
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

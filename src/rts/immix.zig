//! Immix block/line allocator (issue #71, epic #14).
//!
//! Phase-2 heap implementing the Immix mark-region geometry from
//! Blackburn & McKinley, PLDI 2008 ("Immix: A Mark-Region Garbage
//! Collector"). See `docs/references/immix-gc.md` and the design study
//! `docs/decisions/284-zig-gc-immix-reference.md`.
//!
//! This issue (#71) lands the **allocation half** only:
//!
//!   * 32 KB blocks (aligned, requested from a child `std.mem.Allocator`),
//!     each subdivided into 128 B lines.
//!   * In-block side metadata: per-line use bytes, block state, free-line
//!     count, intrusive list pointer.
//!   * Bump-pointer allocation into the first free hole of the current
//!     block; when the current hole is exhausted, scan for the next hole;
//!     when the block is exhausted, take the next recyclable/free block
//!     or request a fresh one from the child allocator.
//!   * Block classification (`free`/`recyclable`/`full`) and recycling of
//!     blocks that have free lines.
//!   * Large-object space (LOS) for allocations larger than the in-block
//!     payload region — these bypass the block geometry entirely.
//!
//! Collection (mark/sweep, evacuation) and root scanning are explicitly
//! out of scope and land in #72/#73. Until those land, `free`, `collect`,
//! and root registration are no-ops, exactly like `ArenaGc`. As a result
//! the heap grows monotonically and blocks only ever transition
//! `free → recyclable → full` (never back).
//!
//! Conventions for the geometry mirror the paper unchanged: blocks are
//! 32 KB, lines are 128 B, blocks are mmap-aligned to their own size so
//! that `block_of(ptr) = ptr & ~(BLOCK_SIZE-1)`. The in-block header
//! occupies an integer number of lines at the start of the block; those
//! lines are pre-marked `used` and skipped during allocation.
//!
//! ## Mark-and-sweep collection (#72)
//!
//! `collect()` runs a classic Cheney-style trace from a set of roots,
//! marks every reachable `Node` (object granularity) and the lines it
//! occupies (line granularity), then re-files every block based on its
//! resulting line-mark count. Dead lines become free; dead large
//! objects are released to the child allocator.
//!
//! Object marks live in `Node.gc_flags` and store the *cycle id* at
//! which the node was last marked — `node.gc_flags == self.mark_id`
//! means "alive in this cycle". This avoids a separate reset pass: each
//! collection bumps `mark_id`, and stale ids automatically read as
//! unmarked.
//!
//! Roots come from two precise sources:
//!
//!   * Explicitly-registered slots via `addRoot`/`removeRoot` — used
//!     by the RTS itself and by unit tests that want deterministic
//!     control over the root set.
//!   * The **shadow stack** populated by the LLVM backend (#780): the
//!     generated code calls `rts_shadow_push` at every `*Node` SSA
//!     definition, brackets each function body with
//!     `rts_shadow_save`/`rts_shadow_restore`, and the collector walks
//!     the global slot buffer via `markFromShadowStack`. This is the
//!     long-term precise root mechanism — every live `*Node` reachable
//!     from generated code is rooted by construction.
//!
//! Object-body tracing is **precise** for built-in tags whose layout
//! the RTS knows (`Unit`/`Int`/`Char`/`String` carry no pointers;
//! `Ind` has exactly one pointer at `field[0]`), and **conservative**
//! within the remaining tag classes (`Thunk`, `Closure`, `Data`,
//! user-defined constructors) where the RTS does not yet have a
//! per-tag pointer mask. Each field slot in those classes is treated
//! as a candidate pointer; only words that pass `isHeapPointer`
//! (alignment, falls inside an Immix block's payload region or an LOS
//! slab) are followed. Precise per-constructor masks are tracked
//! separately as a backend deliverable.

const std = @import("std");
const heap = @import("heap.zig");
const nodemod = @import("node.zig");
const Node = nodemod.Node;

// ═══════════════════════════════════════════════════════════════════════
// Geometry
// ═══════════════════════════════════════════════════════════════════════

/// Block size in bytes (Immix paper: 32 KB).
pub const BLOCK_SIZE: usize = 32 * 1024;

/// Line size in bytes (Immix paper: 128 B).
pub const LINE_SIZE: usize = 128;

/// Total lines per block (256 for the canonical configuration).
pub const LINES_PER_BLOCK: usize = BLOCK_SIZE / LINE_SIZE;

comptime {
    std.debug.assert(BLOCK_SIZE % LINE_SIZE == 0);
    std.debug.assert(std.math.isPowerOfTwo(BLOCK_SIZE));
}

/// Block classification. Used to decide which list a block lives on
/// after a collection (or, in this issue, after allocation fills it).
pub const BlockState = enum(u8) {
    /// All lines free. Ready to be handed out cold.
    free,
    /// At least one line free and at least one line used.
    recyclable,
    /// No free lines remain; will not satisfy new allocations until a
    /// future collection (#72) reclaims lines.
    full,
};

// ═══════════════════════════════════════════════════════════════════════
// Block Layout
// ═══════════════════════════════════════════════════════════════════════

/// In-block header. Lives at offset 0 of every 32 KB block, padded out
/// to an integer number of lines so the payload begins on a line
/// boundary. Lines covering the header are pre-marked `used` and are
/// never returned to the allocator.
pub const BlockHeader = struct {
    /// Per-line use byte. `0` = free, non-zero = used.
    /// A byte (rather than a bit) keeps the metadata trivial to update;
    /// the small space cost (256 B / 32 KB ≈ 0.78%) is acceptable for a
    /// first implementation and matches the paper's exposition.
    line_marks: [LINES_PER_BLOCK]u8,

    /// Number of currently-free lines in this block (header lines
    /// excluded — they are never counted as free).
    free_lines: u16,

    /// Block classification, kept in sync with `free_lines` and the
    /// allocator's bump cursor.
    state: BlockState,

    /// Intrusive next pointer for block lists (free / recyclable / full /
    /// all-blocks). A single field is sufficient because each block is
    /// on exactly one classification list at a time.
    next: ?*BlockHeader,

    /// Intrusive next pointer for the "all blocks" list, used by
    /// `deinit` to return every block to the child allocator regardless
    /// of classification.
    all_next: ?*BlockHeader,

    pub fn payloadStart(self: *BlockHeader) [*]u8 {
        const base: [*]u8 = @ptrCast(self);
        return base + HEADER_BYTES;
    }

    pub fn payloadEnd(self: *BlockHeader) [*]u8 {
        const base: [*]u8 = @ptrCast(self);
        return base + BLOCK_SIZE;
    }

    /// Line index for a pointer that lives inside this block.
    pub fn lineIndexOf(self: *BlockHeader, ptr: usize) usize {
        const base = @intFromPtr(self);
        std.debug.assert(ptr >= base and ptr < base + BLOCK_SIZE);
        return (ptr - base) / LINE_SIZE;
    }
};

/// Bytes occupied by the in-block header, rounded up to a line boundary.
pub const HEADER_BYTES: usize = std.mem.alignForward(
    usize,
    @sizeOf(BlockHeader),
    LINE_SIZE,
);

/// Number of lines consumed by the in-block header.
pub const HEADER_LINES: usize = HEADER_BYTES / LINE_SIZE;

/// Lines available to the mutator per block.
pub const PAYLOAD_LINES: usize = LINES_PER_BLOCK - HEADER_LINES;

/// Bytes available to the mutator per block.
pub const PAYLOAD_BYTES: usize = PAYLOAD_LINES * LINE_SIZE;

/// Maximum allocation size that can live inside a block. Anything larger
/// is routed to the large-object space.
pub const MAX_BLOCK_ALLOC: usize = PAYLOAD_BYTES;

/// Initial heap budget for the auto-collect trigger (#781). Chosen so
/// short-running programs do not pay the cost of a collection at all
/// (8 blocks ≈ 256 KiB of live data), while long-running programs see
/// their first collection promptly after passing that threshold. The
/// budget is re-tuned upward after each cycle proportional to the
/// post-collection live size.
pub const INITIAL_TARGET_BLOCKS: u64 = 8;

comptime {
    // The header must fit in a small, fixed number of lines, leaving the
    // overwhelming majority of the block as payload. If this assertion
    // ever trips it means the header grew and we need to reconsider the
    // metadata layout.
    std.debug.assert(HEADER_LINES <= 4);
}

// ═══════════════════════════════════════════════════════════════════════
// Per-Constructor Pointer-Mask Table (issue #779)
// ═══════════════════════════════════════════════════════════════════════
//
// Backend-emitted side table mapping each constructor's tag
// discriminant to a 64-bit bitmask over its field slots: bit `i` set
// ⇔ field `i` holds a `*Node` (the only thing the collector needs to
// trace). The backend calls `rts_set_pointer_mask(tag, mask)` once per
// known constructor at program start; the collector consults the
// table to replace the conservative scan over `Thunk`/`Closure`/
// `Data` field arrays with precise tracing.
//
// Built-in tags (`Unit`/`Int`/`Char`/`String`/`Ind`) have hard-coded
// semantics in `drainMarkWorklist` and are not driven by this table.
// Tags whose mask has never been set carry the sentinel `UNKNOWN_MASK`
// and the collector falls back to the legacy conservative scan — this
// keeps the heap safe in the presence of newly-introduced tags whose
// backend code has not yet been updated.

/// Maximum supported tag discriminant. User-defined constructor
/// discriminants start at `0x1000` (4096) and grow sequentially, so the
/// table must be large enough to cover the program's entire registry.
/// Sized at 16K slots × 8 bytes = 128 KB resident — covers ~12K user
/// constructors above the built-in range, more than any realistic
/// Haskell program; bump if a real program ever hits it.
pub const MAX_TAG_ID: usize = 16 * 1024;

/// Sentinel mask written into a slot the backend never explicitly
/// registered. The collector reads this as "unknown layout → fall
/// back to the conservative scan." Any constructor whose 64 fields
/// are all genuine pointers would collide with this sentinel; that
/// is well beyond the field-count limit (Node header packs n_fields
/// as u32, but constructors with > 64 pointer fields are unheard of
/// in real Haskell).
pub const UNKNOWN_MASK: u64 = ~@as(u64, 0);

/// The mask table itself. Exported as a C-visible symbol so the
/// generated code (and future inline emission, mirroring #788) can
/// address it directly.
pub export var rts_pointer_masks: [MAX_TAG_ID]u64 = [_]u64{UNKNOWN_MASK} ** MAX_TAG_ID;

/// Backend-callable setter for a single tag's mask. Called once per
/// constructor from the LLVM-generated `main` (or REPL entry) before
/// any user code runs.
pub export fn rts_set_pointer_mask(tag: u64, mask: u64) callconv(.c) void {
    if (tag < MAX_TAG_ID) {
        rts_pointer_masks[@intCast(tag)] = mask;
    }
}

/// Look up the mask for `tag`. Returns `UNKNOWN_MASK` for tags the
/// backend hasn't registered (built-ins included — they go through
/// the special-case dispatch instead).
pub fn pointerMaskFor(tag: u64) u64 {
    if (tag < MAX_TAG_ID) return rts_pointer_masks[@intCast(tag)];
    return UNKNOWN_MASK;
}

// ═══════════════════════════════════════════════════════════════════════
// Large Object Space
// ═══════════════════════════════════════════════════════════════════════

/// Header for an allocation that bypasses the block/line geometry.
///
/// Large objects are simply individual child-allocator slabs threaded
/// onto a list so `deinit` can release them. They carry their own length
/// and alignment so the slab can be returned exactly as it was acquired.
const LargeObject = struct {
    next: ?*LargeObject,
    /// Total slab size including this header and any alignment padding.
    slab_len: usize,
    /// Raw pointer returned by the child allocator. Distinct from the
    /// header address when alignment padding was needed.
    slab_base: [*]u8,
    /// Payload alignment as requested by the caller.
    alignment: std.mem.Alignment,
    /// Length of the payload returned to the caller.
    payload_len: usize,
    /// Payload pointer handed to the caller. Threaded so `containsLarge`
    /// can answer pointer queries cheaply during tests.
    payload: [*]u8,
};

// ═══════════════════════════════════════════════════════════════════════
// ImmixGc
// ═══════════════════════════════════════════════════════════════════════

/// Phase-2 Immix heap: block/line bump allocator + mark-region collector
/// over a child allocator.
///
/// `#71` landed the allocation half; `#72` adds collection: `collect()`
/// runs a mark phase from explicit + (optionally) conservative roots,
/// then sweeps blocks at line granularity and releases unreachable
/// large objects. Defragmentation (#73) is still out of scope — the
/// collector is strictly non-moving.
pub const ImmixGc = struct {
    /// Source of 32 KB blocks and LOS slabs.
    child: std.mem.Allocator,

    // ── Block lists ───────────────────────────────────────────────────
    /// Blocks with no live lines, immediately ready for cold bumping.
    free_blocks: ?*BlockHeader = null,
    /// Blocks with at least one free line and at least one used line.
    recyclable_blocks: ?*BlockHeader = null,
    /// Blocks with no free lines remaining.
    full_blocks: ?*BlockHeader = null,
    /// Singly-linked list of every block this heap owns, used by
    /// `deinit` to return them to the child allocator and by `collect`
    /// to iterate the heap regardless of current classification.
    all_blocks: ?*BlockHeader = null,

    // ── Current bump region (small-object cursor) ─────────────────────
    /// Block currently being bumped into for small (≤ `LINE_SIZE`)
    /// allocations. `null` until the first allocation that needs a
    /// block. Small objects walk through holes — including the
    /// fragments left after a sweep — via `advanceToHole`.
    current_block: ?*BlockHeader = null,
    /// Next byte to hand out for small allocations (absolute pointer
    /// as `usize`).
    cursor: usize = 0,
    /// One past the last byte of the current small-cursor hole.
    limit: usize = 0,

    // ── Overflow bump region (medium-object cursor, #777) ─────────────
    /// Block currently being bumped into for medium (> `LINE_SIZE`,
    /// ≤ block) allocations. Per Blackburn & McKinley §2 the overflow
    /// cursor *prefers fresh blocks* — medium objects never scan for
    /// holes inside a partially-occupied block, so the small fragments
    /// in recyclable blocks remain available to small allocations
    /// instead of being wasted by an oversized header. When the
    /// overflow region is exhausted the block is reclassified
    /// (recyclable / full) and a fresh one is requested.
    overflow_block: ?*BlockHeader = null,
    /// Next byte to hand out for medium allocations.
    overflow_cursor: usize = 0,
    /// One past the last byte of the overflow region.
    overflow_limit: usize = 0,

    // ── Large object space ────────────────────────────────────────────
    large_objects: ?*LargeObject = null,

    // ── Collector state ───────────────────────────────────────────────
    /// Cycle id stamped onto `Node.gc_flags` to indicate liveness in
    /// the current collection. `0` means "no collection has run yet";
    /// freshly-allocated nodes carry this value and are treated as
    /// dead by a collection that hasn't traced them yet — callers are
    /// expected to root them via `addRoot` (or place them somewhere
    /// reachable from a registered root) before invoking `collect`.
    mark_id: u32 = 0,
    /// Roots registered via `addRoot`. Each entry is a pointer to a
    /// slot that holds a `*Node` encoded as `u64` (`@intFromPtr`).
    /// `collect` walks this list precisely; any non-null slot is
    /// followed unconditionally regardless of `isHeapPointer`.
    roots: std.ArrayList(*u64) = .empty,

    // ── Stats ─────────────────────────────────────────────────────────
    stats_data: heap.AllocStats = .{},
    /// Number of blocks owned by this heap (small + LOS counts are
    /// separate; this is the count of 32 KB block allocations).
    blocks_allocated: u64 = 0,
    /// Number of LOS slabs owned by this heap.
    large_objects_allocated: u64 = 0,

    // ── Auto-collect trigger (#781) ──────────────────────────────────
    /// When `true`, the allocator calls `collect()` automatically once
    /// the live block count is about to exceed `target_blocks`. Off by
    /// default for the in-process tests that go through this struct
    /// directly; the global heap (`heap.gcAllocator()`) flips it on at
    /// init time because generated code emits shadow-stack roots at
    /// every `*Node` SSA definition (#780), so collection from inside
    /// the allocator path always sees the full live root set. See
    /// issue #781 and the docstring on `setAutoCollect`.
    auto_collect_enabled: bool = false,
    /// Live block budget. Once `blocks_allocated >= target_blocks` the
    /// allocator runs a collection before requesting fresh memory; the
    /// budget is then re-tuned to `max(min_target_blocks, 2 × live)`.
    target_blocks: u64 = INITIAL_TARGET_BLOCKS,
    /// Floor for the auto-tuned budget — collections never fire more
    /// often than once per `min_target_blocks` allocations.
    min_target_blocks: u64 = INITIAL_TARGET_BLOCKS,
    /// Guard: while collect() is running we must not recursively try
    /// to collect again from inside the mark phase's child-allocator
    /// path (the worklist is backed by `self.child`, not this heap).
    in_collect: bool = false,

    pub fn init(child: std.mem.Allocator) ImmixGc {
        return .{ .child = child };
    }

    /// Enable or disable automatic collection from the allocation path
    /// (#781). When enabled, the allocator runs `collect()` before
    /// requesting a fresh block once the live block count crosses
    /// `target_blocks`, then re-tunes the budget to twice the
    /// post-collection live size (floored at `min_target_blocks`).
    ///
    /// **Safety**: enabling this on a heap with no roots reaps every
    /// live object. Compiled programs are safe by construction — the
    /// LLVM backend emits precise shadow-stack roots at every `*Node`
    /// SSA definition (#780). In-process callers (tests, embedders)
    /// must register their roots via `addRoot` (or push them onto the
    /// shadow stack via `heap.rts_shadow_push`) before enabling.
    pub fn setAutoCollect(self: *ImmixGc, enabled: bool) void {
        self.auto_collect_enabled = enabled;
    }

    /// Set the heap budget (initial value of `target_blocks`). Useful
    /// for tests that want collections to fire deterministically after
    /// a known number of blocks.
    pub fn setTargetBlocks(self: *ImmixGc, target: u64) void {
        self.target_blocks = target;
        self.min_target_blocks = target;
    }

    pub fn deinit(self: *ImmixGc) void {
        // Walk the master list to return every block, regardless of
        // which classification list it currently lives on. The block
        // pointer is itself the start of the 32 KB allocation, aligned
        // to BLOCK_SIZE — reconstruct the original aligned slice so
        // the child allocator's `free` sees the same shape it returned.
        var b = self.all_blocks;
        while (b) |block| {
            const next = block.all_next;
            const raw: [*]align(BLOCK_SIZE) u8 = @ptrCast(@alignCast(block));
            const slice: []align(BLOCK_SIZE) u8 = raw[0..BLOCK_SIZE];
            self.child.free(slice);
            b = next;
        }
        self.all_blocks = null;
        self.free_blocks = null;
        self.recyclable_blocks = null;
        self.full_blocks = null;
        self.current_block = null;
        self.cursor = 0;
        self.limit = 0;
        self.overflow_block = null;
        self.overflow_cursor = 0;
        self.overflow_limit = 0;

        var l = self.large_objects;
        while (l) |lo| {
            const next = lo.next;
            const raw: [*]align(@alignOf(LargeObject)) u8 = @ptrCast(@alignCast(lo.slab_base));
            const slice: []align(@alignOf(LargeObject)) u8 = raw[0..lo.slab_len];
            self.child.free(slice);
            l = next;
        }
        self.large_objects = null;

        self.roots.deinit(self.child);
    }

    /// View this heap through the GC-swappable interface (see
    /// `heap.GcAllocator`). The arena impl already uses the same shape;
    /// `node.zig`/`rts_alloc` sees no difference between the two.
    pub fn gcAllocator(self: *ImmixGc) heap.GcAllocator {
        return .{ .ptr = self, .vtable = &gc_vtable };
    }

    /// Generic `std.mem.Allocator` adapter for callers that need the
    /// standard-library API (e.g. `dupeZ`). Stats are routed through the
    /// same accounting as the `GcAllocator` view.
    pub fn allocator(self: *ImmixGc) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &std_vtable };
    }

    const gc_vtable = heap.GcAllocator.VTable{
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

    // ── GcAllocator vtable ────────────────────────────────────────────

    fn allocImpl(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        const self: *ImmixGc = @ptrCast(@alignCast(ctx));
        return self.alloc(len, alignment);
    }

    fn freeImpl(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment) void {
        // Per-object free is reclaimed in bulk by collection (#72), not
        // by the mutator. Matches `ArenaGc` semantics.
        _ = ctx;
        _ = memory;
        _ = alignment;
    }

    fn collectImpl(ctx: *anyopaque) void {
        const self: *ImmixGc = @ptrCast(@alignCast(ctx));
        self.collect();
    }

    fn statsImpl(ctx: *anyopaque) heap.AllocStats {
        const self: *ImmixGc = @ptrCast(@alignCast(ctx));
        return self.stats_data;
    }

    fn addRootImpl(ctx: *anyopaque, slot: *u64) void {
        const self: *ImmixGc = @ptrCast(@alignCast(ctx));
        // Append is allocator-fallible; in practice the root set is
        // tiny and the child allocator is the same one the heap uses,
        // so OOM here is a hard error.
        self.roots.append(self.child, slot) catch @panic("Immix: out of memory while registering root");
    }

    fn removeRootImpl(ctx: *anyopaque, slot: *u64) void {
        const self: *ImmixGc = @ptrCast(@alignCast(ctx));
        // Linear scan: roots are removed in roughly LIFO order during
        // normal execution (stack frames unwind), so the matching slot
        // is usually near the end of the list.
        var i: usize = self.roots.items.len;
        while (i > 0) {
            i -= 1;
            if (self.roots.items[i] == slot) {
                _ = self.roots.swapRemove(i);
                return;
            }
        }
    }

    // ── std.mem.Allocator adapter ─────────────────────────────────────

    fn stdAlloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        _ = ret_addr;
        return allocImpl(ctx, len, alignment);
    }

    fn stdFree(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        _ = ret_addr;
        freeImpl(ctx, memory, alignment);
    }

    // ── Allocation core ───────────────────────────────────────────────

    fn alloc(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        if (len == 0) return null;

        // Objects larger than what a single block can hold bypass the
        // line geometry entirely and live in the large-object space.
        if (len > MAX_BLOCK_ALLOC) return self.allocLarge(len, alignment);

        // Split the bump path by object size (#777). Small objects
        // (≤ `LINE_SIZE`) walk through every hole, including the
        // small fragments in recyclable blocks; medium objects bypass
        // recyclable holes entirely and bump into a dedicated
        // fresh-block cursor.
        if (len <= LINE_SIZE) {
            return self.allocSmall(len, alignment);
        }
        return self.allocMedium(len, alignment);
    }

    /// Small-object bump path (≤ `LINE_SIZE`). Tries the current
    /// block, then walks the recyclable list, then triggers auto-
    /// collect, then requests a fresh block.
    fn allocSmall(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        if (self.tryAllocInCurrent(len, alignment)) |p| return p;
        if (self.tryAllocInRecyclable(len, alignment)) |p| return p;

        // Recycle pool exhausted (or every hole is too small for this
        // request). If the auto-collect trigger is armed and the heap
        // budget has been crossed, run a collection and try the
        // recyclable pool again — collect frees up lines so the second
        // pass usually fits.
        if (self.auto_collect_enabled and !self.in_collect and
            self.blocks_allocated >= self.target_blocks)
        {
            self.collect();
            self.retuneBudgetAfterCollect();
            if (self.tryAllocInCurrent(len, alignment)) |p| return p;
            if (self.tryAllocInRecyclable(len, alignment)) |p| return p;
        }

        // Last resort: request a fresh block from the child allocator.
        if (self.newBlock()) |b| {
            self.attachBlockAsCurrent(b);
            if (self.tryAllocInCurrent(len, alignment)) |p| return p;
        }
        return null;
    }

    /// Medium-object bump path (> `LINE_SIZE`, ≤ block). Uses a
    /// dedicated overflow cursor that always bumps into a fresh block
    /// — recyclable-block holes are left for small allocations even if
    /// they would technically fit a medium object, so the recycled
    /// space isn't sacrificed to oversized headers.
    fn allocMedium(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        if (self.bumpInOverflowHole(len, alignment)) |p| {
            self.stats_data.bytes_allocated += len;
            return p;
        }

        // Overflow region exhausted — file the block (its remaining
        // small holes are still useful to `allocSmall`) and grab a
        // fresh one.
        self.retireOverflowBlock();

        if (self.auto_collect_enabled and !self.in_collect and
            self.blocks_allocated >= self.target_blocks)
        {
            self.collect();
            self.retuneBudgetAfterCollect();
            // Collect may have produced fresh blocks via reclassification;
            // re-try the overflow bump on whatever's queued for us.
            if (self.bumpInOverflowHole(len, alignment)) |p| {
                self.stats_data.bytes_allocated += len;
                return p;
            }
        }

        if (self.newBlock()) |b| {
            self.attachBlockAsOverflow(b);
            if (self.bumpInOverflowHole(len, alignment)) |p| {
                self.stats_data.bytes_allocated += len;
                return p;
            }
        }
        return null;
    }

    /// Try to satisfy a request from the current block — first by
    /// bumping in the active hole, then by scanning forward through
    /// any remaining free holes inside the same block. Returns null
    /// without mutating state if no hole fits.
    fn tryAllocInCurrent(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        if (self.current_block == null) return null;
        if (self.bumpInCurrentHole(len, alignment)) |p| {
            self.stats_data.bytes_allocated += len;
            return p;
        }
        while (self.advanceToHole(len, alignment)) {
            if (self.bumpInCurrentHole(len, alignment)) |p| {
                self.stats_data.bytes_allocated += len;
                return p;
            }
        }
        return null;
    }

    /// Walk the recyclable and free block lists looking for one that
    /// can satisfy the request. Each block is visited at most once —
    /// blocks whose holes don't fit are reclassified onto the original
    /// list and the search continues. Returns null when no eligible
    /// block remains.
    fn tryAllocInRecyclable(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        const initial_blocks = self.blocks_allocated;
        var visited: u64 = 0;
        while (visited < initial_blocks) : (visited += 1) {
            const next = self.popReusableBlock() orelse return null;
            self.attachBlockAsCurrent(next);
            if (self.tryAllocInCurrent(len, alignment)) |p| return p;
        }
        return null;
    }

    /// Detach a block from `recyclable_blocks` (preferred) or
    /// `free_blocks`, returning it ready to be made current. Returns
    /// null if both lists are empty.
    fn popReusableBlock(self: *ImmixGc) ?*BlockHeader {
        if (self.recyclable_blocks) |b| {
            self.recyclable_blocks = b.next;
            b.next = null;
            return b;
        }
        if (self.free_blocks) |b| {
            self.free_blocks = b.next;
            b.next = null;
            return b;
        }
        return null;
    }

    fn retuneBudgetAfterCollect(self: *ImmixGc) void {
        var live_blocks: u64 = 0;
        var b = self.full_blocks;
        while (b) |bb| : (b = bb.next) live_blocks += 1;
        b = self.recyclable_blocks;
        while (b) |bb| : (b = bb.next) live_blocks += 1;
        self.target_blocks = @max(self.min_target_blocks, live_blocks * 2);
    }

    /// Try to allocate `len` bytes from the current hole. Returns the
    /// pointer on success and leaves `self.cursor` advanced; returns
    /// null without mutating state on failure.
    fn bumpInCurrentHole(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        const aligned = alignment.forward(self.cursor);
        const end = aligned + len;
        if (end > self.limit) return null;
        self.cursor = end;
        markLinesUsed(self.current_block.?, aligned, end);
        return @ptrFromInt(aligned);
    }

    /// Walk forward from the current cursor looking for the next run of
    /// free lines large enough to hold an allocation of size `len` at
    /// the requested alignment. Returns true if a hole was found and
    /// `cursor`/`limit` were updated; false if the block is exhausted.
    fn advanceToHole(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) bool {
        const block = self.current_block orelse return false;
        const base = @intFromPtr(block);

        // Start scanning at the line after the current limit (the line
        // containing `cursor` is occupied by the previous bump, even if
        // the bytes themselves aren't all used — Immix tracks liveness
        // at line granularity).
        var line = if (self.limit == 0)
            HEADER_LINES
        else
            (self.limit - base) / LINE_SIZE;

        while (line < LINES_PER_BLOCK) {
            // Skip used lines.
            if (block.line_marks[line] != 0) {
                line += 1;
                continue;
            }
            // Found the start of a free run; extend it as far as possible.
            const hole_start_line = line;
            while (line < LINES_PER_BLOCK and block.line_marks[line] == 0) {
                line += 1;
            }
            const hole_end_line = line;
            const hole_start = base + hole_start_line * LINE_SIZE;
            const hole_end = base + hole_end_line * LINE_SIZE;
            const aligned = alignment.forward(hole_start);
            if (aligned + len <= hole_end) {
                self.cursor = hole_start;
                self.limit = hole_end;
                return true;
            }
            // Hole too small (or alignment padding pushed past it); keep
            // scanning for the next one.
        }
        return false;
    }

    /// Detach the current block (moving it to a classification list)
    /// and attach a fresh block as the new bump target. The cursor is
    /// positioned at the payload boundary with an empty hole; the
    /// surrounding `alloc` loop calls `advanceToHole` to locate the
    /// first actually-free hole. This unifies the fresh-block and
    /// recyclable-block paths: a fresh block's first hole spans the
    /// whole payload, and a recyclable block's first hole sits between
    /// existing live lines.
    fn attachBlockAsCurrent(self: *ImmixGc, block: *BlockHeader) void {
        if (self.current_block) |old| {
            // Reclassify the previous block based on whether any free
            // lines remain after the bump.
            self.classifyAndFile(old);
        }
        self.current_block = block;
        const base = @intFromPtr(block);
        self.cursor = base + HEADER_BYTES;
        self.limit = base + HEADER_BYTES;
    }

    /// Bump-allocate `len` bytes out of the overflow region. Unlike
    /// the small cursor this never scans for additional holes inside
    /// the same block — overflow allocations only ever consume the
    /// contiguous tail of a fresh block, leaving recycled fragments
    /// to the small cursor.
    fn bumpInOverflowHole(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        if (self.overflow_block == null) return null;
        const aligned = alignment.forward(self.overflow_cursor);
        const end = aligned + len;
        if (end > self.overflow_limit) return null;
        self.overflow_cursor = end;
        markLinesUsed(self.overflow_block.?, aligned, end);
        return @ptrFromInt(aligned);
    }

    /// Install `block` as the overflow bump target. The whole payload
    /// is fresh, so the overflow region spans the block end-to-end.
    /// Any previous overflow block is reclassified first so its
    /// remaining small fragments become visible to `allocSmall`.
    fn attachBlockAsOverflow(self: *ImmixGc, block: *BlockHeader) void {
        self.retireOverflowBlock();
        self.overflow_block = block;
        const base = @intFromPtr(block);
        self.overflow_cursor = base + HEADER_BYTES;
        self.overflow_limit = base + BLOCK_SIZE;
    }

    /// File the current overflow block back onto a classification list
    /// (recyclable / full / free) and reset the overflow cursor pair.
    /// Called when the overflow region is exhausted or before the
    /// collector rewrites every block's classification.
    fn retireOverflowBlock(self: *ImmixGc) void {
        if (self.overflow_block) |old| {
            self.classifyAndFile(old);
        }
        self.overflow_block = null;
        self.overflow_cursor = 0;
        self.overflow_limit = 0;
    }

    fn classifyAndFile(self: *ImmixGc, block: *BlockHeader) void {
        // Recompute free_lines from the line-mark array (the bump path
        // only marks lines it touches, so this is the source of truth).
        var free: u16 = 0;
        for (block.line_marks[HEADER_LINES..]) |m| {
            if (m == 0) free += 1;
        }
        block.free_lines = free;
        if (free == 0) {
            block.state = .full;
            block.next = self.full_blocks;
            self.full_blocks = block;
        } else if (free == PAYLOAD_LINES) {
            block.state = .free;
            block.next = self.free_blocks;
            self.free_blocks = block;
        } else {
            block.state = .recyclable;
            block.next = self.recyclable_blocks;
            self.recyclable_blocks = block;
        }
    }


    /// Request a brand new 32 KB block, aligned to its own size, from
    /// the child allocator. Initialises the header and threads it onto
    /// the master `all_blocks` list.
    fn newBlock(self: *ImmixGc) ?*BlockHeader {
        const raw = self.child.alignedAlloc(
            u8,
            std.mem.Alignment.fromByteUnits(BLOCK_SIZE),
            BLOCK_SIZE,
        ) catch return null;
        const block: *BlockHeader = @ptrCast(@alignCast(raw.ptr));
        block.* = .{
            .line_marks = [_]u8{0} ** LINES_PER_BLOCK,
            .free_lines = @intCast(PAYLOAD_LINES),
            .state = .free,
            .next = null,
            .all_next = self.all_blocks,
        };
        // Pre-mark header lines as used so the allocator never tries to
        // hand them out.
        for (block.line_marks[0..HEADER_LINES]) |*m| m.* = 1;
        self.all_blocks = block;
        self.blocks_allocated += 1;
        return block;
    }

    fn allocLarge(self: *ImmixGc, len: usize, alignment: std.mem.Alignment) ?[*]u8 {
        // We need a slab that holds: the LargeObject header, alignment
        // padding so the payload sits on the requested boundary, and
        // the payload itself. The header is `@alignOf(LargeObject)`-
        // aligned (we ask the child for that alignment), then the
        // payload is hand-aligned within the slab.
        const lo_align = @alignOf(LargeObject);
        const align_bytes = alignment.toByteUnits();
        const slab_len = @sizeOf(LargeObject) + align_bytes + len;
        const raw = self.child.alignedAlloc(
            u8,
            std.mem.Alignment.fromByteUnits(lo_align),
            slab_len,
        ) catch return null;

        const header_end = @intFromPtr(raw.ptr) + @sizeOf(LargeObject);
        const payload_addr = alignment.forward(header_end);
        std.debug.assert(payload_addr + len <= @intFromPtr(raw.ptr) + slab_len);

        const lo: *LargeObject = @ptrCast(@alignCast(raw.ptr));
        lo.* = .{
            .next = self.large_objects,
            .slab_len = slab_len,
            .slab_base = raw.ptr,
            .alignment = alignment,
            .payload_len = len,
            .payload = @ptrFromInt(payload_addr),
        };
        self.large_objects = lo;
        self.large_objects_allocated += 1;
        self.stats_data.bytes_allocated += len;
        return lo.payload;
    }

    // ── Collection ────────────────────────────────────────────────────

    /// Run a single mark-and-sweep cycle.
    ///
    /// Sequence:
    ///   1. Bump `mark_id` so stale per-node marks read as unmarked.
    ///   2. Reset every block's payload line marks to free; header
    ///      lines stay used.
    ///   3. Trace from every precise root: explicit
    ///      `addRoot`-registered slots and the shadow-stack buffer
    ///      populated by `rts_shadow_push` from generated code (#780).
    ///      Each reachable node has its `gc_flags` set to `mark_id` and
    ///      the lines it spans set to used.
    ///   4. Re-classify every block based on the freshly-computed
    ///      line counts and rebuild the free/recyclable/full lists.
    ///   5. Drop large objects whose payload node was not marked.
    ///   6. Reset the bump cursor so the next allocation picks a hole
    ///      from a recyclable block (if any).
    pub fn collect(self: *ImmixGc) void {
        // Re-entry guard: the worklist allocator path or any other
        // helper that could indirectly trigger a collection must see
        // `in_collect` as true and skip.
        if (self.in_collect) return;
        self.in_collect = true;
        defer self.in_collect = false;

        const new_id = std.math.add(u32, self.mark_id, 1) catch blk: {
            // u32 wrap. Reset every node's mark on the heap and start
            // over at 1. Practically unreachable for any realistic
            // workload (4 billion cycles), but covered for completeness.
            self.clearAllMarks();
            break :blk 1;
        };
        self.mark_id = new_id;

        // Step 2: clear payload line marks.
        var b = self.all_blocks;
        while (b) |block| : (b = block.all_next) {
            for (block.line_marks[HEADER_LINES..]) |*m| m.* = 0;
        }

        // Step 3: mark.
        self.markFromRoots();

        // Step 4: re-classify blocks. We rebuild the lists from
        // scratch to avoid double-filing.
        self.free_blocks = null;
        self.recyclable_blocks = null;
        self.full_blocks = null;
        b = self.all_blocks;
        while (b) |block| : (b = block.all_next) {
            block.next = null;
            self.classifyAndFile(block);
        }

        // Step 5: sweep LOS.
        self.sweepLargeObjects();

        // Step 6: drop both bump regions so the next allocation picks
        // a (possibly freshly-recycled) block from
        // `recyclable_blocks`/`free_blocks`. Both the small and the
        // overflow (#777) cursors need to be reset — their blocks
        // have just been re-filed by step 4.
        self.current_block = null;
        self.cursor = 0;
        self.limit = 0;
        self.overflow_block = null;
        self.overflow_cursor = 0;
        self.overflow_limit = 0;

        // Update accounting: the bytes we freed are exactly the lines
        // that were just reclaimed. Re-scan the heap to count free
        // lines (cheap; this is per-cycle bookkeeping, not per-alloc).
        var free_payload_lines: u64 = 0;
        b = self.all_blocks;
        while (b) |block| : (b = block.all_next) {
            for (block.line_marks[HEADER_LINES..]) |m| {
                if (m == 0) free_payload_lines += 1;
            }
        }
        const total_payload_lines: u64 = @as(u64, @intCast(PAYLOAD_LINES)) * self.blocks_allocated;
        const used_payload_lines = total_payload_lines - free_payload_lines;
        const used_payload_bytes = used_payload_lines * LINE_SIZE;
        // bytes_freed is a monotonic counter that tracks lifetime
        // reclamation; we add the delta between bytes-allocated and
        // bytes-still-resident-in-blocks. Plus LOS reclaim accounted
        // for separately in `sweepLargeObjects`.
        const block_freed = if (self.stats_data.bytes_allocated >= used_payload_bytes + self.losBytesLive())
            self.stats_data.bytes_allocated - used_payload_bytes - self.losBytesLive()
        else
            self.stats_data.bytes_freed; // keep monotonic on heuristic mismatch
        self.stats_data.bytes_freed = block_freed;

        self.stats_data.collections += 1;
    }

    /// Sum live LOS payload bytes.
    fn losBytesLive(self: *const ImmixGc) u64 {
        var total: u64 = 0;
        var p = self.large_objects;
        while (p) |lo| : (p = lo.next) total += lo.payload_len;
        return total;
    }

    /// Walk every Node in every block and LOS slab, zeroing its
    /// `gc_flags`. Called only on `mark_id` overflow.
    fn clearAllMarks(self: *ImmixGc) void {
        // Conservative pass: the block's bump cursor doesn't tell us
        // where individual nodes live, so walk linearly from
        // HEADER_BYTES reading {tag, n_fields, gc_flags} and stepping
        // forward by the encoded size. Stops when n_fields would push
        // past the block end (which marks the boundary between live
        // bumped data and unused tail bytes).
        var b = self.all_blocks;
        while (b) |block| : (b = block.all_next) {
            const base = @intFromPtr(block);
            var p = base + HEADER_BYTES;
            const end = base + BLOCK_SIZE;
            while (p + @sizeOf(Node) <= end) {
                const n: *Node = @ptrFromInt(p);
                const size = @sizeOf(Node) + @as(usize, n.n_fields) * @sizeOf(u64);
                if (p + size > end) break; // ragged tail
                n.gc_flags = 0;
                p += std.mem.alignForward(usize, size, @alignOf(Node));
            }
        }
        var l = self.large_objects;
        while (l) |lo| : (l = lo.next) {
            const n: *Node = @ptrCast(@alignCast(lo.payload));
            n.gc_flags = 0;
        }
    }

    /// Mark phase entry point: queues every explicit root and runs the
    /// transitive trace.
    fn markFromRoots(self: *ImmixGc) void {
        var work: std.ArrayList(*Node) = .empty;
        defer work.deinit(self.child);
        for (self.roots.items) |slot| {
            const w = slot.*;
            if (self.isHeapPointer(w)) {
                const addr: usize = @intCast(w);
                work.append(self.child, @ptrFromInt(addr)) catch @panic("Immix: out of memory during mark");
            }
        }
        self.markFromShadowStack(&work);
        self.drainMarkWorklist(&work);
    }

    /// Walk the shadow-stack buffer (issue #780) and queue every slot
    /// that looks like a heap pointer. Slots are written by the
    /// LLVM-generated code via `rts_shadow_push` at every `*Node` SSA
    /// definition; the live region is `rts_shadow_buffer[0..top]`.
    fn markFromShadowStack(self: *ImmixGc, work: *std.ArrayList(*Node)) void {
        const top = heap.rts_shadow_top;
        var i: u32 = 0;
        while (i < top) : (i += 1) {
            const w = heap.rts_shadow_buffer[i];
            if (self.isHeapPointer(w)) {
                const addr: usize = @intCast(w);
                work.append(self.child, @ptrFromInt(addr)) catch @panic("Immix: out of memory during mark");
            }
        }
    }

    fn drainMarkWorklist(self: *ImmixGc, work: *std.ArrayList(*Node)) void {
        while (work.pop()) |node| {
            if (node.gc_flags == self.mark_id) continue;
            // Sanity-clamp `n_fields` against the block payload bound
            // before recursing. A conservative-scan false positive may
            // point at the middle of a node (or at non-node memory
            // that just happens to live inside the heap) where
            // `n_fields` is garbage. Without this clamp we'd walk off
            // the end of the block during pointer recursion.
            if (!self.nodeLooksValid(node)) continue;
            node.gc_flags = self.mark_id;
            self.markNodeLines(node);

            const tag_raw = @intFromEnum(node.tag);
            switch (tag_raw) {
                @intFromEnum(nodemod.Tag.Unit),
                @intFromEnum(nodemod.Tag.Int),
                @intFromEnum(nodemod.Tag.Char),
                @intFromEnum(nodemod.Tag.String),
                => {
                    // No Node-pointer fields.
                },
                @intFromEnum(nodemod.Tag.Ind) => {
                    // Indirection: field[0] is the *Node target.
                    if (node.n_fields >= 1) {
                        const w = nodemod.fieldsConst(node)[0];
                        if (self.isHeapPointer(w)) {
                            const addr: usize = @intCast(w);
                            work.append(self.child, @ptrFromInt(addr)) catch @panic("Immix: out of memory during mark");
                        }
                    }
                },
                else => {
                    // Thunks, closures, Data constructors, user-defined
                    // tags: consult the per-tag pointer-mask table (#779)
                    // populated by the backend at program start. Bit `i`
                    // set ⇔ field `i` holds a `*Node`. Tags the backend
                    // hasn't registered carry `UNKNOWN_MASK` and fall
                    // back to a conservative scan so newly-introduced
                    // tags remain trace-safe.
                    const mask = pointerMaskFor(@as(u64, @intCast(tag_raw)));
                    const fields_slice = nodemod.fieldsConst(node);
                    if (mask == UNKNOWN_MASK) {
                        for (fields_slice) |w| {
                            if (self.isHeapPointer(w)) {
                                const addr: usize = @intCast(w);
                                work.append(self.child, @ptrFromInt(addr)) catch @panic("Immix: out of memory during mark");
                            }
                        }
                    } else {
                        const n = @min(fields_slice.len, 64);
                        var i: usize = 0;
                        while (i < n) : (i += 1) {
                            if ((mask >> @intCast(i)) & 1 == 0) continue;
                            const w = fields_slice[i];
                            if (self.isHeapPointer(w)) {
                                const addr: usize = @intCast(w);
                                work.append(self.child, @ptrFromInt(addr)) catch @panic("Immix: out of memory during mark");
                            }
                        }
                    }
                },
            }
        }
    }

    /// Bound-check a node candidate before treating it as live.
    ///
    /// A conservative-scan pointer may point into the middle of a real
    /// node, or into otherwise-valid heap memory whose contents are not
    /// a node header. In both cases reading `n_fields` returns garbage,
    /// so we cap the resulting object size against the remaining bytes
    /// of the containing block (or LOS slab) before recursing.
    fn nodeLooksValid(self: *const ImmixGc, node: *Node) bool {
        const size = @sizeOf(Node) + @as(usize, node.n_fields) * @sizeOf(u64);
        const addr = @intFromPtr(node);
        if (self.blockOf(node)) |block| {
            const block_end = @intFromPtr(block) + BLOCK_SIZE;
            return addr + size <= block_end;
        }
        // LOS object — payload size known from the slab header.
        var l = self.large_objects;
        while (l) |lo| : (l = lo.next) {
            const start = @intFromPtr(lo.payload);
            if (addr == start) {
                return size <= lo.payload_len;
            }
        }
        return false;
    }

    /// Mark every line the given node occupies. Marks the line
    /// containing the header byte and the lines containing payload
    /// bytes; the last line is the one holding `addr + size - 1`.
    fn markNodeLines(self: *ImmixGc, node: *Node) void {
        const addr = @intFromPtr(node);
        const size = @sizeOf(Node) + @as(usize, node.n_fields) * @sizeOf(u64);
        // Small object inside a block?
        if (self.blockOf(node)) |block| {
            const first = block.lineIndexOf(addr);
            const last = block.lineIndexOf(addr + size - 1);
            for (first..last + 1) |i| block.line_marks[i] = 1;
        }
        // LOS objects have no line marks (their whole slab is live or
        // dead in one shot).
    }

    /// Test whether `word` looks like a pointer into our heap.
    ///
    /// Strict: must be non-null, 8-byte-aligned, and either point into
    /// the payload region of an Immix block (i.e. past the in-block
    /// header) or into an LOS payload.
    pub fn isHeapPointer(self: *const ImmixGc, word: u64) bool {
        if (word == 0) return false;
        // `Node` requires 8-byte alignment.
        if (word % @alignOf(Node) != 0) return false;
        // Search block list. The block base is the word masked to
        // BLOCK_SIZE; check whether that base appears in `all_blocks`.
        const candidate_base = word & ~@as(u64, BLOCK_SIZE - 1);
        var b = self.all_blocks;
        while (b) |block| : (b = block.all_next) {
            if (@intFromPtr(block) == candidate_base) {
                const offset = word - candidate_base;
                return offset >= HEADER_BYTES and offset < BLOCK_SIZE;
            }
        }
        // Check LOS.
        var l = self.large_objects;
        while (l) |lo| : (l = lo.next) {
            const payload_start = @intFromPtr(lo.payload);
            if (word >= payload_start and word < payload_start + lo.payload_len) {
                return true;
            }
        }
        return false;
    }

    /// LOS sweep: drop slabs whose payload `Node` wasn't marked in
    /// this cycle. Assumes LOS payloads start with a `Node` header
    /// (the only thing the RTS allocates through this allocator).
    fn sweepLargeObjects(self: *ImmixGc) void {
        var pp: *?*LargeObject = &self.large_objects;
        while (pp.*) |lo| {
            const n: *const Node = @ptrCast(@alignCast(lo.payload));
            if (n.gc_flags == self.mark_id) {
                pp = &lo.next;
                continue;
            }
            // Unlink and free.
            pp.* = lo.next;
            const raw: [*]align(@alignOf(LargeObject)) u8 = @ptrCast(@alignCast(lo.slab_base));
            const slice: []align(@alignOf(LargeObject)) u8 = raw[0..lo.slab_len];
            self.child.free(slice);
            self.large_objects_allocated -= 1;
            // bytes_freed includes the payload (not the slab overhead).
            // We avoid touching stats here because `collect()` recomputes
            // it consistently at the end.
        }
    }

    // ── Introspection helpers (test-only) ─────────────────────────────

    /// Address of the block that owns `ptr`, or `null` if `ptr` does
    /// not live in any of this heap's blocks. Pointer-only: large
    /// objects return `null`. Useful for tests asserting that small
    /// objects end up clustered as expected.
    pub fn blockOf(self: *const ImmixGc, ptr: *const anyopaque) ?*BlockHeader {
        const addr = @intFromPtr(ptr);
        const candidate_base = addr & ~(@as(usize, BLOCK_SIZE) - 1);
        // Confirm the candidate is one of ours; ptr arithmetic alone
        // is insufficient because the LOS lives in unrelated slabs.
        var b = self.all_blocks;
        while (b) |block| : (b = block.all_next) {
            if (@intFromPtr(block) == candidate_base) return block;
        }
        return null;
    }

    /// True if `ptr` lives in the large-object space.
    pub fn isLarge(self: *const ImmixGc, ptr: *const anyopaque) bool {
        const addr = @intFromPtr(ptr);
        var l = self.large_objects;
        while (l) |lo| : (l = lo.next) {
            const start = @intFromPtr(lo.payload);
            if (addr >= start and addr < start + lo.payload_len) return true;
        }
        return false;
    }
};

/// Mark every line that overlaps the byte range `[start, end)` as used.
///
/// The Immix paper additionally marks the *next* line after a small
/// object to handle objects that don't end on a line boundary
/// (conservative one-line overestimate). Bump allocation always packs
/// objects contiguously, so the next line is already covered by the
/// next allocation in the same hole; we therefore mark exactly the
/// lines spanned by `[start, end)`. This is the precise variant
/// described in §3 of the paper.
fn markLinesUsed(block: *BlockHeader, start: usize, end: usize) void {
    const base = @intFromPtr(block);
    std.debug.assert(start >= base + HEADER_BYTES);
    std.debug.assert(end <= base + BLOCK_SIZE);
    const first = (start - base) / LINE_SIZE;
    // `end` is exclusive, so the last line touched is the one that
    // contains byte `end - 1`. Compute via `(end - 1 - base)/LINE_SIZE`
    // to avoid marking a phantom line when `end` lands exactly on a
    // boundary.
    const last = (end - 1 - base) / LINE_SIZE;
    for (first..last + 1) |i| block.line_marks[i] = 1;
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

const testing = std.testing;

test "Immix: geometry constants match the paper" {
    try testing.expectEqual(@as(usize, 32 * 1024), BLOCK_SIZE);
    try testing.expectEqual(@as(usize, 128), LINE_SIZE);
    try testing.expectEqual(@as(usize, 256), LINES_PER_BLOCK);
    try testing.expect(HEADER_LINES >= 1 and HEADER_LINES <= 4);
    try testing.expect(PAYLOAD_LINES + HEADER_LINES == LINES_PER_BLOCK);
}

test "Immix: init/deinit with no allocations leaks nothing" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    try testing.expectEqual(@as(u64, 0), gc.blocks_allocated);
    try testing.expectEqual(@as(u64, 0), gc.stats_data.bytes_allocated);
}

test "Immix: single small allocation lives in payload region" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const p = (try gc.gcAllocator().alloc(64, .of(u64)));
    const block = gc.blockOf(p) orelse return error.TestUnexpectedNullBlock;
    const base = @intFromPtr(block);
    try testing.expect(@intFromPtr(p) >= base + HEADER_BYTES);
    try testing.expect(@intFromPtr(p) + 64 <= base + BLOCK_SIZE);
    try testing.expectEqual(@as(u64, 1), gc.blocks_allocated);
    try testing.expectEqual(@as(u64, 64), gc.stats_data.bytes_allocated);
}

test "Immix: many small allocations cluster into the same block" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    var ptrs: [64][*]u8 = undefined;
    for (&ptrs) |*slot| slot.* = try a.alloc(32, .of(u64));

    // 64 × 32 B = 2 KB of payload, well under a single 32 KB block.
    try testing.expectEqual(@as(u64, 1), gc.blocks_allocated);
    const first_block = gc.blockOf(ptrs[0]).?;
    for (ptrs) |p| {
        try testing.expectEqual(first_block, gc.blockOf(p).?);
    }
}

test "Immix: allocations are aligned" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    for ([_]std.mem.Alignment{ .of(u8), .of(u16), .of(u32), .of(u64), .of(u128) }) |al| {
        const p = try a.alloc(48, al);
        try testing.expectEqual(@as(usize, 0), @intFromPtr(p) % al.toByteUnits());
    }
}

test "Immix: writes to allocated memory survive" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    const p = try a.alloc(256, .of(u64));
    @memset(p[0..256], 0xCD);
    try testing.expectEqual(@as(u8, 0xCD), p[0]);
    try testing.expectEqual(@as(u8, 0xCD), p[255]);
}

test "Immix: filling a block triggers a fresh block" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    // Allocate enough small objects to overflow a single block. With
    // PAYLOAD_BYTES of payload per block and 128-byte allocations,
    // (PAYLOAD_BYTES / 128) + 1 allocations is guaranteed to require a
    // second block.
    const count = (PAYLOAD_BYTES / 128) + 4;
    var blocks_seen = std.AutoHashMap(*BlockHeader, void).init(testing.allocator);
    defer blocks_seen.deinit();
    for (0..count) |_| {
        const p = try a.alloc(128, .of(u64));
        try blocks_seen.put(gc.blockOf(p).?, {});
    }
    try testing.expect(blocks_seen.count() >= 2);
    try testing.expect(gc.blocks_allocated >= 2);
}

test "Immix: line marks reflect bumped lines" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    const p = try a.alloc(LINE_SIZE, .of(u64));
    const block = gc.blockOf(p).?;
    // Header lines must always read as used.
    for (block.line_marks[0..HEADER_LINES]) |m| {
        try testing.expect(m != 0);
    }
    // The line containing the allocation must be marked used.
    const line = block.lineIndexOf(@intFromPtr(p));
    try testing.expect(block.line_marks[line] != 0);
    // Lines beyond the bump cursor should still read free (no
    // collection touches them yet).
    try testing.expectEqual(@as(u8, 0), block.line_marks[LINES_PER_BLOCK - 1]);
}

test "Immix: large allocation goes to the LOS, not a block" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    const big = try a.alloc(PAYLOAD_BYTES + 1, .of(u64));
    try testing.expect(gc.isLarge(big));
    try testing.expectEqual(@as(?*BlockHeader, null), gc.blockOf(big));
    try testing.expectEqual(@as(u64, 1), gc.large_objects_allocated);
    try testing.expectEqual(@as(u64, 0), gc.blocks_allocated);

    // The payload must be writable end-to-end.
    @memset(big[0 .. PAYLOAD_BYTES + 1], 0xAB);
    try testing.expectEqual(@as(u8, 0xAB), big[PAYLOAD_BYTES]);
}

test "Immix: large allocations honour requested alignment" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    // A 4-KB-aligned, multi-block payload. This exercises the LOS
    // alignment-padding path.
    const al: std.mem.Alignment = .fromByteUnits(4096);
    const p = try a.alloc(PAYLOAD_BYTES * 2, al);
    try testing.expectEqual(@as(usize, 0), @intFromPtr(p) % 4096);
}

test "Immix: blocks remain on the master list after classification" {
    // Force a second block to be allocated and verify both are tracked
    // by `all_blocks` (so `deinit` can free them).
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    var i: usize = 0;
    while (gc.blocks_allocated < 2 and i < 10_000) : (i += 1) {
        _ = try a.alloc(256, .of(u64));
    }
    try testing.expect(gc.blocks_allocated >= 2);

    var count: usize = 0;
    var b = gc.all_blocks;
    while (b) |block| : (b = block.all_next) count += 1;
    try testing.expectEqual(@as(usize, @intCast(gc.blocks_allocated)), count);
}

test "Immix: GcAllocator.free is still a bulk-reclaim no-op" {
    // Per-object free is reclaimed by collection (#72), not by the
    // mutator. Verifies the vtable hook is callable and does not
    // accidentally update accounting.
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    const p = try a.alloc(64, .of(u64));
    a.free(p[0..64], .of(u64));
    try testing.expectEqual(@as(u64, 0), a.stats().bytes_freed);
}

test "Immix: collect() bumps the cycle counter" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    try testing.expectEqual(@as(u64, 0), a.stats().collections);
    a.collect();
    try testing.expectEqual(@as(u64, 1), a.stats().collections);
    a.collect();
    try testing.expectEqual(@as(u64, 2), a.stats().collections);
}

test "Immix: addRoot / removeRoot maintain the root list" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    var slot_a: u64 = 0;
    var slot_b: u64 = 0;
    const a = gc.gcAllocator();
    a.addRoot(&slot_a);
    a.addRoot(&slot_b);
    try testing.expectEqual(@as(usize, 2), gc.roots.items.len);
    a.removeRoot(&slot_a);
    try testing.expectEqual(@as(usize, 1), gc.roots.items.len);
    try testing.expectEqual(&slot_b, gc.roots.items[0]);
    a.removeRoot(&slot_b);
    try testing.expectEqual(@as(usize, 0), gc.roots.items.len);
}

// ── Shadow-stack ABI (#780) ──────────────────────────────────────────

/// Reset the shadow-stack buffer to a known-empty state so tests can
/// run independently. Other tests that don't touch the shadow stack
/// don't need this because they go through the explicit `addRoot`
/// path; tests in this section share the global buffer.
fn resetShadowStack() void {
    heap.rts_shadow_top = 0;
    @memset(&heap.rts_shadow_buffer, 0);
}

test "Immix: collect walks the shadow stack and keeps pushed nodes" {
    resetShadowStack();
    defer resetShadowStack();

    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const live = try newNode(&gc, .Int, 1);
    nodemod.fields(live)[0] = 7;
    const dead = try newNode(&gc, .Int, 1);
    nodemod.fields(dead)[0] = 99;

    heap.rts_shadow_push(@intFromPtr(live));

    gc.collect();
    try testing.expectEqual(gc.mark_id, live.gc_flags);
    try testing.expect(dead.gc_flags != gc.mark_id);
}

test "Immix: rts_shadow_save / rts_shadow_restore brackets a region" {
    resetShadowStack();
    defer resetShadowStack();

    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const outer = try newNode(&gc, .Int, 1);
    nodemod.fields(outer)[0] = 1;
    const inner = try newNode(&gc, .Int, 1);
    nodemod.fields(inner)[0] = 2;

    heap.rts_shadow_push(@intFromPtr(outer));
    const saved = heap.rts_shadow_save();
    heap.rts_shadow_push(@intFromPtr(inner));

    // Both roots are visible to a collection that fires inside the
    // nested region.
    gc.collect();
    try testing.expectEqual(gc.mark_id, outer.gc_flags);
    try testing.expectEqual(gc.mark_id, inner.gc_flags);

    // After restore the inner root is released; a later collection
    // sees only the outer one.
    heap.rts_shadow_restore(saved);
    const inner2 = try newNode(&gc, .Int, 1);
    nodemod.fields(inner2)[0] = 3;

    gc.collect();
    try testing.expectEqual(gc.mark_id, outer.gc_flags);
    // inner2 was never pushed, so it should not survive.
    try testing.expect(inner2.gc_flags != gc.mark_id);
}

test "Immix: shadow-stack slots holding null are skipped" {
    resetShadowStack();
    defer resetShadowStack();

    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const live = try newNode(&gc, .Int, 1);
    nodemod.fields(live)[0] = 42;

    heap.rts_shadow_push(0);
    heap.rts_shadow_push(@intFromPtr(live));
    heap.rts_shadow_push(0);

    gc.collect();
    try testing.expectEqual(gc.mark_id, live.gc_flags);
}

test "Immix: rts_shadow_restore truncates the buffer and zeroes released slots" {
    resetShadowStack();
    defer resetShadowStack();

    const saved = heap.rts_shadow_save();
    try testing.expectEqual(@as(u32, 0), saved);
    heap.rts_shadow_push(0xCAFE0001);
    heap.rts_shadow_push(0xCAFE0002);
    try testing.expectEqual(@as(u32, 2), heap.rts_shadow_top);
    heap.rts_shadow_restore(saved);
    try testing.expectEqual(@as(u32, 0), heap.rts_shadow_top);
    try testing.expectEqual(@as(u64, 0), heap.rts_shadow_buffer[0]);
    try testing.expectEqual(@as(u64, 0), heap.rts_shadow_buffer[1]);
}

test "Immix: std.mem.Allocator adapter routes through the same heap" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.allocator();
    const buf = try a.dupe(u8, "hello immix");
    try testing.expectEqualStrings("hello immix", buf);
    try testing.expect(gc.stats_data.bytes_allocated >= "hello immix".len);
}

test "Immix: classifyAndFile records a filled block as full" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    // Fill a block end-to-end with line-sized allocations so every line
    // is marked, then provoke advancement to a fresh block by
    // requesting one more allocation.
    const a = gc.gcAllocator();
    const per_block = PAYLOAD_BYTES / LINE_SIZE;
    var i: usize = 0;
    while (i < per_block) : (i += 1) {
        _ = try a.alloc(LINE_SIZE, .of(u64));
    }
    // Force the allocator to retire the now-full block.
    _ = try a.alloc(LINE_SIZE, .of(u64));

    // At least one block should have been filed as full.
    var fullc: usize = 0;
    var b = gc.full_blocks;
    while (b) |bl| : (b = bl.next) fullc += 1;
    try testing.expect(fullc >= 1);
}

// ── Collection (#72) ─────────────────────────────────────────────────

/// Helper for the collector tests: allocate a header + N payload slots
/// from `gc` and initialise the resulting Node in place.
fn newNode(gc: *ImmixGc, tag: nodemod.Tag, n_fields: u32) !*Node {
    const size = @sizeOf(Node) + @as(usize, n_fields) * @sizeOf(u64);
    const raw = try gc.gcAllocator().alloc(size, .of(Node));
    const n: *Node = @ptrCast(@alignCast(raw));
    n.* = .{ .tag = tag, .n_fields = n_fields };
    if (n_fields > 0) @memset(nodemod.fields(n), 0);
    return n;
}

test "Immix: collect with no roots clears every payload line" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    _ = try newNode(&gc, .Int, 1);
    _ = try newNode(&gc, .Int, 1);
    _ = try newNode(&gc, .Data, 2);
    gc.collect();
    // Every payload line of every block should now read as free.
    var b = gc.all_blocks;
    while (b) |block| : (b = block.all_next) {
        for (block.line_marks[HEADER_LINES..]) |m| {
            try testing.expectEqual(@as(u8, 0), m);
        }
    }
}

test "Immix: collect keeps a rooted Int, drops an unrooted one" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    const live = try newNode(&gc, .Int, 1);
    nodemod.fields(live)[0] = 42;
    const dead = try newNode(&gc, .Int, 1);
    nodemod.fields(dead)[0] = 99;

    var slot: u64 = @intFromPtr(live);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    gc.collect();
    try testing.expectEqual(gc.mark_id, live.gc_flags);
    try testing.expect(dead.gc_flags != gc.mark_id);
}

test "Immix: collect follows Ind indirection" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    const target = try newNode(&gc, .Int, 1);
    nodemod.fields(target)[0] = 7;
    const ind = try newNode(&gc, .Ind, 1);
    nodemod.fields(ind)[0] = @intFromPtr(target);

    var slot: u64 = @intFromPtr(ind);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    gc.collect();
    try testing.expectEqual(gc.mark_id, ind.gc_flags);
    try testing.expectEqual(gc.mark_id, target.gc_flags);
}

test "Immix: collect terminates on heap cycles" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    // A and B point at each other through Data field[0].
    const a = try newNode(&gc, .Data, 1);
    const b = try newNode(&gc, .Data, 1);
    nodemod.fields(a)[0] = @intFromPtr(b);
    nodemod.fields(b)[0] = @intFromPtr(a);

    var slot: u64 = @intFromPtr(a);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    gc.collect();
    try testing.expectEqual(gc.mark_id, a.gc_flags);
    try testing.expectEqual(gc.mark_id, b.gc_flags);
}

test "Immix: collect reclaims an unrooted LOS allocation" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    const big = try gc.gcAllocator().alloc(PAYLOAD_BYTES + 64, .of(Node));
    const n: *Node = @ptrCast(@alignCast(big));
    n.* = .{ .tag = .Data, .n_fields = 0 };
    try testing.expectEqual(@as(u64, 1), gc.large_objects_allocated);

    gc.collect();
    try testing.expectEqual(@as(u64, 0), gc.large_objects_allocated);
}

test "Immix: collect preserves a rooted LOS allocation" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    const big = try gc.gcAllocator().alloc(PAYLOAD_BYTES + 64, .of(Node));
    const n: *Node = @ptrCast(@alignCast(big));
    n.* = .{ .tag = .Data, .n_fields = 0 };

    var slot: u64 = @intFromPtr(n);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    gc.collect();
    try testing.expectEqual(@as(u64, 1), gc.large_objects_allocated);
    try testing.expectEqual(gc.mark_id, n.gc_flags);
}

test "Immix: collect re-files blocks based on surviving lines" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    // Allocate a single rooted Int — at most a handful of lines used.
    const live = try newNode(&gc, .Int, 1);
    var slot: u64 = @intFromPtr(live);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    // And several unrooted Data nodes to dirty more lines.
    var i: usize = 0;
    while (i < 32) : (i += 1) _ = try newNode(&gc, .Data, 1);

    gc.collect();

    // After collect, the single block should be recyclable (live lines
    // remain) — not free (something is still live) and not full (most
    // lines were reclaimed).
    const block = gc.all_blocks orelse return error.TestUnexpectedNullBlock;
    try testing.expectEqual(BlockState.recyclable, block.state);
    try testing.expect(block.free_lines > 0);
    try testing.expect(block.free_lines < PAYLOAD_LINES);
}

test "Immix: allocation after collect reuses reclaimed lines" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    // Fill some lines, drop them all, collect.
    var i: usize = 0;
    while (i < 32) : (i += 1) _ = try newNode(&gc, .Int, 1);
    const blocks_before = gc.blocks_allocated;
    gc.collect();
    // The next allocation should NOT need a new block — there should be
    // plenty of reclaimed lines available.
    _ = try newNode(&gc, .Int, 1);
    try testing.expectEqual(blocks_before, gc.blocks_allocated);
}

test "Immix: stress — repeated alloc/collect leaves no LOS leak" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    const cycles: usize = 16;
    var i: usize = 0;
    while (i < cycles) : (i += 1) {
        // Each iteration: alloc one LOS object, no root, collect.
        const big = try gc.gcAllocator().alloc(PAYLOAD_BYTES + 32, .of(Node));
        const n: *Node = @ptrCast(@alignCast(big));
        n.* = .{ .tag = .Data, .n_fields = 0 };
        gc.collect();
    }
    try testing.expectEqual(@as(u64, 0), gc.large_objects_allocated);
}

test "Immix: collect monotonically increments mark_id" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    const before = gc.mark_id;
    gc.collect();
    try testing.expect(gc.mark_id > before);
    const mid = gc.mark_id;
    gc.collect();
    try testing.expect(gc.mark_id > mid);
}

test "Immix: isHeapPointer rejects non-pointer words" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    _ = try newNode(&gc, .Int, 1);
    try testing.expect(!gc.isHeapPointer(0));
    try testing.expect(!gc.isHeapPointer(7)); // misaligned
    try testing.expect(!gc.isHeapPointer(0xdeadbeef_00000000));
}

// ── Small / overflow cursor split (#777) ─────────────────────────────

test "Immix: medium allocations go to a dedicated overflow block" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    // A small allocation seeds the small cursor in block A.
    _ = try gc.gcAllocator().alloc(64, .of(u64));
    const small_block = gc.current_block.?;
    try testing.expect(gc.overflow_block == null);

    // A medium allocation (> LINE_SIZE) must NOT bump into the
    // small-cursor block; it grabs a fresh overflow block.
    _ = try gc.gcAllocator().alloc(LINE_SIZE * 2, .of(u64));
    try testing.expect(gc.overflow_block != null);
    try testing.expect(gc.overflow_block.? != small_block);
    try testing.expectEqual(small_block, gc.current_block.?);
}

test "Immix: small allocations stay on the small cursor when overflow is active" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    // Force the overflow cursor to be initialised first.
    _ = try gc.gcAllocator().alloc(LINE_SIZE * 3, .of(u64));
    const overflow_block = gc.overflow_block.?;

    // A subsequent small allocation must seed (or reuse) the small
    // cursor, leaving the overflow block untouched.
    _ = try gc.gcAllocator().alloc(48, .of(u64));
    try testing.expect(gc.current_block != null);
    try testing.expect(gc.current_block.? != overflow_block);
    try testing.expectEqual(overflow_block, gc.overflow_block.?);
}

test "Immix: overflow block is retired and re-classified when exhausted" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    // Fill the overflow block almost to capacity with one big
    // allocation, then trigger an overflow that exceeds the remaining
    // tail — the second medium allocation must request a new block.
    const big_len = PAYLOAD_BYTES - LINE_SIZE * 2;
    _ = try gc.gcAllocator().alloc(big_len, .of(u64));
    const first_overflow = gc.overflow_block.?;

    // Second medium allocation cannot fit in the tail; it grabs a
    // fresh overflow block and the previous one is filed away.
    _ = try gc.gcAllocator().alloc(LINE_SIZE * 4, .of(u64));
    try testing.expect(gc.overflow_block.? != first_overflow);

    // The retired block lives on `full_blocks` (most of its payload is
    // marked) or `recyclable_blocks`; either way it must not be on the
    // free list.
    var on_free: bool = false;
    var b = gc.free_blocks;
    while (b) |bb| : (b = bb.next) {
        if (bb == first_overflow) on_free = true;
    }
    try testing.expect(!on_free);
}

// ── Per-constructor pointer-mask table (#779) ────────────────────────

/// Reset the pointer-mask table to its default `UNKNOWN_MASK` state so
/// tests that mutate it don't leak into other tests. Tests share the
/// global `rts_pointer_masks` array since it's the production storage.
fn resetPointerMasks() void {
    for (&rts_pointer_masks) |*m| m.* = UNKNOWN_MASK;
}

test "Immix: pointer-mask scalar fields are not followed" {
    resetPointerMasks();
    defer resetPointerMasks();

    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    // Two heap nodes; one referenced through a marked pointer field,
    // the other through a slot the mask declares scalar. The scalar
    // slot is forced to hold a value that *looks* like a heap pointer
    // — without the mask the conservative scan would mark its target.
    const live_via_ptr = try newNode(&gc, .Int, 1);
    nodemod.fields(live_via_ptr)[0] = 0xC0FFEE;
    const masked_target = try newNode(&gc, .Int, 1);
    nodemod.fields(masked_target)[0] = 0xFACADE;

    const data_tag: u64 = @intFromEnum(nodemod.Tag.Data);
    rts_set_pointer_mask(data_tag, 0b01); // only field[0] is a ptr

    const root_node = try newNode(&gc, .Data, 2);
    nodemod.fields(root_node)[0] = @intFromPtr(live_via_ptr);
    nodemod.fields(root_node)[1] = @intFromPtr(masked_target);

    var slot: u64 = @intFromPtr(root_node);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    gc.collect();
    try testing.expectEqual(gc.mark_id, root_node.gc_flags);
    try testing.expectEqual(gc.mark_id, live_via_ptr.gc_flags);
    try testing.expect(masked_target.gc_flags != gc.mark_id);
}

test "Immix: pointer-mask UNKNOWN_MASK falls back to conservative scan" {
    resetPointerMasks();
    defer resetPointerMasks();

    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const reachable = try newNode(&gc, .Int, 1);
    nodemod.fields(reachable)[0] = 7;
    const root_node = try newNode(&gc, .Data, 1);
    nodemod.fields(root_node)[0] = @intFromPtr(reachable);

    var slot: u64 = @intFromPtr(root_node);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    gc.collect();
    try testing.expectEqual(gc.mark_id, reachable.gc_flags);
}

test "Immix: pointer-mask all-zero treats every field as scalar" {
    resetPointerMasks();
    defer resetPointerMasks();

    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    rts_set_pointer_mask(@intFromEnum(nodemod.Tag.Data), 0);

    const unreachable_node = try newNode(&gc, .Int, 1);
    const root_node = try newNode(&gc, .Data, 1);
    nodemod.fields(root_node)[0] = @intFromPtr(unreachable_node);

    var slot: u64 = @intFromPtr(root_node);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    gc.collect();
    try testing.expectEqual(gc.mark_id, root_node.gc_flags);
    try testing.expect(unreachable_node.gc_flags != gc.mark_id);
}

// ── Auto-collect trigger (#781) ──────────────────────────────────────

test "Immix: auto-collect is off by default" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    try testing.expect(!gc.auto_collect_enabled);
}

test "Immix: setAutoCollect with a tiny budget triggers collect on grow" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    gc.setAutoCollect(true);
    gc.setTargetBlocks(2);

    // Allocate enough small nodes to force at least three blocks if
    // collection never runs. With auto-collect on and no roots, the
    // collector reaps everything between bursts, so the live block
    // count never exceeds the budget by much and `collections > 0`.
    const a = gc.gcAllocator();
    // Allocate 4× the payload of a single block.  With target=2 this
    // forces at least one auto-collect cycle.
    var i: usize = 0;
    while (i < 4) : (i += 1) {
        var j: usize = 0;
        while (j < (PAYLOAD_BYTES / 256)) : (j += 1) {
            _ = try a.alloc(256, .of(u64));
        }
    }
    try testing.expect(a.stats().collections > 0);
}

test "Immix: auto-collect with rooted node preserves the root" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    gc.setAutoCollect(true);
    gc.setTargetBlocks(2);

    // Pre-allocate a Data node and root it.
    const live = try newNode(&gc, .Data, 1);
    nodemod.fields(live)[0] = 0xCAFE;
    var slot: u64 = @intFromPtr(live);
    gc.gcAllocator().addRoot(&slot);
    defer gc.gcAllocator().removeRoot(&slot);

    // Burn enough block-sized allocations to push past the 2-block
    // budget — 256-byte slabs are unrelated to `Node` layout but
    // they exercise the same code path and let the iteration count
    // match the byte budget exactly.
    const a = gc.gcAllocator();
    var i: usize = 0;
    while (i < (PAYLOAD_BYTES * 4 / 256)) : (i += 1) {
        _ = try a.alloc(256, .of(u64));
    }
    try testing.expect(a.stats().collections > 0);
    // The rooted node must still be reachable and unmolested.
    try testing.expectEqual(@as(u64, 0xCAFE), nodemod.fields(live)[0]);
}

test "Immix: target_blocks grows after a non-trivial live set" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    gc.setAutoCollect(true);
    gc.setTargetBlocks(2);

    // Pin a handful of nodes so each collection retains them.
    var pinned: [4]u64 = .{ 0, 0, 0, 0 };
    for (&pinned) |*slot| {
        const n = try newNode(&gc, .Int, 1);
        slot.* = @intFromPtr(n);
        gc.gcAllocator().addRoot(slot);
    }
    defer for (&pinned) |*slot| gc.gcAllocator().removeRoot(slot);

    const start_target = gc.target_blocks;
    const a = gc.gcAllocator();
    var i: usize = 0;
    while (i < (PAYLOAD_BYTES * 4 / 256)) : (i += 1) {
        _ = try a.alloc(256, .of(u64));
    }
    // After the first collection the budget should have re-tuned to
    // at least the floor, and (since the rooted nodes are tiny) it
    // should not have shrunk below the floor either.
    try testing.expect(gc.target_blocks >= start_target);
}

test "Immix: collect() is re-entrant safe" {
    // Calling collect from inside collect (defensively, e.g. if the
    // worklist allocator path ever triggered a collection) must be a
    // no-op rather than a stack overflow.
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    gc.in_collect = true;
    gc.collect();
    try testing.expectEqual(@as(u64, 0), gc.stats_data.collections);
}

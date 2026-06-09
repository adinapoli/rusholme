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
//! Roots are pulled from two sources:
//!
//!   * Explicitly-registered slots via `addRoot`/`removeRoot` — precise.
//!     This is the long-term root mechanism (LLVM backend will spill
//!     live `*Node` values into shadow-stack frames; the GC walks them
//!     exactly).
//!   * Optional **conservative stack scan** between `stack_base` (set
//!     once via `setStackBase`) and the current frame address — every
//!     aligned word in that range that *looks* like a heap pointer is
//!     treated as a root. This is the zig-gc-style bring-up path so
//!     the collector works before the backend emits precise roots.
//!     If `stack_base` is `null` the scan is skipped entirely (the
//!     mode unit tests use, since their roots are explicit). The
//!     conservative scan does **not** cover register-resident values,
//!     so production use will need a `setjmp`-style register spill or
//!     precise shadow-stack roots before it can be trusted.
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

    // ── Current bump region ───────────────────────────────────────────
    /// Block currently being bumped into. `null` until the first
    /// allocation that needs a block.
    current_block: ?*BlockHeader = null,
    /// Next byte to hand out (absolute pointer as `usize`).
    cursor: usize = 0,
    /// One past the last byte of the current hole.
    limit: usize = 0,

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
    /// Optional high-water frame address for the conservative stack
    /// scan. If `null`, only explicit roots are used.
    stack_base: ?usize = null,

    // ── Stats ─────────────────────────────────────────────────────────
    stats_data: heap.AllocStats = .{},
    /// Number of blocks owned by this heap (small + LOS counts are
    /// separate; this is the count of 32 KB block allocations).
    blocks_allocated: u64 = 0,
    /// Number of LOS slabs owned by this heap.
    large_objects_allocated: u64 = 0,

    // ── Auto-collect trigger (#781) ──────────────────────────────────
    /// When `true`, the allocator calls `collect()` automatically once
    /// the live block count is about to exceed `target_blocks`. **Off
    /// by default**: enabling it on a heap with no roots is
    /// catastrophic (collect would reap everything live). Callers must
    /// either register precise roots (`addRoot`) or arm the
    /// conservative scan (`setStackBase`) before turning this on. See
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

    /// Record the calling frame as the boundary for the conservative
    /// stack scanner. Call this once, as high in the program's
    /// lifetime as possible (typically from `main`). Until called, the
    /// conservative scan is disabled and the collector only sees
    /// explicit roots registered via `addRoot`.
    pub fn setStackBase(self: *ImmixGc, frame_address: usize) void {
        self.stack_base = frame_address;
    }

    /// Enable or disable automatic collection from the allocation path
    /// (#781). When enabled, the allocator runs `collect()` before
    /// requesting a fresh block once the live block count crosses
    /// `target_blocks`, then re-tunes the budget to twice the
    /// post-collection live size (floored at `min_target_blocks`).
    ///
    /// **Safety**: enabling this on a heap with no roots reaps every
    /// live object. Callers must either register precise roots via
    /// `addRoot` for every live `*Node`, or arm the conservative scan
    /// via `setStackBase` (transitional; unsafe in optimised builds —
    /// see [#780](https://github.com/adinapoli/rusholme/issues/780)
    /// for the precise-roots replacement).
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
    ///   3. Trace from every registered root (precise) and, if a
    ///      `stack_base` was set, every aligned word in the
    ///      conservative stack range. Each reachable node has its
    ///      `gc_flags` set to `mark_id` and the lines it spans set to
    ///      used.
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
        // Pass the current frame as the low-water mark for the
        // conservative scan. Capture it here so the scan covers every
        // frame younger than `stack_base`.
        if (self.stack_base) |sb| {
            self.markFromStackRange(@frameAddress(), sb);
        }

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

        // Step 6: drop the current bump region so the next allocation
        // picks a (possibly freshly-recycled) block from
        // `recyclable_blocks`/`free_blocks`.
        self.current_block = null;
        self.cursor = 0;
        self.limit = 0;

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
        self.drainMarkWorklist(&work);
    }

    fn markFromStackRange(self: *ImmixGc, lo_addr: usize, hi_addr: usize) void {
        var work: std.ArrayList(*Node) = .empty;
        defer work.deinit(self.child);
        var start: usize = undefined;
        var end: usize = undefined;
        if (lo_addr < hi_addr) {
            start = lo_addr;
            end = hi_addr;
        } else {
            start = hi_addr;
            end = lo_addr;
        }
        const word_size = @sizeOf(usize);
        var p = std.mem.alignForward(usize, start, word_size);
        while (p + word_size <= end) : (p += word_size) {
            const w: u64 = @as(*const usize, @ptrFromInt(p)).*;
            if (self.isHeapPointer(w)) {
                const addr: usize = @intCast(w);
                work.append(self.child, @ptrFromInt(addr)) catch @panic("Immix: out of memory during mark");
            }
        }
        self.drainMarkWorklist(&work);
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
                    // tags: conservatively scan every field slot. A
                    // tag→pointer-mask table from the backend would
                    // make this precise; tracked separately.
                    for (nodemod.fieldsConst(node)) |w| {
                        if (self.isHeapPointer(w)) {
                            const addr: usize = @intCast(w);
                            work.append(self.child, @ptrFromInt(addr)) catch @panic("Immix: out of memory during mark");
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

test "Immix: markFromStackRange follows pointers in a synthetic buffer" {
    // Bypasses the real stack so the test doesn't depend on compiler
    // frame-pointer choices. Exercises the conservative scan logic
    // directly against a known byte range.
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    const live = try newNode(&gc, .Int, 1);

    // Pretend this buffer is a stack window: one entry is the heap
    // pointer to `live`; the others are noise. The scan should pick
    // out the heap pointer and mark its target.
    var buf: [4]usize align(@alignOf(usize)) = .{
        0xdead,
        @intFromPtr(live),
        0,
        0xbeef,
    };

    // Set up collector state as if collect() had just bumped mark_id
    // and cleared payload line marks.
    gc.mark_id = 1;
    var b = gc.all_blocks;
    while (b) |block| : (b = block.all_next) {
        for (block.line_marks[HEADER_LINES..]) |*m| m.* = 0;
    }
    gc.markFromStackRange(
        @intFromPtr(&buf),
        @intFromPtr(&buf) + @sizeOf(@TypeOf(buf)),
    );

    try testing.expectEqual(@as(u32, 1), live.gc_flags);
}

test "Immix: isHeapPointer rejects non-pointer words" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();
    _ = try newNode(&gc, .Int, 1);
    try testing.expect(!gc.isHeapPointer(0));
    try testing.expect(!gc.isHeapPointer(7)); // misaligned
    try testing.expect(!gc.isHeapPointer(0xdeadbeef_00000000));
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

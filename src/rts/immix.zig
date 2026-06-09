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

const std = @import("std");
const heap = @import("heap.zig");

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

/// Phase-2 Immix heap: block/line bump allocator over a child allocator.
///
/// The collector half lands in #72; until then, `free`/`collect`/roots
/// are no-ops and the heap grows monotonically. Even so, the on-disk
/// layout already carries every piece of metadata the collector will
/// need (per-line marks, per-block classification, intrusive lists),
/// so #72 is a logic-only addition.
pub const ImmixGc = struct {
    /// Source of 32 KB blocks and LOS slabs.
    child: std.mem.Allocator,

    // ── Block lists ───────────────────────────────────────────────────
    /// Blocks with no live lines, immediately ready for cold bumping.
    free_blocks: ?*BlockHeader = null,
    /// Blocks with at least one free line and at least one used line.
    /// In Phase 2 these only appear as the current bump block moves on
    /// (no collection yet recycles full blocks down).
    recyclable_blocks: ?*BlockHeader = null,
    /// Blocks with no free lines remaining.
    full_blocks: ?*BlockHeader = null,
    /// Singly-linked list of every block this heap owns, used solely by
    /// `deinit` to return them to the child allocator.
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

    // ── Stats ─────────────────────────────────────────────────────────
    stats_data: heap.AllocStats = .{},
    /// Number of blocks owned by this heap (small + LOS counts are
    /// separate; this is the count of 32 KB block allocations).
    blocks_allocated: u64 = 0,
    /// Number of LOS slabs owned by this heap.
    large_objects_allocated: u64 = 0,

    pub fn init(child: std.mem.Allocator) ImmixGc {
        return .{ .child = child };
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
        // Collection lands in #72. Until then this is a no-op so the
        // surrounding RTS can call it unconditionally.
        _ = ctx;
    }

    fn statsImpl(ctx: *anyopaque) heap.AllocStats {
        const self: *ImmixGc = @ptrCast(@alignCast(ctx));
        return self.stats_data;
    }

    fn addRootImpl(ctx: *anyopaque, slot: *u64) void {
        // Roots are needed by tracing (#72) and required to be precise
        // by evacuation (#73). Recorded as no-op here so the interface
        // is callable from day one — replaced with a real root set in
        // #72.
        _ = ctx;
        _ = slot;
    }

    fn removeRootImpl(ctx: *anyopaque, slot: *u64) void {
        _ = ctx;
        _ = slot;
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

        // Fast path: the requested allocation fits in the current hole.
        if (self.current_block != null) {
            if (self.bumpInCurrentHole(len, alignment)) |p| {
                self.stats_data.bytes_allocated += len;
                return p;
            }
        }

        // Slow path: current hole is too small. Advance to the next hole
        // in the current block, or move to a different block.
        if (self.advanceToHole(len, alignment)) {
            if (self.bumpInCurrentHole(len, alignment)) |p| {
                self.stats_data.bytes_allocated += len;
                return p;
            }
        }

        // The freshly-attached hole still didn't fit. This can only
        // happen if every hole we can reach is smaller than `len + α`
        // where α is the alignment padding — i.e. the block is too
        // fragmented to satisfy this medium-sized request. Allocate a
        // fresh block as overflow.
        //
        // Note: the Immix paper distinguishes a dedicated *overflow
        // cursor* (medium objects skip small holes and go to fresh
        // blocks to avoid wasting them). We use the simpler single-
        // cursor design here; a dedicated overflow path can be added
        // when fragmentation measurements (#72) show it pays off.
        const fresh = self.allocBlock() orelse return null;
        self.attachBlockAsCurrent(fresh);
        if (self.bumpInCurrentHole(len, alignment)) |p| {
            self.stats_data.bytes_allocated += len;
            return p;
        }
        // A fresh block whose entire payload couldn't satisfy `len`
        // would mean `len > PAYLOAD_BYTES`, which we already routed to
        // the LOS above.
        unreachable;
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
    /// and attach a fresh block as the new bump target. Used both when
    /// the current block is exhausted and when we need to bring in the
    /// first block.
    fn attachBlockAsCurrent(self: *ImmixGc, block: *BlockHeader) void {
        if (self.current_block) |old| {
            // Reclassify the previous block based on whether any free
            // lines remain after the bump.
            self.classifyAndFile(old);
        }
        self.current_block = block;
        const base = @intFromPtr(block);
        self.cursor = base + HEADER_BYTES;
        self.limit = base + BLOCK_SIZE;
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

    /// Request a fresh, zero-line-mark block from the child allocator
    /// (or reuse one from `free_blocks` / `recyclable_blocks`). The
    /// returned block is removed from any list it lived on.
    fn allocBlock(self: *ImmixGc) ?*BlockHeader {
        // Prefer recyclable blocks (paper: bump into existing holes
        // before grabbing a fresh block). With no collection yet,
        // recyclable_blocks is normally empty — but keeping the order
        // correct here means #72 only needs to add free-line reclamation
        // and the allocation policy already does the right thing.
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
        return self.newBlock();
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

    // ── Introspection helpers (test-only) ─────────────────────────────

    /// Address of the block that owns `ptr`, or `null` if `ptr` does
    /// not live in any of this heap's blocks. Pointer-only: large
    /// objects return `null`. Useful for tests asserting that small
    /// objects end up clustered as expected.
    pub fn blockOf(self: *ImmixGc, ptr: *const anyopaque) ?*BlockHeader {
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
    pub fn isLarge(self: *ImmixGc, ptr: *const anyopaque) bool {
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

test "Immix: GcAllocator.free/collect/addRoot are callable no-ops" {
    var gc = ImmixGc.init(testing.allocator);
    defer gc.deinit();

    const a = gc.gcAllocator();
    const p = try a.alloc(64, .of(u64));
    a.free(p[0..64], .of(u64));
    a.collect();

    var slot: u64 = 0;
    a.addRoot(&slot);
    a.removeRoot(&slot);

    try testing.expectEqual(@as(u64, 0), a.stats().bytes_freed);
    try testing.expectEqual(@as(u64, 0), a.stats().collections);
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

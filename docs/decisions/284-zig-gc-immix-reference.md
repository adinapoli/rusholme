# Study of zig-gc as a Reference for an Immix GC in Rusholme

**Issue:** [#284](https://github.com/adinapoli/rusholme/issues/284) — Research: Study zig-gc as reference for Immix GC implementation
**Status:** Research decision document
**Date:** 2026-06-07

## Scope

This document studies [Hejsil/zig-gc](https://github.com/Hejsil/zig-gc), a small
mark-and-sweep collector written in Zig, as a *reference* for the Immix collector
that Rusholme will build (epic #14, issues #70–#73). It then maps the lessons
onto Rusholme's concrete RTS — an arena exposed over a C ABI
(`src/rts/heap.zig`, `src/rts/node.zig`) — and recommends a phased
implementation plan.

The reference implementation is **not** Immix: it is a conservative, non-moving
mark-and-sweep allocator that wraps a child `std.mem.Allocator`. Its value is
pedagogical (root scanning, mark/sweep mechanics, allocator-wrapping idiom),
not architectural. The Immix algorithm itself comes from the paper, not from
zig-gc.

**Sources**

- zig-gc source: https://raw.githubusercontent.com/Hejsil/zig-gc/master/gc.zig
- zig-gc README (self-described: *"This GC is pretty bad, and mostly just a proof of concept"*): https://github.com/Hejsil/zig-gc
- Immix: Blackburn & McKinley, *"Immix: A Mark-Region Garbage Collector with
  Space Efficiency, Fast Collection, and Mutator Performance"*, PLDI 2008.
  PDF: https://users.cecs.anu.edu.au/~steveb/pubs/papers/immix-pldi-2008.pdf
- Rusholme design: `DESIGN.md` (§ Memory Management, decisions 8–11),
  `docs/rts-design.md`

---

## 1. zig-gc Architecture

zig-gc is a single file (`gc.zig` at repo root). It implements **conservative
mark-and-sweep** over allocations made through a wrapper allocator.

### 1.1 Object header / metadata layout

zig-gc does **not** use an inline object header. Instead it keeps an
out-of-band side table — an `ArrayList` of `Pointer` records, one per live
allocation:

```zig
const Pointer = struct {
    flags: Flags,
    memory: []u8,
};

const Flags = packed struct {
    checked: bool,
    marked: bool,
};
```

`memory` is the slice handed back to the mutator; `flags` holds the mark bit
(`marked`) and a "visited during this trace" bit (`checked`) to break cycles.
There is no per-object header in the heap payload itself — all GC metadata
lives in the parallel `ptrs` table. This is simple but means every pointer
lookup is an O(n) linear scan of the table (`findPtr`).

### 1.2 Allocator integration (and Zig-version drift)

The collector is a wrapper allocator that delegates the actual bytes to a
child allocator. It is constructed in the **old (pre-0.11)
`std.mem.Allocator` style**, where `Allocator` was a *struct of function
pointers* embedded by value via `@fieldParentPtr`:

```zig
pub inline fn init(child_alloc: *mem.Allocator) GcAllocator {
    return GcAllocator{
        .base = mem.Allocator{
            .allocFn  = allocFn,
            .resizeFn = resizeFn,
        },
        // ...
    };
}
```

It also uses pre-0.10 builtins throughout: `@intToPtr` / `@ptrToInt`,
`@frameAddress()`, `for ([_]void{} ** N) |_, i|` index-style loops, and
`@call(.{ .modifier = .never_inline }, ...)`. **This is Zig ~0.6–0.9 era code
and will not compile on modern Zig.**

> **API drift vs. Zig 0.16.** Modern `std.mem.Allocator` is a
> `{ ptr: *anyopaque, vtable: *const VTable }` pair, and the vtable has
> **four** entries — `alloc`, `resize`, `remap`, `free` — using
> `std.mem.Alignment` (an enum) rather than the old `u29` log2-align
> integers. Pointer-cast builtins are now `@intFromPtr` / `@ptrFromInt`, and
> the loop-index idiom is `for (slice, 0..) |x, i|`. Any code lifted from
> zig-gc must be rewritten against this interface; treat zig-gc as
> *algorithm pseudocode*, not as copy-paste source.

### 1.3 Root scanning — conservative stack scan

zig-gc finds roots by **conservatively scanning the C stack**. At init it
records a boundary frame address; at collection time it captures the current
frame address and treats the byte range between them as the stack:

```zig
// at init:
.start = @intToPtr([*]const u8, @frameAddress()),

// at collect:
pub fn collect(gc: *GcAllocator) void {
    @call(.{ .modifier = .never_inline }, collectNoInline, .{gc});
}
```

It then reads **every pointer-aligned word** in that range (at every byte
offset, making it tolerant of misaligned interior pointers), and for each word
asks `findPtr` whether it falls inside any tracked allocation:

```zig
for (gc.ptrs.items) |*ptr| {
    const ptr_start = @ptrToInt(ptr.memory.ptr);
    const ptr_end   = ptr_start + ptr.memory.len;
    if (ptr_start <= @ptrToInt(to_find_ptr) and @ptrToInt(to_find_ptr) < ptr_end)
        return ptr;
}
```

This is **conservative interior-pointer scanning**: any stack word that *looks
like* it points into a live block keeps that block alive. It is
moving-incompatible (you cannot relocate an object whose "root" might be a
false-positive integer), `never_inline` keeps the collector's own frame below
the scan boundary, and it does not reliably scan registers or spilled
callee-saved registers.

### 1.4 Mark phase

`mark(frame)` is the conservative scan applied recursively: scan a byte range
for pointer-shaped words, and for each that hits a tracked block, set
`marked` + `checked` and recurse into that block's payload (so the block's own
contents are treated as another "frame" to scan):

```zig
fn mark(gc: *GcAllocator, frame: []const u8) void {
    const ptr_size = @sizeOf(*u8);
    for ([_]void{} ** ptr_size) |_, i| {
        if (frame.len <= i) break;
        const frame2 = frame[i..];
        const len = (frame2.len / ptr_size) * ptr_size;
        for (std.mem.bytesAsSlice([*]u8, frame2[0..len])) |frame_ptr| {
            const ptr = gc.findPtr(frame_ptr) orelse continue;
            if (ptr.flags.checked) continue;   // cycle guard
            ptr.flags.marked  = true;
            ptr.flags.checked = true;
            gc.mark(ptr.memory);               // recurse into object body
        }
    }
}
```

Tracing is *fully conservative* even inside objects — it does not consult any
layout/tag information; it treats the whole object body as raw bytes and scans
for pointers.

### 1.5 Sweep phase

Sweep walks the side table, clears flags on survivors, and frees the rest back
to the child allocator:

```zig
fn sweep(gc: *GcAllocator) void {
    const child_alloc = gc.childAllocator();
    const ptrs = gc.ptrs.items;
    var i: usize = 0;
    while (i < gc.ptrs.items.len) {
        const ptr = &ptrs[i];
        if (ptr.flags.marked) {
            ptr.flags = Flags.zero;   // reset for next cycle
            i += 1;
            continue;
        }
        gc.freePtr(ptr);              // free + swap-remove from table
    }
}
```

### 1.6 Summary judgement

zig-gc is correct-ish for its toy purpose but has properties Rusholme must
**not** inherit: O(n) `findPtr` per scanned word (quadratic-ish collection),
fully conservative tracing (no layout precision), non-moving (so no
compaction/defrag), and a stale Allocator ABI. Its genuinely reusable ideas
are narrow: the *shape* of the allocator-wrapper, the mark/sweep control flow,
and the conservative-stack-scan technique as a fallback.

---

## 2. Design Patterns That Carry Over (and Those That Don't)

### Carries over

- **Allocator-as-wrapper / vtable swap.** The whole premise — a GC that *is*
  an allocator and delegates raw pages to a child allocator — matches
  Rusholme's design exactly (`DESIGN.md` decision 11; `docs/rts-design.md`
  "vtable-based `std.mem.Allocator`"). Rusholme's `heap.zig` seam (#70's
  `GcAllocator` interface) is the only place the RTS asks for memory, so
  swapping arena → Immix is a `heap.zig`-local change.
- **Two-phase mark/sweep control flow.** Mark roots → trace transitively →
  sweep unmarked. Immix keeps this skeleton; only *what* gets marked (lines +
  objects) and *how* free space is reclaimed (region recycling, not
  per-object free) change.
- **Mark bit + "visited" guard for cycles.** Immix needs the same cycle
  guard; in Rusholme this becomes a header bit (§4.2), not a side-table flag.
- **Conservative stack scanning as a *fallback*.** The `@frameAddress()` +
  scan-aligned-words + range-test technique is exactly what a conservative
  root scanner looks like. Rusholme can keep this in its back pocket for an
  initial bring-up (it lets the first GC work *before* the LLVM backend emits
  precise root information), then graduate to precision.

### Does not carry over

- **Out-of-band `ArrayList<Pointer>` side table.** O(n) `findPtr` is fatal at
  scale and is moving-incompatible. Immix derives liveness from block/line
  metadata indexed by *address arithmetic* (mask the pointer to find its
  block, shift to find its line), which is O(1). Rusholme should put
  mark/metadata **in headers and block side-metadata**, never in a global
  list.
- **Old `allocFn`/`resizeFn`/`u29` ABI.** Must be rewritten to the 0.16
  four-entry vtable (`alloc`/`resize`/`remap`/`free`) with
  `std.mem.Alignment`.
- **Fully conservative *tracing*.** Rusholme has something zig-gc lacks: a
  self-describing object format. `node.zig`'s `Node{ tag, n_fields }` header
  plus the GRIN type information means tracing can be **precise** — we know
  exactly which field slots are `*Node` pointers vs. unboxed scalars. We
  should not scan object bodies conservatively (§4.1).
- **Non-moving design.** zig-gc cannot relocate. Immix's whole point is
  opportunistic *evacuation*; precise roots are a prerequisite, so the
  conservative-stack design is at best transitional.

---

## 3. Gaps Between Simple Mark-Sweep and Immix

The Immix algorithm (Blackburn & McKinley 2008) replaces per-object free lists
with a **mark-region** heap. The deltas from zig-gc-style mark-sweep:

1. **Block / line organisation.** The heap is a set of fixed **blocks**
   (paper: 32 KB) subdivided into fixed **lines** (paper: 128 B). A block is a
   contiguous bump region; a line is the granularity of liveness and
   recycling. Rusholme's nodes (16 B header + 8 B/field) are small — a 128 B
   line holds several small nodes, which is the intended common case.

2. **Bump allocation within blocks.** Within a block the mutator allocates by
   bumping a cursor (`cursor`/`limit`), exactly like Rusholme's current
   arena — but bounded to a block and to the gaps between marked lines. This
   is why Rusholme's existing bump-pointer code is a *good* starting point:
   Immix allocation is bump allocation, just over a recyclable region instead
   of one global slab.

3. **Line marking vs. object marking.** Immix marks **both** objects (for
   tracing/cycle detection) and **lines** (for reclamation). When an object is
   marked live, the line(s) it spans are marked live. Free space is reclaimed
   at *line* granularity, not object granularity — there is no per-object
   `free`. This eliminates the free-list bookkeeping and fragmentation of
   classic mark-sweep. (Immix also uses *implicit marking* of the line
   *after* a small object to handle objects that don't end on a line
   boundary — a conservative one-line overestimate that avoids tracking exact
   object extents.)

4. **Recycling partially-free blocks.** After a collection, blocks are
   classified **free** (no live lines), **recyclable** (some free lines), or
   **full** (no free lines). The allocator preferentially bump-allocates into
   the *holes* (runs of free lines) of recyclable blocks before grabbing a
   fresh free block. zig-gc has no analogue — it just frees individual
   objects.

5. **Opportunistic evacuation / defragmentation.** When fragmentation is
   high, Immix *evacuates* objects out of lightly-occupied blocks into other
   blocks during the same mark phase (mark-region + copying = a "mark-copy"
   hybrid), then frees the emptied blocks. This requires **moving** objects
   and therefore **precise roots and forwarding pointers** — the single
   biggest reason Rusholme cannot stay with conservative scanning long-term.
   Evacuation is *opportunistic*: candidate blocks are selected from the
   previous cycle's stats, and if space runs out mid-evacuation it falls back
   to in-place marking.

6. **Medium / large objects.**
   - **Small objects** (≤ line) and **medium objects** (> line but ≤ block)
     are bump-allocated; medium objects that don't fit in the current block's
     hole trigger **overflow allocation** into a fresh block to avoid wasting
     the tail of the current one.
   - **Large objects** (> block) bypass the line/block machinery entirely and
     live in a separate **large object space (LOS)**, managed by a simpler
     non-moving scheme (mark bit + free on sweep). Rusholme will rarely
     allocate large nodes (a node is header + N×8 B), but big arrays/`String`
     payloads belong there.

In short: zig-gc gives the mark/sweep *loop*; Immix adds the *heap structure*
(blocks, lines, holes, LOS) and the *reclamation/relocation policy* on top of
it.

---

## 4. Design Recommendations for Rusholme

Rusholme's setting (from `src/rts/heap.zig`, `src/rts/node.zig`,
`docs/rts-design.md`):

- The RTS is Zig, exposed to LLVM-generated GRIN code over a C ABI:
  `rts_alloc(tag, n_fields)`, `rts_store_field`, `rts_load_field`,
  `rts_store`.
- All heap objects are uniform `Node`s: a 16-byte header (`tag: u64`,
  `n_fields: u32`, `_pad: u32`) followed by `n_fields` 8-byte slots. Slots
  hold either `*Node` (as `@intFromPtr`) or unboxed scalars — *which is which
  is determined by the tag*.
- The Phase-1 heap is an arena over `page_allocator` — grow-only, no
  reclamation.
- Roots live on the stack of generated code.

### 4.1 Precise vs. conservative root scanning — **recommend precise, with a conservative bring-up phase**

Rusholme should target **precise** root scanning, for two decisive reasons:

1. **Immix evacuation requires it.** You cannot relocate an object reachable
   only through a maybe-pointer. Conservative roots pin objects and forbid
   moving — which forecloses issue #73 (defrag) entirely.
2. **Rusholme can afford precision that zig-gc could not.** Object *bodies*
   are already self-describing: given a `Node`'s tag, the compiler knows
   exactly which slots are pointers. So **tracing is precise for free** —
   `mark` walks `fields(node)`, and for each slot that the tag says is a
   pointer, recurses. No conservative body scan, no false retention inside
   the heap.

The hard part is precise *roots* (the stack), because that needs the LLVM
backend to tell the GC where live `*Node` values are at each safepoint.
Concretely:

- **Preferred: an explicit shadow stack.** The GRIN→LLVM backend already
  controls codegen. Have it spill live `*Node` roots into an explicit,
  RTS-managed shadow-stack frame across allocation calls (the points where GC
  can trigger). The GC then walks the shadow stack precisely — no
  register/stack guessing. This is the LLVM-idiomatic `gc "shadow-stack"`
  approach. It is simpler to get correct than LLVM `statepoint`/stack-map
  lowering and is moving-safe (the GC can rewrite shadow-stack slots after
  evacuation). This is the recommended long-term design.
- **Bring-up shortcut: conservative stack scan (the zig-gc technique).** For
  the *first* working collector (#72, in-place, non-moving), a conservative
  `@frameAddress()`-based scan lets us test mark/sweep before the backend
  emits shadow-stack spills. It must be flagged as transitional and **must be
  disabled before #73**, because it blocks moving.

> **Architectural-coherence note (per CLAUDE.md §9).** The issue framing
> "study a mark-and-sweep GC" must not lead us to copy zig-gc's *conservative
> tracing of object bodies*. Rusholme's `Node` tags make precise tracing
> available and correct; using conservative body scans would be a regression
> dressed as a reference. Trace bodies precisely; only the *root* phase may
> be temporarily conservative.

### 4.2 Header bits needed

Rusholme is lucky: the `Node` header has a free 32-bit hole — `_pad: u32`
(`src/rts/node.zig`) — currently zeroed and unused. GC metadata fits there
with zero layout change to the 16-byte header and **no ABI break** for
LLVM-generated code (which only reads `tag` and `n_fields`). Repurpose `_pad`
into a flags word:

- **`mark` bit** (1): set during trace; used by sweep and as the cycle guard
  (replacing zig-gc's `checked`+`marked` with a single bit + a
  flip-the-sense-each-cycle convention, or two bits if simpler).
- **`forwarded` bit** + **forwarding pointer** (for #73): when an object is
  evacuated, mark it forwarded and store the new address. With only a 32-bit
  pad this is tight for a 64-bit forwarding pointer; the standard trick is to
  **store the forwarding pointer in field[0]** of the old object (it's dead
  after evacuation) and use one pad bit as the "forwarded" flag. This keeps
  the header 16 bytes.
- **(optional) `pinned` bit**: needed if/while any conservative roots remain
  (a conservatively-reachable object must not move).

**Line marks are not header bits** — they live in **per-block side metadata**
(a small bitmap or byte array at a known offset in/beside each block), indexed
by line index. Object mark → set the line-mark byte(s) for the lines the
object spans. This is the Immix-specific structure that has no zig-gc analogue
and is the core of issue #71.

So: object-level bits go in the recovered `_pad`; line/block-level marks go in
block metadata. No change to `n_fields`/`tag`, no change to the LLVM-visible
ABI.

### 4.3 Keep the arena as `--rts=arena` opt-in

`DESIGN.md` (decisions 8 & 11) and `docs/rts-design.md` explicitly want a
*swappable* allocator. The arena must stay — it is the fastest "allocator"
(never collects), invaluable for short-lived programs, for differential
testing ("run the same program under Arena vs. Immix and compare",
`DESIGN.md`), and as the GC's *page source*. Mechanics:

- Keep `heap.zig`'s seam as the single source of truth (it already is —
  #70's `GcAllocator` interface). Behind it, choose backend at startup from a
  config: `enum RtsAllocator { arena, immix }`.
- Surface this as a compiler/RTS flag **`--rts=arena|immix`** (default
  `immix` once it lands; `arena` remains supported and CI-tested).
- Immix's block allocator should request its 32 KB blocks from a *child*
  allocator (page allocator), exactly like zig-gc wraps a child — so the
  arena and Immix share the same "where do raw pages come from" plumbing.
- Critically, this keeps `node.zig`/`rts_alloc` **unchanged**: they call the
  heap seam; whether that's arena bump or Immix bump is invisible to them.
  (One caveat: under a *moving* Immix, `rts_alloc` callers must not cache raw
  `*Node` across allocation points without going through the shadow stack — a
  backend invariant to enforce in #72/#73.)

### 4.4 Phased implementation plan (mapping to #70–#73)

| Issue | Deliverable | Maps to |
|------|-------------|---------|
| **#70** Allocator interface | The `GcAllocator` `{ptr, vtable}` interface behind `heap.zig` (alloc/free/collect/stats + root registration), with the arena as first concrete impl. **No collection yet.** | zig-gc's *allocator-wrapper shape* (§2), reframed to the modern ABI. |
| **#71** Block & line allocator | The Immix heap structure: 32 KB blocks from the child allocator, 128 B lines, per-block line-mark side metadata, bump allocation into block holes, block classification (free/recyclable/full), recyclable-block recycling, medium-object overflow allocation, and a large-object space for `> block` allocations. Still **no reclamation logic** — just the geometry + bump path. | Immix paper §2 (block/line/region); no zig-gc analogue. |
| **#72** Mark-and-sweep collection | Tracing + reclamation: precise body tracing via `Node` tag/`fields` (recurse into pointer slots only); object **and** line marking; sweep = reclaim unmarked lines/blocks (no per-object free). Roots: ship a **conservative `@frameAddress()` stack scan** (the zig-gc technique) as a bring-up, followed by the precise **shadow-stack** walk once the backend emits root spills. Use the recovered `_pad` mark bit + cycle guard. In-place only (non-moving). | zig-gc's *mark/sweep loop* + *conservative root scan* (§1.3–1.5), bodies traced precisely (§4.1). |
| **#73** Opportunistic defragmentation | Evacuation: per-cycle fragmentation stats select candidate blocks; evacuate live objects into other blocks during marking; install forwarding pointers (forwarded bit + field[0]); fix up references and shadow-stack roots; free emptied blocks; fall back to in-place marking on space exhaustion. **Requires precise roots** — remove/forbid the conservative scanner here (pinning otherwise blocks moving). | Immix paper §4 (opportunistic evacuation); precise-root prerequisite. |

**Follow-up issues to file during implementation** (per CLAUDE.md §5):

- "Backend: emit shadow-stack root spills at GC safepoints" — prerequisite
  for precise roots; blocks #72's precise mode and all of #73.
- "RTS: forbid caching raw `*Node` across allocation points under moving GC"
  — a backend invariant + verification; introduced by #73's moving semantics.
- "Remove conservative stack scanner once shadow stack lands" — the explicit
  migration step (it must not survive into #73).

---

## 5. Bottom Line

zig-gc is worth reading for exactly three things: the **allocator-wrapper
shape**, the **mark/sweep control flow**, and the **conservative
`@frameAddress()` root-scan trick** (useful only as a bring-up scaffold).
Everything else about it — the O(n) side-table, fully conservative tracing,
non-moving design, and the obsolete `u29` Allocator ABI — is the *opposite* of
what Rusholme needs and must be left behind. Rusholme's `Node` tag header
makes **precise tracing free**, the recovered `_pad` field gives mark/forward
bits **without an ABI change**, and the `heap.zig` seam makes the
**arena-vs-Immix swap** a configuration choice. The real work (#71–#73) is the
Immix *heap structure* and *evacuation policy* from Blackburn & McKinley 2008,
for which zig-gc offers no guidance — the paper is the reference there, not
the repo.

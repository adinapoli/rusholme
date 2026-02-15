# Immix: A Mark-Region Garbage Collector

> Authors: Stephen M. Blackburn, Kathryn S. McKinley
> Venue: PLDI 2008
> Retrieved: 2026-02-15

## Abstract

Immix is a mark-region garbage collector that achieves space efficiency, fast
collection, and good mutator performance. It allocates and reclaims memory in
contiguous regions, operating at a coarse block grain (32KB blocks) and falling
back to a finer line grain (128B lines) when necessary. It introduces
*opportunistic defragmentation* — mixing copying and marking in a single pass.

## Key Design

- **Blocks and lines**: Heap is divided into 32KB blocks, each subdivided into
  128-byte lines. Allocation is bump-pointer within blocks.
- **Mark-region collection**: Live objects are marked; entire lines containing
  no live objects are reclaimed. This gives fine-grained reclamation without
  per-object freelists.
- **Opportunistic defragmentation**: When fragmentation is detected, Immix
  selectively copies objects out of fragmented blocks during the same marking
  pass — combining the benefits of copying and mark-sweep.

## Performance

Comprehensive evaluation showed Immix improves total application performance
by 7–25% over canonical GCs (mark-sweep, semi-space, mark-compact). It achieves
space efficiency comparable to mark-compact and collection times similar to
mark-sweep, with excellent mutator locality.

## Relevance to Rusholme

- Immix is the sweet spot between simplicity and performance for a toy compiler
- Simon Marlow noted in 2010 that GHC's allocator is "quite similar to Immix"
  and proposed Immix-style old-gen sweeping for near-real-time GC in Haskell
- An LLVM-based Immix implementation exists (github.com/pauek/immix-gc)
- Immix can be implemented as a custom Zig `std.mem.Allocator`
- GRIN's explicit memory operations make Immix integration natural

## Links

- Direct PDF: https://users.cecs.anu.edu.au/~steveb/pubs/papers/immix-pldi-2008.pdf
- ACM Digital Library: PLDI 2008
- Simon Marlow's haskell-cafe discussion (2010):
  https://mail.haskell.org/pipermail/haskell-cafe/2010-June/078745.html

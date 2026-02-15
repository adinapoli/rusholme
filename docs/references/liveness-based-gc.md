# Liveness-Based Garbage Collection for Lazy Languages

> Authors: Prasanna Kumar K, Amitabha Sanyal, Amey Karkare
> arXiv: 1604.05841 (April 2016)
> Retrieved: 2026-02-15

## Summary

This paper addresses reducing memory requirements for lazy first-order
functional programs by analysing the *liveness* of heap-allocated data. Unlike
standard reachability-based GC (which keeps everything reachable from roots),
liveness analysis determines which objects will actually be *used* in the future.
This allows the GC to reclaim reachable-but-not-live objects, including
closures.

## Key Insight

In a lazy language, many reachable objects (thunks, closures) may never actually
be forced. Standard GC keeps them alive because they're reachable. Liveness
analysis proves they'll never be needed, enabling earlier reclamation and
significant peak memory reduction.

## Relevance to Rusholme

- Could be combined with GRIN's whole-program analysis to improve GC precision
- Complements ASAP: liveness analysis for what can be statically deallocated,
  runtime GC only for the remainder
- Particularly valuable for lazy languages where thunk accumulation ("space
  leaks") is a real problem

## Links

- arXiv: https://arxiv.org/abs/1604.05841
- Direct PDF: https://arxiv.org/pdf/1604.05841

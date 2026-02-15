# Cloaca: A Concurrent Hardware Garbage Collector for Non-Strict Functional Languages

> Venue: Haskell Symposium 2024 (co-located with ICFP), Milan
> DOI: https://doi.org/10.1145/3677999.3678277
> Retrieved: 2026-02-15

## Summary

Cloaca is an FPGA-based hardware implementation of a concurrent, hybrid garbage
collector designed for pure non-strict functional languages (specifically
Haskell). It combines mark-and-sweep tracing with one-bit reference counting.

## Key Results

- Achieves **8.6% of GHC's GC wall-clock time** on average across benchmarks
- Zero-cost write barriers via hardware-level synchronisation
- Runs concurrently with graph reduction without impacting mutator performance
- Hybrid design: reference counting handles short-lived objects efficiently,
  mark-and-sweep handles cycles

## Relevance to Rusholme

Primarily interesting as a research reference rather than directly usable:
- Not applicable to software-only runtimes
- However, the *hybrid refcount + tracing* idea could inform our software GC
  design — use refcounting for easy cases, tracing for cycles
- Worth tracking for future hardware-accelerated functional language runtimes

## Links

- DOI: https://doi.org/10.1145/3677999.3678277
- ACM Digital Library: Haskell Symposium 2024

# ASAP: As Static As Possible Memory Management

> Author: Raphaël L. Proust
> Institution: University of Cambridge, Computer Laboratory
> Report: UCAM-CL-TR-908, 2017
> Retrieved: 2026-02-15

## Summary

ASAP (As Static As Possible) is a compile-time automatic memory management
strategy. The compiler performs whole-program analysis to insert deallocation
calls at the point where values become provably useless — essentially generating
a specialised garbage collector for each compiled program.

## Key Properties

- **Safe**: prevents programs from dereferencing dangling pointers
- **Complete**: all values no longer useful are eventually deallocated
- **Timely**: deallocation occurs as early as statically provable; timeliness
  is comparable to liveness-based GC and better than reachability-based GC
- **No runtime GC**: all deallocation decisions are made at compile time
- **Whole-program**: requires access to the full program for analysis

## Challenges

- Handling polymorphism and mutability adds complexity
- Whole-program analysis can increase compile times
- Still at research stage — no production implementations yet

## Relevance to Rusholme

ASAP is exceptionally interesting for Rusholme because:
- GRIN already performs whole-program analysis, so the infrastructure is there
- GRIN explicitly represents memory operations (`store`/`fetch`/`update`),
  making it natural to insert static deallocation
- Could be Rusholme's differentiating feature: a Haskell compiler that needs
  no (or minimal) runtime GC
- Could be layered as an optimisation pass: ASAP where provable, fallback to
  Immix where not

## Links

- Direct PDF: https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-908.pdf

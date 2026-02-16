# Decision 002: Zero-Leak Enforcement Strategy

**Status:** Accepted
**Date:** 2026-02-16
**Issue:** #107

## Context

Rusholme is written in Zig, which uses manual memory management. Every heap
allocation must be paired with a corresponding deallocation. Memory leaks are
unacceptable — they indicate bugs in resource ownership and will compound as the
compiler grows. We need a strategy to detect and prevent leaks from being merged
into the codebase.

## Options Evaluated

### 1. Zig `std.testing.allocator` Only

Zig's test framework provides `std.testing.allocator`, which wraps a
`GeneralPurposeAllocator` configured for leak detection. Tests using this
allocator **automatically fail** if any allocation is not freed by the end of
the test. The allocator reports the exact source location of the leaked
allocation with a stack trace.

**Pros:**
- Zero setup cost — built into Zig's standard library
- Automatic — tests fail on leak without manual checks
- Exact source location of leaked allocation
- Already used consistently across all Rusholme tests

**Cons:**
- Only detects leaks in Zig-managed allocations
- Cannot see leaks inside C libraries (e.g. LLVM C API)

### 2. Valgrind (External Tool)

Valgrind's Memcheck tracks all heap allocations (malloc/free) and reports leaks,
use-after-free, and uninitialised reads. Works with any compiled binary.

**Pros:**
- Catches leaks in C library code (LLVM C API bindings)
- Detects use-after-free and buffer overruns
- Language-agnostic — works on the final binary

**Cons:**
- Significant slowdown (~10-20x)
- Requires building with `c_allocator` for Zig code to be visible
- Linux-only (macOS support via Valgrind is limited/broken)
- Adds CI complexity and time
- Noisy output from C library internals (LLVM suppressions needed)

### 3. Zig `GeneralPurposeAllocator` in `main.zig`

Use GPA with a `.deinit()` == `.ok` assertion in the compiler's main entry
point, so that even non-test invocations detect leaks in debug builds.

**Pros:**
- Catches leaks during manual testing / development runs
- No external tooling needed
- Can be disabled in release builds for performance

**Cons:**
- Only effective when someone runs the compiler in debug mode
- Same limitation as option 1 for C interop

### 4. Hybrid: `std.testing.allocator` + GPA in `main` + Valgrind for C interop

Combine all three approaches, each covering a different layer:

| Layer | Tool | Catches |
|-------|------|---------|
| Unit tests | `std.testing.allocator` | Zig-side leaks per test |
| Debug builds | GPA with `.deinit()` check | Zig-side leaks in full runs |
| C interop | Valgrind (periodic, not every CI run) | LLVM C API leaks |

## Recommendation

**Option 4: Hybrid approach**, with the following priorities:

1. **Mandatory (now):** All tests MUST use `std.testing.allocator` (or
   `ArenaAllocator` wrapping it). This is already the case — codify it as
   policy.

2. **Mandatory (now):** `main.zig` debug builds MUST use GPA with a
   `.deinit()` assertion. This catches leaks during development.

3. **Deferred (when LLVM backend is active):** Add a Valgrind CI step that
   runs end-to-end tests with Valgrind + suppression file. This only becomes
   relevant once we're calling LLVM C API functions at runtime (#53, #54, #55).
   Until then, it's overhead with no benefit.

## Rationale

- The audit of existing tests shows **100% consistency** — all heap-allocating
  tests already use `std.testing.allocator`. The infrastructure is already
  working; we just need to codify the policy and add the GPA check to `main`.

- Valgrind for C interop is important but premature. The LLVM bindings (#53)
  exist but aren't yet exercised in tests. When Epic #9 (LLVM Backend) is
  active, a Valgrind step should be added.

- The GPA `.deinit()` check in `main.zig` is trivially cheap to add now and
  catches leaks during any `zig build run` invocation in debug mode.

## Implementation

1. Add "Zero-leak policy" section to CONTRIBUTING.md
2. Verify all tests use `std.testing.allocator` (audit: already compliant)
3. Add GPA `.deinit()` check to `main.zig`
4. Add a Valgrind CI step later (tracked as separate issue, depends on LLVM backend)

# Decision 003: Calling Convention for Compiled Haskell

**Status:** Accepted
**Date:** 2026-02-16
**Issue:** #66

## Context

Rusholme will compile Haskell code to LLVM IR, which will then be compiled to
machine code. The calling convention determines how function calls are
implemented, how arguments are passed, and how partial application and laziness
are handled. This is a critical design decision that affects the runtime,
codegen, and performance.

## Options Evaluated

### 1. Eval/Apply (GHC's current approach)

Caller evaluates arguments, callee receives evaluated values. Each function takes
a fixed number of arguments.

**Pros:**
- Well-studied and production-proven (GHC uses it)
- Simpler for codegen than push/enter
- Good performance for fully saturated calls

**Cons:**
- Complex handling of partial application (requires wrapper functions / thunks)
- More complex runtime
- Not directly compatible with standard C calling conventions

**LLVM Compatibility:** Requires custom calling convention or significant wrapper
layer to map to LLVM's model.

### 2. Push/Enter

Arguments pushed onto stack, callee pops what it needs. Works well with partial
application.

**Pros:**
- Natural for partial application
- Traditional approach (used by early functional compilers)

**Cons:**
- Poor LLVM backend compatibility — LLVM is designed for register-based C-like
  calls, not stack-structured calls
- Requires custom stack management that fights LLVM's model
- Performance can be worse for fully saturated calls

**LLVM Compatibility:** Very poor — essentially requires a complete wrapper
around LLVM's calling convention implementation.

### 3. CPS (Continuation-Passing Style)

Every function takes an explicit continuation argument. Control flow becomes
explicit via continuations.

**Pros:**
- Natural for lazy evaluation
- No stack needed (heap-allocated continuations)
- Elegant theoretical foundation

**Cons:**
- Dramatically increases code size (every call becomes an extra continuation)
- Not LLVM-friendly — LLVM's tail-call optimization helps but CPS is
  non-idiomatic
- Complex to implement efficiently for real code

**LLVM Compatibility:** Poor — LLVM has tail-call optimization but CPS is
non-idiomatic and produces verbose IR.

### 4. Direct Style with Thunks

Standard C-like function calls where unevaluated expressions are represented as
thunk objects. Thunks are evaluated by calling a function pointer.

**Pros:**
- Perfect LLVM compatibility (direct style matches C/Fortran calling
  conventions)
- Simple runtime — thunks are just function pointers with payloads
- GRIN already models thunks explicitly, so alignment is natural
- Easiest to implement from scratch with minimal complexity

**Cons:**
- Not as optimized for partial application as eval/apply push/enter
- Requires explicit thunk allocation and indirection overhead

**LLVM Compatibility:** Excellent — matches C calling conventions that LLVM is
designed for.

## Recommendation: Direct Style with Thunks

### Rationale

For a toy compiler like Rusholme, the key constraints differ from GHC:

1. **LLVM Compatibility is Paramount:** Direct style maps cleanly to LLVM's
   calling conventions. LLVM is designed for and optimized around C-like calls.
   Trying to use eval/apply, push/enter, or CPS requires fighting the tool's
   design, adding complexity and potentially suboptimal code generation.

2. **Implementation Simplicity:** Direct style with thunks is the simplest
   approach to understand and implement correctly:
   - Thunks are evaluated by calling a function pointer
   - No exotic calling convention mechanics
   - No continuation management machinery
   - Direct translation from GRIN's thunk model

3. **GRIN Alignment:** GRIN already has an explicit thunk representation with
   `Update` and `Eval` operations. Direct style with thunks maps 1:1 to this
   model without additional translation layers.

4. **Resource Constraints:** Rusholme is a toy compiler with limited development
   time. The path to "Hello World" (M1 milestone) should prioritize correctness
   and simplicity over the last 10% of performance that eval/apply provides.

For a research/teaching compiler targeted at getting a working end-to-end
pipeline, direct style with thunks is pragmatically optimal. Performance-
driven optimizations like eval/apply can be layered on later if needed.

### Implementation Approach

**Thunk Representation:** A thunk is a lightweight struct with a function pointer
and optional payload:

```zig
const Thunk = struct {
    // Entry point: forces evaluation by calling this function
    fn_ptr: *const fn (*Thunk) void,
    // Payload: constructor arguments or data
    payload: ?*anyopaque,
};
```

**Evaluation:** Calling a thunk forces its evaluation:

```zig
fn evaluate(thunk: *Thunk) void {
    thunk.fn_ptr(thunk);
}
```

**Codegen Strategy (LLLM → LLVM):**

1. For each GRIN application, generate LLVM IR that:
   - Allocates thunks on the heap using the runtime's allocator
   - Calls thunk entry points directly using standard LLVM `call` instruction
   - Passes arguments via LLVM's standard calling convention

2. For each GRIN case expression, generate LLVM IR that:
   - Uses `switch` instruction to pattern-match on evaluated thunks
   - Extracts payload from thunk struct when needed

3. Link with minimal Zig runtime that provides:
   - Heap allocator for thunk allocation
   - Entry point initialization
   - Basic IO primitives (putStrLn, getLine)

### Performance Considerations

Direct style is not as fast as GHC's eval/apply for workloads heavy on partial
application. However:

- For a toy compiler, correctness and simplicity outrank performance
- LLVM's optimizer will optimize direct style calls effectively
- Future optimization passes (GRIN optimizations epic, M3) can be layered on top
- The runtime overhead of thunk indirection is acceptable for the initial goal

## Decision

**Choose:** Direct style with thunks

**Implementation:**
- Thunks as function pointers with heap-allocated payloads
- Standard LLVM calling conventions (no custom ABI)
- Minimal Zig runtime for thunk allocation and management

**Next Step:**
- Implement LLVM codegen skeleton (#54) using direct style calling convention
- Implement Zig runtime heap allocator for thunks (#56)

## References

- Marlow & Peyton Jones, 'Making a Fast Curry: Push/Enter vs. Eval/Apply for
  Higher-Order Languages', JFP 2006
- GHC calling convention:
  https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/haskell-execution/calling-convention
- GRIN calling model: Hruska et al. 2020 (see docs/references/grin-overview.md)
- LLVM calling conventions:
  https://llvm.org/docs/LangRef.html#calling-conventions

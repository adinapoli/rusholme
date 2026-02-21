# Rusholme Run-Time System (RTS) Design

This document outlines the proposed design for the Rusholme compiler's Run-Time System (RTS), drawing inspiration from the GHC RTS but adapted for a Zig-based toolchain.

## High-Level Architecture

In a lazy functional language like Haskell, the RTS governs garbage collection (GC), thunk evaluation, threading, and more. GHC's RTS is written in C/C-- and linked against compiled Haskell binaries.

For Rusholme, we intend to write the RTS entirely in Zig.

### 1. RTS Responsibilities
- **Garbage Collection (GC):** A copying, generational, or mark-and-sweep GC. Zig's allocators can manage underlying OS memory, but the RTS will trace roots and collect dead thunks/closures.
- **Evaluator / Machine Model:** An evaluator (e.g., STG machine) that knows how to enter a thunk, interact with the runtime stack, and update thunks with computed values to enforce laziness.
- **Entry Point Integration:** Instead of standard C `main`, the compiled binary delegates to an RTS `main`, which initializes the heap/state and begins evaluating the compiled `Main.main` entry point.

### 2. ABI and Interface
A strict Application Binary Interface (ABI) needs to be defined between the Rusholme-compiled code and the Zig RTS.
- **Allocation:** Compiled code calls memory allocation routines (`rusholme_alloc`) provided by the RTS to create new thunks or closures on the GC heap.
- **Metadata:** The compiler emits metadata that the GC uses to understand object layouts and trace pointers.

### 3. Compilation & Linking Strategy
Since Rusholme is written in Zig, the generated code (whether emitted as C code, LLVM IR, or Zig source) will be linked with the compiled Zig RTS structure (`librusholme_rts.a` or via `zig build-exe`).

### 4. The Execution Flow
1. The OS starts the process and vectors into the Zig RTS `main` function.
2. The Zig RTS initializes its internal state (memory allocators, stacks, garbage collector structures).
3. The Zig RTS makes an external call to the generated `rusholme_Main_main` closure.
4. The generated code leverages the RTS for allocations (`rusholme_alloc`) and yielding (if threading/concurrency is supported).
5. At exit, control yields back to the RTS for clean shutdown.

## Advantages of Zig
Using Zig for both the Rusholme compiler and its RTS gives us a major advantage: **Pervasive Code Sharing**.
- Data structures representing a `Closure` or `Thunk` can be defined once in a shared Zig package.
- The compiler uses these structs to calculate accurate offsets when generating code.
- The RTS uses the exact same structs to parse closures during GC.
- This eliminates the class of bugs where the compiler and RTS subtly disagree on object memory layouts.

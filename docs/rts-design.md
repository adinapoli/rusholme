# Rusholme Run-Time System (RTS) Design

This document outlines the design for the Rusholme compiler's Run-Time System (RTS). Unlike GHC, which uses a C/C-- RTS with an STG machine and a bespoke garbage collector, Rusholme's RTS is written entirely in Zig, utilizes the GRIN (Graph Reduction Intermediate Notation) evaluator, and heavily leverages Zig's `std.mem.Allocator` interface for a flexible, phased approach to memory management.

## High-Level Architecture

The RTS serves as the foundation for executing compiled Rusholme code, providing memory management, thunk evaluation, and runtime startup.

### 1. Evaluator / Machine Model
Rusholme skips STG and Cmm entirely, using **GRIN** as its core intermediate representation before sending code to LLVM. GRIN explicitly represents memory operations (`store`, `fetch`, `update`) and thunks as first-class IR constructs. The RTS will provide the necessary runtime primitives to support these memory operations, ensuring that the lazy evaluation (call-by-need) semantics are strictly preserved across different targets.

### 2. Phased Memory Management Strategy
Rusholme avoids building a monolithic, complex garbage collector from day one (unlike GHC's generational copying GC). Instead, it adopts a phased strategy leveraging Zig's vtable-based `std.mem.Allocator`:
- **Phase 1: Arena / Region Allocator:** Utilizing Zig's `std.heap.ArenaAllocator` for bulk memory deallocation. This provides a fast, simple start for early milestones.
- **Phase 2: Immix (Mark-Region GC):** A custom Zig `Allocator` implementing the Immix algorithm (opportunistic defragmentation, high space efficiency) for robust runtime collection.
- **Phase 3: ASAP (As Static As Possible):** Utilizing GRIN's whole-program analysis to insert compile-time static deallocations. The goal is to eliminate runtime GC overhead for statically-deallocatable values, falling back to Immix only where necessary.

Because the entire runtime and its internal tools are parameterized over the `std.mem.Allocator` interface, switching between these phases requires swapping out the allocator instance at startup—not rewriting the runtime codebase.

### 3. ABI and Interface
The interface between the compiled GRIN output and the Zig RTS relies on a strict Application Binary Interface (ABI):
- **Allocation:** Compiled code calls standard RTS allocator functions (backed by the active `std.mem.Allocator`) for `store` operations and closure creation.
- **Thunk Updates:** The RTS exposes functions to handle the `update` of a thunk with its evaluated form.

### 4. Compilation & Linking Strategy
With LLVM as the primary backend emitting native code or WebAssembly, the compiled object files will be linked against the Zig RTS (e.g., via `zig build-exe` or by linking a static `librusholme_rts.a`).

### 5. Execution Flow
1. The OS starts the process, invoking the Zig RTS `main` function.
2. The RTS initializes the specific memory allocator (Arena or Immix) and its internal state.
3. The RTS invokes the compiled `rusholme_Main_main` closure.
4. The generated GRIN code executes, making calls into the RTS for `store`, `fetch`, and `update` memory operations.
5. On completion, control yields back to the RTS to perform clean shutdown and free allocated regions via the `Allocator` interface.

## The Zig Advantage
Using Zig for both the compiler and the RTS offers pervasive code sharing:
- Data structures for closures and heap objects can be defined once in a shared Zig package.
- The compiler uses these exact structs to calculate memory offsets during code generation.
- The RTS uses the same structs to traverse memory during garbage collection.
- This unified memory model eliminates bugs caused by disagreements between the compiler's emitted layouts and the runtime's expectations.

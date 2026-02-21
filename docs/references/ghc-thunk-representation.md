# GHC Thunk Representation — Research Notes

> Retrieved: 2026-02-21
> Purpose: Inform Rusholme's thunk design (runtime, GRIN codegen, GC interaction)

## 1. Uniform Closure Layout

Every GHC heap object is a **closure**: a header followed by a payload.
The header's first word is an **info pointer** into static memory.

```
+------------------+---------------------+
|  info pointer    |  payload (free vars) |
+------------------+---------------------+
         |
         v
+--------+--------+------+=================+
| layout | type   | srt  |  entry code...  |
+--------+--------+------+=================+
                         ^
                   info pointer lands here
              (TABLES_NEXT_TO_CODE layout)
```

With `TABLES_NEXT_TO_CODE` (GHC's default), the info table sits *immediately
before* the entry code. The info pointer points at the boundary — jump forward
to enter the closure, read backward for metadata. One pointer, two purposes.

The **info table** (`StgInfoTable`) contains:

| Field    | Purpose |
|----------|---------|
| `layout` | Payload shape for the GC: (pointers, non-pointers) counts or a bitmap |
| `type`   | Closure type tag (`THUNK`, `CONSTR`, `FUN`, `BLACKHOLE`, `IND`, ...) |
| `srt`    | Static Reference Table — static closures reachable from this closure's code |

## 2. Thunk-Specific Representation

Thunks use a **wider header** than other closures:

```c
// Standard closure header (constructors, functions, etc.)
typedef struct {
    const StgInfoTable* info;
} StgHeader;

// Thunk header: standard + SMP padding word
typedef struct {
    const StgInfoTable* info;
    StgSMPThunkHeader smp;   // extra padding word
} StgThunkHeader;

typedef struct StgThunk_ {
    StgThunkHeader header;
    struct StgClosure_ *payload[];  // free variables
} StgThunk;
```

**Why the extra word?** When a thunk is updated (overwritten with an indirection
to its result), the runtime writes the `indirectee` pointer into this padding
slot rather than over the free-variable payload. This makes concurrent updates
lock-free — a reader examining the payload never sees a half-written indirectee.

### Specialised thunk types

GHC encodes the payload layout directly in the closure type for small thunks,
so the GC can skip reading the info table's layout field:

| Type | Payload |
|------|---------|
| `THUNK` | Generic, arbitrary payload |
| `THUNK_1_0` | 1 pointer, 0 non-pointers |
| `THUNK_0_1` | 0 pointers, 1 non-pointer |
| `THUNK_2_0` | 2 pointers, 0 non-pointers |
| `THUNK_1_1` | 1 pointer, 1 non-pointer |
| `THUNK_0_2` | 0 pointers, 2 non-pointers |
| `THUNK_STATIC` | Statically allocated (a CAF) |
| `THUNK_SELECTOR` | Selects one field from a constructor |

### Selector thunks

A selector thunk represents `case x of { K _ _ field _ -> field }`. The GC
evaluates these *during collection* if the selectee is already evaluated,
preventing space leaks where an entire constructor is kept alive for one field.

```c
typedef struct {
    StgThunkHeader header;
    StgClosure *selectee;
} StgSelector;
```

### AP and AP_STACK

Two additional thunk-like closure types:

- **AP** — a generic unevaluated function application (`fun arg1 arg2 ...`),
  with arity 0. Arises when the code generator cannot produce a more specific form.
- **AP_STACK** — a thunk whose "arguments" are a saved stack chunk. Created by
  the exception system.

## 3. Evaluation Lifecycle

### Entering a thunk

1. Load the info pointer from the closure header.
2. Jump to the entry code (at or after the info pointer, depending on
   `TABLES_NEXT_TO_CODE`).
3. The entry code pushes an **update frame** on the stack.
4. The thunk's body executes, producing a value.
5. The update frame fires, overwriting the thunk with an indirection to the
   result.

### Dynamic pointer tagging

The low bits of a pointer (2 bits on 32-bit, 3 on 64-bit) encode whether the
target is already evaluated:

- **Tag 0**: unevaluated or unknown — must enter.
- **Tag 1–N**: constructor tag + 1 (already in WHNF).

This eliminates the indirect jump in the common case (~14% speedup, ~2% code
size increase).

### Update frames

An update frame records "update this thunk when the current computation
finishes":

```c
typedef struct _StgUpdateFrame {
    StgHeader header;       // info = stg_upd_frame_info
    StgClosure *updatee;   // pointer to the thunk being evaluated
} StgUpdateFrame;
```

When the body returns a value, the update frame's entry code calls
`updateWithIndirection(updatee, result)`.

## 4. Blackholing

Marking a thunk as "currently being evaluated" serves three purposes:

1. **Loop detection** — re-entering a thunk you're already evaluating would
   loop forever.
2. **Parallel deduplication** — other threads block on the blackhole instead of
   duplicating work.
3. **Space leak prevention** — once blackholed, the thunk's free variables
   become unreachable through it.

### Lazy blackholing (default)

The thunk is *not* modified on entry. If the thread yields, `threadPaused()`
walks the stack and retroactively blackholes all pending update frames. This
avoids a write in the common case (most thunks complete before yielding).

### Eager blackholing (`-feager-blackholing`)

The thunk's info pointer is set to `EAGER_BLACKHOLE_info` immediately on entry.
The `indirectee` (in the SMP padding word) is set to the current thread's TSO.
Important for parallel programs.

## 5. Indirections and the BLACKHOLE Trick

After evaluation, a thunk becomes an indirection — a closure that just points
to the result. GHC uses a clever trick: **`BLACKHOLE` serves as both "being
evaluated" and "evaluated (indirection)".**

The `indirectee` field distinguishes the two states:

- Points to a **TSO** or **BLOCKING_QUEUE** → still being evaluated.
- Points to a **normal value** → evaluation complete, acts as indirection.

This makes the update a single atomic store sequence:

```c
// Write result pointer FIRST (release semantics)
RELEASE_STORE(&((StgInd *)p1)->indirectee, p2);
// Then set info to BLACKHOLE (release semantics)
SET_INFO_RELEASE(p1, &stg_BLACKHOLE_info);
```

The ordering guarantees: any thread that sees `BLACKHOLE` and reads `indirectee`
will see the correct value. No race window.

True `IND` / `IND_STATIC` types are reserved for special cases (selector thunk
evaluation during GC, static indirections for CAFs).

### GC short-circuiting

Indirections are **not** eliminated at runtime. The **garbage collector**
short-circuits them during copying: when it encounters a BLACKHOLE/IND, it
follows the `indirectee` and updates all references to point directly to the
result. The indirection becomes garbage.

## 6. CAFs (Constant Applicative Forms)

Top-level thunks with no free variables live in static memory and get special
treatment:

1. On first entry, info pointer changes to `stg_IND_STATIC_info`.
2. `indirectee` points to the heap-allocated result.
3. `saved_info` preserves the original info table (for GHCi reloading).
4. `static_link` threads the CAF onto a linked list for GC reachability.

## 7. Summary: Thunk Lifecycle

```
  THUNK (unevaluated)
       |
       | thread enters
       |
       +-- [lazy blackhole] -----> remains THUNK until thread yields
       |                           threadPaused() converts to BLACKHOLE
       |
       +-- [eager blackhole] ----> immediately becomes EAGER_BLACKHOLE
                                   indirectee -> TSO
       |
       | evaluation completes, update frame fires
       v
  BLACKHOLE (indirectee -> result value)
       |
       | next GC cycle
       v
  (short-circuited: all references point directly to result)
```

## 8. Relevance to Rusholme

### What Rusholme can learn

- **The SMP padding word** makes updates lock-free. Even for single-threaded
  Rusholme, this design eliminates a class of bugs at the representation level.
  Worth adopting if we ever want concurrency.
- **Selector thunk evaluation in the GC** is essential, not optional. Without
  it, lazy programs suffer severe space leaks.
- **Dynamic pointer tagging** is a huge win (14%) with minimal complexity.
  Zig's pointer alignment guarantees make the low bits available.
- **The `_p_n` variants** are a GC optimization. Whether Rusholme needs them
  depends on how our GC traverses closures.

### What differs for Rusholme

- **GRIN makes thunks explicit.** GHC hides evaluation behind info-table
  indirection; GRIN's `store`/`fetch`/`update` model thunk lifecycle directly
  in the IR. The runtime representation can be simpler because GRIN has already
  resolved evaluation order.
- **Direct style with thunks** (Decision 003) means we use standard C calling
  conventions, not GHC's custom register convention. Thunks are just function
  pointers with payloads, evaluated by calling the function pointer.
- **No STG.** GHC's thunk types are intimately tied to the STG machine (update
  frames, entry code conventions). Rusholme's GRIN-based pipeline should derive
  its thunk representation from GRIN's semantics, not from STG conventions.

### Open questions for Rusholme

1. **What is the concrete heap layout for a Rusholme thunk?** Decision 003
   sketched `fn_ptr + payload`. Does it need a type tag? A header word for GC?
2. **How does the GC interact with thunks?** If we adopt Immix (Phase 2), the
   GC needs to distinguish pointers from non-pointers in the payload. Do we
   use GHC-style layout bitmaps, or something simpler?
3. **Do we need blackholing?** For single-threaded execution, blackholing for
   loop detection is still valuable. Space-leak prevention matters too.
4. **Do we need selector thunks?** If GRIN optimizations eliminate most selector
   expressions before codegen, the GC optimization may be unnecessary.
5. **Should we adopt pointer tagging?** Zig gives us aligned pointers with
   spare low bits. The 14% win is hard to ignore, but it adds complexity.

## References

- GHC Commentary: Heap Objects —
  https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
- GHC Source: `rts/include/rts/storage/Closures.h` —
  https://github.com/ghc/ghc/blob/master/rts/include/rts/storage/Closures.h
- GHC Source: `rts/include/rts/storage/InfoTables.h` —
  https://github.com/ghc/ghc/blob/master/rts/include/rts/storage/InfoTables.h
- GHC Source: `rts/include/rts/storage/ClosureTypes.h` —
  https://github.com/ghc/ghc/blob/master/rts/include/rts/storage/ClosureTypes.h
- GHC Source: `rts/Updates.cmm` —
  https://github.com/ghc/ghc/blob/master/rts/Updates.cmm
- Marlow & Peyton Jones, "Making a Fast Curry: Push/Enter vs. Eval/Apply",
  JFP 2006 —
  https://www.cs.tufts.edu/~nr/cs257/archive/simon-peyton-jones/eval-apply-jfp.pdf
- Marlow et al., "Faster Laziness Using Dynamic Pointer Tagging", ICFP 2007 —
  https://simonmar.github.io/bib/papers/ptr-tagging.pdf
- GHC (STG, Cmm, asm) Illustrated (Takenobu T.) —
  https://takenobu-hs.github.io/downloads/haskell_ghc_illustrated.pdf
- Yang, "The GHC Runtime System" (draft) —
  http://ezyang.com/jfp-ghc-rts-draft.pdf
- Hruska et al., "A Modern Look at GRIN", Acta Cybernetica 2020 —
  see docs/references/grin-overview.md
- Rusholme Decision 003: Calling Convention —
  see docs/decisions/003-calling-convention.md

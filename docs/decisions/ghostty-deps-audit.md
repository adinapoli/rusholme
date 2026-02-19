# Ghostty Dependency Audit — Relevance for Rusholme

**Date:** 2026-02-19
**Source:** [`ghostty-org/ghostty` — `build.zig.zon`](https://github.com/ghostty-org/ghostty/blob/main/build.zig.zon)
**Purpose:** Audit Ghostty's Zig/C dependencies to identify libraries that could benefit Rusholme.

---

## TL;DR

| Library | Relevant? | Why |
|---------|-----------|-----|
| **libxev** | Unlikely | Event loop — compiler I/O is synchronous |
| **uucode** | **Yes — strong candidate** | Fast Unicode library; Haskell identifiers and strings need Unicode |
| **oniguruma** | **Yes — possible** | Battle-tested regex engine; useful for lexer helpers or error display |
| **simdutf** | **Yes — worth watching** | SIMD UTF-8 validation; could accelerate source decoding |
| **zf** | No | File fuzzy-finder CLI tool |
| **z2d** | No | 2D vector graphics renderer |
| **vaxis** | No | TUI framework (Go, terminal UI) |
| **harfbuzz** | No | Text shaping for rendered fonts |
| **freetype** | No | Font rendering |
| **fontconfig** | No | Font discovery |
| **highway** | No | SIMD abstraction — very low-level, no clear compiler use |
| **wuffs** | No | Image/media decoding |
| **libpng** | No | PNG image I/O |
| **opengl / glslang / spirv_cross** | No | GPU rendering pipeline |
| **gtk4_layer_shell / wayland / gobject** | No | GUI/display layer |
| **zig_objc / zig_js / zig_wayland** | No | Platform-specific bindings |
| **sentry** | No | Crash reporting SaaS |
| **utfcpp** | No | C++ UTF-8 iterator (C++ only) |
| **zlib** | No | Compression — no current need |
| **JetBrains Mono / Nerd Fonts** | No | Font assets |
| **iterm2_themes** | No | Color theme data |
| **apple_sdk / macos** | No | macOS platform package |
| **dcimgui** | No | Dear ImGui bindings |
| **libintl** | No | i18n translation |

---

## Detailed Analysis

### libxev — Cross-Platform Event Loop
- **Repo:** [mitchellh/libxev](https://github.com/mitchellh/libxev)
- **What it does:** A proactor-style async event loop built in Zig. Provides non-blocking I/O (TCP, UDP, files), timers, signals, and process management. Uses `io_uring` on Linux. Zero runtime allocations. Cross-platform (Linux, macOS, WASI).
- **Relevance to Rusholme:** **Low.** Rusholme's compilation pipeline is inherently synchronous and single-threaded: lex → parse → Core → GRIN → codegen. There is no inherent need for an async event loop. The one speculative use case would be a language server (LSP) sitting in front of Rusholme, which needs async I/O for stdin/stdout or sockets — but that is far out of current scope (no LSP issue exists on the roadmap). If Rusholme ever grows an LSP or a build-system daemon that watches files, libxev would be an excellent choice. **File for future reference, do not adopt now.**
- **Verdict:** Skip for now; revisit if an LSP or file-watching daemon becomes a roadmap item.

---

### uucode — Fast Unicode Library in Zig
- **Repo:** [jacobsandlund/uucode](https://github.com/jacobsandlund/uucode)
- **What it does:** A fast, flexible Unicode library written in Zig, configurable at build time. Built on top of Ghostty's Unicode performance work. Three-layer architecture: (1) parses the Unicode Character Database (UCD), (2) generates Zig table data, (3) exposes APIs for general categories, case mappings, grapheme clustering, and UTF-8 iteration. MIT licensed.
- **Relevance to Rusholme:** **High.** Haskell source files use Unicode identifiers, Unicode operator symbols, and Unicode string literals. The Rusholme lexer needs to:
  - Classify characters (letter, digit, symbol, whitespace) per Haskell 2010 §2.2
  - Iterate over Unicode code points (not bytes) when scanning identifiers
  - Handle Unicode escape sequences (`\xNN`, `\uNNNN`, etc.) in string/char literals

  Currently the lexer likely handles ASCII well but may have gaps on non-ASCII identifiers. `uucode` provides exactly the character category tables needed, is already used in production in Ghostty, is pure Zig (no C FFI overhead), and is allocation-free.
- **Verdict:** **Strong candidate.** Evaluate against the existing lexer Unicode handling. If there are gaps, adopt uucode. Even if the current code handles the basics, using a proper Unicode library is the principled choice (mantra: "parse everything GHC parses" includes Unicode identifiers).

---

### oniguruma — Regular Expression Engine (C)
- **Repo:** [kkos/oniguruma](https://github.com/kkos/oniguruma)
- **What it does:** A battle-tested, multi-encoding regular expression library written in C. Supports Unicode, multiple regex syntaxes (POSIX, Python, Ruby, etc.), and is used in Ruby's standard library and many other production systems.
- **Relevance to Rusholme:** **Moderate.** Rusholme implements its own hand-written lexer, so oniguruma is not needed for tokenization. However, it could be useful for:
  - **Diagnostic message formatting** — regex-based string matchers in tests (though Zig has `std.mem.startsWith` etc.)
  - **Future pattern matching in the compiler** — very speculative
  - **Test infrastructure** — pattern matching on compiler output in integration tests

  The project's mantra "leverage battle-tested C libraries" applies here, but only if there's an actual need. The hand-written lexer is the right approach for a compiler; oniguruma would be overkill. Zig's `std.mem` and string functions are sufficient for most compiler internal needs.
- **Verdict:** Skip unless a concrete use case emerges. The hand-written lexer is correct; don't introduce a C dependency without a compelling reason.

---

### simdutf — SIMD UTF-8 Validation and Transcoding
- **Repo:** [simdutf/simdutf](https://github.com/simdutf/simdutf)
- **What it does:** A C++ library using SIMD instructions to validate and transcode UTF-8, UTF-16, and UTF-32 at very high throughput. Used in Node.js and other high-performance runtimes.
- **Relevance to Rusholme:** **Low–Moderate.** Source file decoding (reading `.hs` files and validating UTF-8) is a one-time cost per compilation. For the current scale of Rusholme (small Haskell programs), SIMD acceleration is premature optimisation. The project mantra says "correctness first, performance later." However, if Rusholme ever processes large codebases or becomes a batch compiler, fast UTF-8 validation at file load time would be valuable. It's also a C++ library (not C), which complicates Zig's C interop somewhat.
- **Verdict:** Skip for now. Revisit if profiling shows UTF-8 decoding as a bottleneck.

---

### zf — Fuzzy Finder / Filter Library
- **Repo:** [natecraddock/zf](https://github.com/natecraddock/zf)
- **What it does:** A CLI fuzzy finder and allocation-free Zig library for fuzzy filtering of file paths. Optimized for path-aware ranking (filename > directory components).
- **Relevance to Rusholme:** **None.** Rusholme has no interactive fuzzy-search UI. The library is compelling for tooling (an interactive module browser, IDE plugin, etc.) but nothing of that kind is on the roadmap.
- **Verdict:** Skip.

---

### z2d — 2D Vector Graphics Renderer
- **Repo:** [vancluever/z2d](https://github.com/vancluever/z2d)
- **What it does:** A pure-Zig 2D graphics library for rasterizing vector primitives (lines, Bezier curves, arcs). Supports stroke/fill, gradients, PNG export, 28 composition operators. Inspired by Cairo.
- **Relevance to Rusholme:** **None.** Rusholme generates text output; it has no rendering pipeline.
- **Verdict:** Skip.

---

### vaxis — TUI Framework
- **Repo:** [rockorager/vaxis](https://github.com/rockorager/vaxis) (note: the Ghostty dependency is the Zig port)
- **What it does:** A modern terminal UI library. Handles styled terminal output, input parsing, graphics (Sixel), and widgets. Does not use terminfo; detects capabilities via queries.
- **Relevance to Rusholme:** **None** in the core compiler. A compiler REPL or interactive debugger could use it, but neither is on the roadmap.
- **Verdict:** Skip.

---

### harfbuzz, freetype, fontconfig — Text Rendering Stack
- **What they do:** Together these form the standard text rendering pipeline: freetype rasterizes glyph outlines, harfbuzz does complex text shaping (ligatures, bidirectional text, OpenType features), fontconfig discovers system fonts.
- **Relevance to Rusholme:** **None.** Rusholme outputs text to a terminal or file; it does not render glyphs.
- **Verdict:** Skip all three.

---

### highway — SIMD Abstraction Library
- **Repo:** [google/highway](https://github.com/google/highway)
- **What it does:** A C++ library providing portable SIMD operations across x86, ARM, RISC-V. Used by Ghostty for rendering performance.
- **Relevance to Rusholme:** **None.** No vectorisable hot loop has been identified in the compiler pipeline at this stage.
- **Verdict:** Skip.

---

### wuffs — Image and Media Decoding
- **Repo:** [google/wuffs](https://github.com/google/wuffs)
- **What it does:** A memory-safe language and library for parsing binary file formats (GIF, PNG, JSON, etc.) with provable safety bounds.
- **Relevance to Rusholme:** **None.** Rusholme processes Haskell text source; no binary media decoding needed.
- **Verdict:** Skip.

---

### Platform-Specific / GUI / Rendering Deps
The following are entirely Ghostty-specific and have no applicability to a compiler:
- `opengl`, `glslang`, `spirv_cross` — GPU shader compilation/rendering
- `gtk4_layer_shell`, `wayland`, `wayland_protocols`, `plasma_wayland_protocols` — Wayland display protocol
- `gobject` — GObject/GLib bindings for GTK
- `zig_objc` — Objective-C interop for macOS
- `zig_js` — JavaScript/WASM interop
- `zig_wayland` — Wayland Zig bindings
- `apple_sdk`, `macos` — macOS SDK packaging
- `dcimgui` — Dear ImGui bindings (debug UI)
- `sentry` — Crash reporting
- `libintl` — GNU gettext i18n
- `utfcpp` — C++ only, no Zig interop
- `zlib` — compression (no current need)
- `JetBrains Mono`, `Nerd Fonts Symbols Only` — font assets
- `iterm2_themes` — terminal color themes

---

## Summary and Recommendations

### Adopt / Evaluate
1. **`uucode`** — Evaluate against the current lexer's Unicode handling. Haskell 2010 §2.2 defines identifiers using Unicode character classes. Using a proper, production-tested library here is the principled choice. If the lexer has any gaps (non-ASCII identifiers, Unicode operators), `uucode` closes them cleanly.

### File for Future Reference (Do Not Adopt Now)
2. **`libxev`** — Excellent library, not yet the right stage. Two concrete future use cases exist:
   - **Parallel module compilation:** A Haskell dependency graph has many independent modules (no inter-dependencies). A build driver could submit each module's compilation as a unit of work and process completions as they arrive — exactly the proactor model libxev provides. This would be a meaningful speedup for multi-module projects.
   - **LSP server / file-watching daemon:** A `rusholme --lsp` process needs async stdin/stdout I/O and could watch source files for changes, re-checking incrementally. libxev is a natural fit here.

   Neither use case applies to the current single-file interpreter/compiler. Add a note when the build system or LSP epics are created.

### Skip
Everything else is either GUI/rendering infrastructure, platform-specific to a terminal emulator, or performance optimization for problems Rusholme does not yet have.

---

## A Note on libxev for the Curious

`libxev` implements the **proactor pattern**: you submit work (read this file, wait for a connection) and receive a completion callback — rather than the **reactor pattern** (tell me when this fd is ready, then I'll do the work). This mirrors `io_uring` on Linux. It is:
- Cross-platform: `io_uring` (Linux), `kqueue` (macOS), `IOCP` (Windows, future), WASI
- Zero-allocation at runtime
- Pure Zig, no C dependency

For a single-file compiler, the key insight is: **compilation is CPU-bound and sequential within a single module**. The bottleneck is parsing and typechecking, not waiting on file descriptors.

However, a multi-module Haskell project has a **dependency graph** between modules. Independent subgraphs can be compiled in parallel — and this is where libxev becomes interesting. Rather than forking processes or blocking on each module serially, a build driver could submit each independent compilation as a work item and process completions as they arrive (proactor style). This is essentially what `make -j` achieves with processes, but with finer-grained async dispatch.

A second use case: a `rusholme --lsp` language server process needs async I/O (stdin/stdout or a socket) and file-watching for incremental recheck. libxev handles both naturally.

Neither use case applies yet — Rusholme currently processes single files. When the build system or LSP epics are scoped, libxev should be the first library evaluated.

//! REPL JIT Execution Engine
//!
//! Wraps LLVM ORC LLJIT to provide native JIT compilation and execution
//! for the REPL. Takes a compiled GRIN `Program`, translates it to LLVM
//! IR via `GrinTranslator`, feeds the module to LLJIT, and calls the
//! entry-point function directly.
//!
//! RTS functions (rts_alloc, rts_store_field, etc.) are registered as
//! absolute symbols so that JIT'd code can resolve them at link time.
//!
//! This is the native execution backend. The WASM backend uses the GRIN
//! tree-walking evaluator instead (see engine.zig).
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");
const Allocator = std.mem.Allocator;

const llvm = @import("../backend/llvm.zig");
const c = llvm.c;
const grin_to_llvm = @import("../backend/grin_to_llvm.zig");
const GrinTranslator = grin_to_llvm.GrinTranslator;
const grin_ast = @import("../grin/ast.zig");
const rts_node = @import("../rts/node.zig");

// ── Result types ──────────────────────────────────────────────────────

/// Result of executing a GRIN program via JIT.
pub const ExecResult = struct {
    /// Human-readable string representation of the result value.
    value: []const u8,
};

/// Errors that can occur during JIT execution.
pub const JitError = error{
    /// LLJIT creation failed.
    JitCreationFailed,
    /// LLVM module could not be added to the JIT.
    ModuleAddFailed,
    /// The entry-point symbol was not found.
    EntryPointNotFound,
    /// GRIN-to-LLVM translation failed.
    TranslationFailed,
    /// Thread-safe context creation failed.
    ContextCreationFailed,
    /// Result formatting failed.
    FormatError,
    /// Out of memory.
    OutOfMemory,
    /// RTS symbol registration failed.
    RtsRegistrationFailed,
    /// Value is not a valid heap node (raw pointer to non-heap memory).
    InvalidNode,
};

// ── JIT Engine ────────────────────────────────────────────────────────

/// Execution engine backed by LLVM ORC LLJIT.
///
/// Manages JIT compilation and execution for the REPL. Declarations are
/// added permanently to the main JITDylib; expressions use unique entry
/// point names and resource trackers for per-evaluation cleanup.
const KnownTags = grin_to_llvm.KnownTags;

pub const JitEngine = struct {
    allocator: Allocator,
    jit: llvm.OrcLLJITRef,
    /// Monotonically increasing counter for generating unique entry
    /// point names ("repl_expr_0", "repl_expr_1", ...).
    eval_counter: u64 = 0,
    /// Buffer for formatting the entry point name as a null-terminated
    /// C string for LLVM symbol lookup.
    entry_name_buf: [64]u8 = undefined,
    /// GRIN defs from prior `addDeclarations` calls. Accumulated so
    /// that expression compilation can scan them for F-tag registration,
    /// enabling `forceValueToWhnf` to handle thunks from any session.
    accumulated_grin_defs: std.ArrayListUnmanaged(grin_ast.Def) = .{},
    /// Constructor discriminants from Prelude compilation for result formatting.
    known_tags: KnownTags = .{},
    /// Resource tracker for the shared `__rhc_force` module.
    /// Allows replacing it when new F-tags appear in expressions.
    force_tracker: ?llvm.OrcResourceTrackerRef = null,
    /// Set of F-tag unique IDs covered by the current force module.
    /// Tracked as a set (not a count) because two expressions can
    /// introduce different F-tags yet have the same total count —
    /// e.g. `[1..10]` wraps `enumFromTo` while `[1..]` wraps `enumFrom`,
    /// both adding exactly one new tag to the same Prelude baseline.
    force_ftag_uniques: std.AutoHashMapUnmanaged(u64, void) = .{},
    /// Cached pointer to the JIT'd `__rhc_force` function.
    /// Used by the formatter to force thunks when walking heap structures.
    /// Signature: fn(ptr) callconv(.c) *anyopaque — forces a value to WHNF.
    force_fn: ?*const fn (*anyopaque) callconv(.c) *anyopaque = null,

    /// Create a new JIT engine backed by LLVM ORC LLJIT.
    pub fn init(allocator: Allocator) JitError!JitEngine {
        llvm.initialize();

        var jit: llvm.OrcLLJITRef = null;
        const err = c.LLVMOrcCreateLLJIT(&jit, null);
        if (err != null) {
            c.LLVMConsumeError(err);
            return JitError.JitCreationFailed;
        }

        var engine = JitEngine{
            .allocator = allocator,
            .jit = jit,
        };

        try engine.registerRtsSymbols();

        return engine;
    }

    /// Destroy the JIT engine and release all JIT'd code.
    pub fn deinit(self: *JitEngine) void {
        if (self.force_tracker) |tracker| {
            c.LLVMOrcReleaseResourceTracker(tracker);
        }
        self.force_ftag_uniques.deinit(self.allocator);
        self.accumulated_grin_defs.deinit(self.allocator);
        if (self.jit) |jit| {
            const err = c.LLVMOrcDisposeLLJIT(jit);
            if (err != null) c.LLVMConsumeError(err);
        }
    }

    /// Emit and add a shared `__rhc_force` module to the JIT.
    ///
    /// If a previous force module exists (tracked by `force_tracker`),
    /// it is removed first.  The new module contains `__rhc_force` with
    /// external linkage and covers all F-tags currently in `translator`'s
    /// tag table.
    fn emitSharedForceModule(self: *JitEngine, translator: *GrinTranslator) JitError!void {
        // Remove previous force module if it exists.
        if (self.force_tracker) |old_tracker| {
            const rm_err = c.LLVMOrcResourceTrackerRemove(old_tracker);
            if (rm_err != null) c.LLVMConsumeError(rm_err);
            c.LLVMOrcReleaseResourceTracker(old_tracker);
            self.force_tracker = null;
        }

        const ir_text = translator.emitForceModuleIr() catch
            return JitError.TranslationFailed;
        defer self.allocator.free(ir_text);

        const ts_mod = self.parseIrToThreadSafeModule(ir_text) catch
            return JitError.TranslationFailed;

        const main_dylib = c.LLVMOrcLLJITGetMainJITDylib(self.jit);
        const tracker = c.LLVMOrcJITDylibCreateResourceTracker(main_dylib);

        const add_err = c.LLVMOrcLLJITAddLLVMIRModuleWithRT(self.jit, tracker, ts_mod);
        if (add_err != null) {
            c.LLVMConsumeError(add_err);
            c.LLVMOrcReleaseResourceTracker(tracker);
            return JitError.ModuleAddFailed;
        }

        self.force_tracker = tracker;

        // Rebuild the set of covered F-tag uniques so that execute() can
        // detect missing tags by set membership rather than count comparison.
        self.force_ftag_uniques.clearRetainingCapacity();
        var ftag_iter = translator.tag_table.fun_tags.iterator();
        while (ftag_iter.next()) |entry| {
            try self.force_ftag_uniques.put(self.allocator, entry.key_ptr.*, {});
        }

        // The cached force_fn pointer is now stale; clear it so that
        // execute() re-resolves it after the new module is materialised.
        self.force_fn = null;
    }

    /// Add declaration definitions permanently to the JIT's main dylib.
    ///
    /// These symbols persist across REPL inputs so that subsequent
    /// expressions can reference user-defined functions and data types.
    pub fn addDeclarations(self: *JitEngine, program: *const grin_ast.Program) JitError!void {
        if (program.defs.len == 0) return;

        // Accumulate defs for tag scanning in future expression compilations.
        for (program.defs) |def| {
            self.accumulated_grin_defs.append(self.allocator, def) catch
                return JitError.OutOfMemory;
        }

        // Use a single translator with a global tag table so that
        // discriminant assignments are consistent across all defs.
        // Then translate each def individually into its own LLVM module.
        //
        // Compiling all defs into a single large module triggers an ORC
        // JIT "Duplicate definition" error: the inline eval loop in each
        // translated function forward-declares thunk functions from other
        // defs, and ORC's materializer treats the combination of forward
        // declaration + definition as a duplicate symbol within the same
        // materialization unit. Per-def modules avoid this by keeping
        // each module small — intra-program function references become
        // cross-module external declarations that ORC resolves at link time.
        var translator = GrinTranslator.init(self.allocator);
        defer translator.deinit();
        translator.repl_entry_point = "__decl__";
        // Seed with accumulated defs from prior sessions (e.g. Prelude)
        // so that discriminant assignments are consistent with future
        // expression compilations that also scan these defs.
        translator.extra_tag_defs = self.accumulated_grin_defs.items;

        // Build a global tag table from all defs.
        translator.prepareGlobalTagTable(program.*) catch
            return JitError.TranslationFailed;

        // Capture constructor discriminants for result formatting.
        self.known_tags = translator.getKnownTagDiscriminants();

        // Emit a shared __rhc_force module BEFORE per-def modules.
        // Per-def modules declare __rhc_force as external and ORC JIT
        // resolves calls to this shared version (lazy symbol lookup).
        try self.emitSharedForceModule(&translator);

        for (program.defs) |def| {
            const single_defs = self.allocator.alloc(grin_ast.Def, 1) catch
                return JitError.OutOfMemory;
            defer self.allocator.free(single_defs);
            single_defs[0] = def;

            const single_prog = grin_ast.Program{
                .defs = single_defs,
                .field_types = program.field_types,
                .arities = program.arities,
            };

            const mod = translator.translateModuleGrin("decl", single_prog) catch
                return JitError.TranslationFailed;

            const ir_text = llvm.printModuleToString(mod, self.allocator) catch
                return JitError.OutOfMemory;
            defer self.allocator.free(ir_text);

            const ts_mod = self.parseIrToThreadSafeModule(ir_text) catch
                return JitError.TranslationFailed;

            const main_dylib = c.LLVMOrcLLJITGetMainJITDylib(self.jit);
            const add_err = c.LLVMOrcLLJITAddLLVMIRModule(self.jit, main_dylib, ts_mod);
            if (add_err != null) {
                c.LLVMConsumeError(add_err);
                return JitError.ModuleAddFailed;
            }
        }
    }

    /// Translate a GRIN expression program to LLVM IR, JIT-compile it,
    /// execute the entry point, and return the formatted result.
    ///
    /// Each call uses a unique entry point name and a resource tracker
    /// so the expression's symbols are removed after execution. This
    /// allows multiple expressions to be evaluated without symbol
    /// collisions.
    pub fn execute(self: *JitEngine, program: *const grin_ast.Program) JitError!ExecResult {
        // 1. Generate a unique entry point name for this evaluation.
        const entry_name = std.fmt.bufPrint(&self.entry_name_buf, "repl_expr_{d}", .{self.eval_counter}) catch {
            return JitError.OutOfMemory;
        };
        self.entry_name_buf[entry_name.len] = 0;
        const entry_name_z: [:0]const u8 = self.entry_name_buf[0..entry_name.len :0];
        self.eval_counter += 1;

        // 2. Patch the GRIN program: rename replExpr__ to the unique name.
        const patched_program = patchEntryPointName(self.allocator, program, entry_name) catch {
            return JitError.OutOfMemory;
        };

        // 3. Translate GRIN → LLVM IR text.
        //    We use a temporary GrinTranslator to produce IR text, then
        //    parse it into a fresh module owned by a ThreadSafeContext.
        //    This avoids a double-free: GrinTranslator.deinit() destroys
        //    its own LLVM context, but LLJIT also takes ownership of the
        //    module. Going through IR text decouples the two ownership
        //    domains.
        var translator = GrinTranslator.init(self.allocator);
        defer translator.deinit();
        translator.repl_entry_point = entry_name;
        // Seed with accumulated defs from prior declaration sessions so
        // that the tag table includes F-tags for all known functions.
        translator.extra_tag_defs = self.accumulated_grin_defs.items;

        const ir_text = translator.translateProgram(patched_program) catch {
            return JitError.TranslationFailed;
        };
        defer self.allocator.free(ir_text);

        // Update known_tags from the expression's translator, which has
        // the complete tag table (seeded from all accumulated defs).
        // This ensures formatJitResult uses correct discriminants.
        self.known_tags = translator.getKnownTagDiscriminants();

        // Re-emit __rhc_force if the expression introduces any F-tag not
        // covered by the current force module. We compare sets, not counts:
        // two different expressions can introduce different F-tags while
        // keeping the total count equal (e.g. `[1..10]` wraps enumFromTo
        // and `[1..]` wraps enumFrom — same count, different set members).
        var needs_force_reemit = false;
        var ftag_check_iter = translator.tag_table.fun_tags.iterator();
        while (ftag_check_iter.next()) |entry| {
            if (!self.force_ftag_uniques.contains(entry.key_ptr.*)) {
                needs_force_reemit = true;
                break;
            }
        }
        if (needs_force_reemit) {
            try self.emitSharedForceModule(&translator);
        }

        // 4. Parse IR and add to JIT with a resource tracker.
        const ts_mod = try self.parseIrToThreadSafeModule(ir_text);

        const main_dylib = c.LLVMOrcLLJITGetMainJITDylib(self.jit);
        const tracker = c.LLVMOrcJITDylibCreateResourceTracker(main_dylib);

        const add_err = c.LLVMOrcLLJITAddLLVMIRModuleWithRT(self.jit, tracker, ts_mod);
        if (add_err != null) {
            c.LLVMConsumeError(add_err);
            c.LLVMOrcReleaseResourceTracker(tracker);
            return JitError.ModuleAddFailed;
        }

        // 5. Look up the unique entry point.
        var addr: llvm.OrcExecutorAddress = 0;
        const lookup_err = c.LLVMOrcLLJITLookup(self.jit, &addr, entry_name_z);
        if (lookup_err != null) {
            c.LLVMConsumeError(lookup_err);
            // Clean up before returning.
            const rm_err = c.LLVMOrcResourceTrackerRemove(tracker);
            if (rm_err != null) c.LLVMConsumeError(rm_err);
            c.LLVMOrcReleaseResourceTracker(tracker);
            return JitError.EntryPointNotFound;
        }

        // 6. Call the entry point. REPL entry points return i64 (either
        //    a literal value or a pointer to a heap node cast to i64).
        const EntryFn = *const fn () callconv(.c) i64;
        const entry_fn: EntryFn = @ptrFromInt(addr);
        const raw_result = entry_fn();

        // 6b. Lazily resolve __rhc_force for thunk-forcing during display.
        //     Done here (after the entry point runs) so all dependencies are
        //     materialized. The lookup is cached for future calls.
        if (self.force_fn == null) {
            var force_addr: llvm.OrcExecutorAddress = 0;
            const flookup_err = c.LLVMOrcLLJITLookup(self.jit, &force_addr, "__rhc_force");
            if (flookup_err != null) {
                c.LLVMConsumeError(flookup_err);
            } else if (force_addr != 0) {
                self.force_fn = @ptrFromInt(force_addr);
            }
        }

        // 7. Format the result before cleaning up.
        const formatted = formatJitResult(self.allocator, raw_result, self.known_tags, self.force_fn) catch {
            const rm_err = c.LLVMOrcResourceTrackerRemove(tracker);
            if (rm_err != null) c.LLVMConsumeError(rm_err);
            c.LLVMOrcReleaseResourceTracker(tracker);
            return JitError.FormatError;
        };

        // 8. Remove the expression's symbols from the dylib. The result
        //    has already been captured as a formatted string, so the
        //    JIT'd code is no longer needed.
        const rm_err = c.LLVMOrcResourceTrackerRemove(tracker);
        if (rm_err != null) c.LLVMConsumeError(rm_err);
        c.LLVMOrcReleaseResourceTracker(tracker);

        return .{ .value = formatted };
    }

    /// Parse LLVM IR text into a ThreadSafeModule ready for LLJIT.
    ///
    /// Sets the data layout and target triple to match the JIT engine.
    /// The returned ThreadSafeModule takes ownership of the underlying
    /// LLVM module and context.
    fn parseIrToThreadSafeModule(self: *JitEngine, ir_text: []const u8) JitError!llvm.OrcThreadSafeModuleRef {
        const ts_ctx = c.LLVMOrcCreateNewThreadSafeContext();
        if (ts_ctx == null) return JitError.ContextCreationFailed;

        const ctx = c.LLVMOrcThreadSafeContextGetContext(ts_ctx);
        var err_msg: [*c]u8 = null;
        const buf = c.LLVMCreateMemoryBufferWithMemoryRangeCopy(
            ir_text.ptr,
            ir_text.len,
            "repl_module",
        );

        var llvm_module: llvm.Module = null;
        if (c.LLVMParseIRInContext(ctx, buf, &llvm_module, &err_msg) != 0) {
            if (err_msg) |msg| c.LLVMDisposeMessage(msg);
            c.LLVMOrcDisposeThreadSafeContext(ts_ctx);
            return JitError.TranslationFailed;
        }

        const data_layout_str = c.LLVMOrcLLJITGetDataLayoutStr(self.jit);
        c.LLVMSetDataLayout(llvm_module, data_layout_str);
        const triple = c.LLVMGetDefaultTargetTriple();
        defer c.LLVMDisposeMessage(triple);
        c.LLVMSetTarget(llvm_module, triple);

        const ts_mod = c.LLVMOrcCreateNewThreadSafeModule(llvm_module, ts_ctx);
        // NOTE: Do NOT dispose the ThreadSafeContext here. The ThreadSafeModule
        // takes ownership and will clean it up when the JIT disposes the module.
        // Disposing it here causes a use-after-free when the JIT tries to compile.
        return ts_mod;
    }

    /// Register the RTS functions as absolute symbols in the JIT's main
    /// dylib so that JIT'd code can resolve calls to rts_alloc, etc.
    fn registerRtsSymbols(self: *JitEngine) JitError!void {
        const Symbol = struct {
            name: [:0]const u8,
            addr: usize,
        };

        const symbols = [_]Symbol{
            .{ .name = "rts_alloc", .addr = @intFromPtr(&rts_node.rts_alloc) },
            .{ .name = "rts_store_field", .addr = @intFromPtr(&rts_node.rts_store_field) },
            .{ .name = "rts_load_field", .addr = @intFromPtr(&rts_node.rts_load_field) },
            .{ .name = "rts_store", .addr = @intFromPtr(&rts_node.rts_store) },
        };

        const rts_io = @import("../rts/io.zig");
        const io_symbols = [_]Symbol{
            .{ .name = "rts_putStrLn", .addr = @intFromPtr(&rts_io.rts_putStrLn) },
            .{ .name = "rts_putStr", .addr = @intFromPtr(&rts_io.rts_putStr) },
            .{ .name = "rts_putChar", .addr = @intFromPtr(&rts_io.rts_putChar) },
            .{ .name = "rts_charlist_to_cstring", .addr = @intFromPtr(&rts_io.rts_charlist_to_cstring) },
            .{ .name = "rts_cstring_to_charlist", .addr = @intFromPtr(&rts_io.rts_cstring_to_charlist) },
            .{ .name = "rts_error", .addr = @intFromPtr(&rts_io.rts_error) },
        };

        const es = c.LLVMOrcLLJITGetExecutionSession(self.jit);
        const main_dylib = c.LLVMOrcLLJITGetMainJITDylib(self.jit);

        inline for (symbols ++ io_symbols) |sym| {
            try self.defineAbsoluteSymbol(es, main_dylib, sym.name, sym.addr);
        }
    }

    /// Define a single absolute symbol in a JIT dylib.
    fn defineAbsoluteSymbol(
        self: *JitEngine,
        es: llvm.OrcExecutionSessionRef,
        dylib: llvm.OrcJITDylibRef,
        name: [:0]const u8,
        addr: usize,
    ) JitError!void {
        _ = self;
        const interned = c.LLVMOrcExecutionSessionIntern(es, name.ptr);

        var pair: c.LLVMOrcCSymbolMapPair = .{
            .Name = interned,
            .Sym = .{
                .Address = @intCast(addr),
                .Flags = .{
                    .GenericFlags = c.LLVMJITSymbolGenericFlagsExported,
                    .TargetFlags = 0,
                },
            },
        };

        const mu = c.LLVMOrcAbsoluteSymbols(&pair, 1);
        const err = c.LLVMOrcJITDylibDefine(dylib, mu);
        if (err != null) {
            c.LLVMConsumeError(err);
            return JitError.RtsRegistrationFailed;
        }
    }
};

/// Create a copy of the GRIN program with `replExpr__` renamed to the
/// given target name. The unique ID is preserved.
fn patchEntryPointName(allocator: Allocator, program: *const grin_ast.Program, target_name: []const u8) Allocator.Error!grin_ast.Program {
    const new_defs = try allocator.alloc(grin_ast.Def, program.defs.len);
    for (program.defs, 0..) |def, i| {
        new_defs[i] = def;
        if (std.mem.eql(u8, def.name.base, "replExpr__")) {
            new_defs[i].name = .{
                .base = target_name,
                .unique = def.name.unique,
            };
        }
    }
    return .{
        .defs = new_defs,
        .field_types = .{},
        .arities = .{},
    };
}

// ── Result formatting ─────────────────────────────────────────────────

/// Format the raw i64 result from a JIT'd GRIN function.
///
/// GRIN functions return i64 which is either:
/// - A literal integer value, or
/// - A pointer to a heap node (cast to i64).
///
/// We check if the value looks like a valid heap pointer (non-zero,
/// aligned) and try to interpret it as a node. If that fails, we
/// treat it as a plain integer.
/// RTS thunk-forcing function. Takes a heap pointer, returns forced WHNF pointer.
const ForceFn = *const fn (*anyopaque) callconv(.c) *anyopaque;

fn formatJitResult(allocator: Allocator, raw: i64, tags: KnownTags, force_fn: ?ForceFn) Allocator.Error![]const u8 {
    // Low-bit tagging (see #624):
    //   bit 0 set   → tagged integer, value = raw >> 1
    //   bit 0 clear → heap pointer (or null for Unit)
    const as_usize: usize = @bitCast(raw);

    if (as_usize & 1 == 1) {
        // Tagged integer — arithmetic shift right to recover the value.
        const value = raw >> 1;
        return std.fmt.allocPrint(allocator, "{d}", .{value});
    }

    // Heap pointer (low bit clear). Null (0) is Unit.
    if (raw == 0) return allocator.dupe(u8, "");

    // Force thunks to WHNF if the RTS force function is available.
    var effective_usize = as_usize;
    if (force_fn) |force| {
        if (as_usize >= 0x1000 and as_usize % @alignOf(*anyopaque) == 0) {
            const forced: *anyopaque = force(@ptrFromInt(as_usize));
            const forced_int: usize = @intFromPtr(forced);
            // After forcing, the result might be a tagged integer.
            if (forced_int & 1 == 1) {
                const value: i64 = @bitCast(forced_int);
                return std.fmt.allocPrint(allocator, "{d}", .{value >> 1});
            }
            effective_usize = forced_int;
        }
    }

    // Validate that the pointer looks like a heap node before
    // dereferencing. Must be above the first page to avoid
    // accidental dereference of small values.
    const MIN_HEAP_PTR: usize = 0x1000;
    if (effective_usize >= MIN_HEAP_PTR and effective_usize % @alignOf(*anyopaque) == 0) {
        const node_ptr: *const rts_node.Node = @ptrFromInt(effective_usize);
        const tag_int: u64 = @intFromEnum(node_ptr.tag);
        if (tag_int <= 0x10000 and node_ptr.n_fields <= 1024) {
            return formatNode(allocator, node_ptr, tags, force_fn);
        }
    }

    // Fallback: display as raw integer (shouldn't normally reach here).
    return std.fmt.allocPrint(allocator, "{d}", .{raw});
}

/// Format a heap node as a human-readable string using dynamic tag
/// discriminants from the compilation's tag table.
fn formatNode(allocator: Allocator, node: *const rts_node.Node, tags: KnownTags, force_fn: ?ForceFn) Allocator.Error![]const u8 {
    const tag_int: u64 = @intFromEnum(node.tag);
    const disc: i64 = @bitCast(tag_int);

    // Unit (RTS-level tag 0)
    if (tag_int == @intFromEnum(rts_node.Tag.Unit)) {
        return allocator.dupe(u8, "");
    }

    // Boolean constructors (nullary, 0 fields)
    if (tags.true_disc) |td| {
        if (disc == td and node.n_fields == 0) return allocator.dupe(u8, "True");
    }
    if (tags.false_disc) |fd| {
        if (disc == fd and node.n_fields == 0) return allocator.dupe(u8, "False");
    }

    // Nothing (nullary, 0 fields)
    if (tags.nothing_disc) |nd| {
        if (disc == nd and node.n_fields == 0) return allocator.dupe(u8, "Nothing");
    }

    // Just x (1 field)
    if (tags.just_disc) |jd| {
        if (disc == jd and node.n_fields == 1) {
            const inner_raw: i64 = @bitCast(rts_node.fieldsConst(node)[0]);
            const inner = try formatJitResult(allocator, inner_raw, tags, force_fn);
            defer allocator.free(inner);
            return std.fmt.allocPrint(allocator, "Just {s}", .{inner});
        }
    }

    // List: [] (Nil) or x : xs (Cons)
    if (tags.nil_disc) |nd| {
        if (disc == nd and node.n_fields == 0) return allocator.dupe(u8, "[]");
    }
    if (tags.cons_disc) |cd| {
        if (disc == cd and node.n_fields == 2) {
            return formatList(allocator, node, tags, force_fn);
        }
    }

    // Generic constructor display
    if (node.n_fields == 0) {
        return std.fmt.allocPrint(allocator, "<constructor tag={d}>", .{tag_int});
    }

    var result = try std.fmt.allocPrint(allocator, "<constructor tag={d}", .{tag_int});
    var i: u32 = 0;
    while (i < node.n_fields) : (i += 1) {
        const field_raw: i64 = @bitCast(rts_node.fieldsConst(node)[i]);
        const field_str = try formatJitResult(allocator, field_raw, tags, force_fn);
        defer allocator.free(field_str);
        const new = try std.fmt.allocPrint(allocator, "{s} {s}", .{ result, field_str });
        allocator.free(result);
        result = new;
    }
    const final = try std.fmt.allocPrint(allocator, "{s}>", .{result});
    allocator.free(result);
    return final;
}

/// Format a Cons-headed list as "[e1,e2,e3]".
/// Traverses the spine, collecting elements until Nil or a non-list node.
fn formatList(allocator: Allocator, head_node: *const rts_node.Node, tags: KnownTags, force_fn: ?ForceFn) Allocator.Error![]const u8 {
    const nil_disc = tags.nil_disc orelse return allocator.dupe(u8, "[...]");
    const cons_disc = tags.cons_disc orelse return allocator.dupe(u8, "[...]");

    // First pass: check if this is a [Char] list (String).
    // If every element is a printable character, format as "string".
    if (isCharList(head_node, cons_disc, nil_disc)) {
        return formatCharList(allocator, head_node, cons_disc, nil_disc);
    }

    var buf = std.ArrayListUnmanaged(u8){};
    try buf.append(allocator, '[');

    var current: *const rts_node.Node = head_node;
    var first = true;
    var depth: usize = 0;
    const max_depth: usize = 100; // Safety limit

    while (depth < max_depth) : (depth += 1) {
        const cur_disc: i64 = @bitCast(@as(u64, @intFromEnum(current.tag)));

        if (cur_disc == nil_disc and current.n_fields == 0) {
            // End of list
            break;
        }

        if (cur_disc != cons_disc or current.n_fields != 2) {
            // Not a proper list tail — show as improper
            try buf.appendSlice(allocator, "|...");
            break;
        }

        if (!first) try buf.append(allocator, ',');
        first = false;

        // Format the head element
        const head_raw: i64 = @bitCast(rts_node.fieldsConst(current)[0]);
        const elem = try formatJitResult(allocator, head_raw, tags, force_fn);
        defer allocator.free(elem);
        try buf.appendSlice(allocator, elem);

        // Advance to the tail, forcing thunks if possible.
        var tail_raw: usize = rts_node.fieldsConst(current)[1];
        // Force the tail pointer if it's a valid heap pointer (thunk).
        if (force_fn) |force| {
            if (tail_raw >= 0x1000 and tail_raw % @alignOf(*anyopaque) == 0) {
                const forced = force(@ptrFromInt(tail_raw));
                tail_raw = @intFromPtr(forced);
            }
        }
        if (tail_raw == 0 or tail_raw % @alignOf(*anyopaque) != 0) break;
        current = @ptrFromInt(tail_raw);
    }

    try buf.append(allocator, ']');
    return buf.toOwnedSlice(allocator);
}

/// Check if a list is a [Char] — every element is a valid Unicode codepoint
/// stored as a raw integer (not a heap pointer).
fn isCharList(head_node: *const rts_node.Node, cons_disc: i64, nil_disc: i64) bool {
    var current: *const rts_node.Node = head_node;
    var depth: usize = 0;
    const max_depth: usize = 1000;

    while (depth < max_depth) : (depth += 1) {
        const cur_disc: i64 = @bitCast(@as(u64, @intFromEnum(current.tag)));

        if (cur_disc == nil_disc and current.n_fields == 0) return depth > 0;
        if (cur_disc != cons_disc or current.n_fields != 2) return false;

        const head_val: u64 = rts_node.fieldsConst(current)[0];
        // Characters are tagged integers (low bit set, value = raw >> 1).
        // Must be a tagged integer with a valid Unicode codepoint.
        if (head_val & 1 != 1) return false;
        const codepoint = head_val >> 1;
        if (codepoint > 0x10FFFF) return false;

        const tail_raw: usize = rts_node.fieldsConst(current)[1];
        if (tail_raw == 0 or tail_raw % @alignOf(*anyopaque) != 0) return false;
        current = @ptrFromInt(tail_raw);
    }
    return false;
}

/// Format a [Char] list as a quoted string: "hello".
fn formatCharList(allocator: Allocator, head_node: *const rts_node.Node, cons_disc: i64, nil_disc: i64) Allocator.Error![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    try buf.append(allocator, '"');

    var current: *const rts_node.Node = head_node;
    var depth: usize = 0;
    const max_depth: usize = 1000;

    while (depth < max_depth) : (depth += 1) {
        const cur_disc: i64 = @bitCast(@as(u64, @intFromEnum(current.tag)));
        if (cur_disc == nil_disc and current.n_fields == 0) break;
        if (cur_disc != cons_disc or current.n_fields != 2) break;

        const raw_ch: u64 = rts_node.fieldsConst(current)[0];
        // Untag: characters are tagged integers (value = raw >> 1).
        const ch: u64 = raw_ch >> 1;
        if (ch < 128) {
            try buf.append(allocator, @intCast(ch));
        } else {
            // Encode as Unicode escape for non-ASCII
            var code_buf: [4]u8 = undefined;
            const cp: u21 = @intCast(ch);
            const len = std.unicode.utf8Encode(cp, &code_buf) catch 0;
            if (len > 0) {
                try buf.appendSlice(allocator, code_buf[0..len]);
            }
        }

        const tail_raw: usize = rts_node.fieldsConst(current)[1];
        if (tail_raw == 0 or tail_raw % @alignOf(*anyopaque) != 0) break;
        current = @ptrFromInt(tail_raw);
    }

    try buf.append(allocator, '"');
    return buf.toOwnedSlice(allocator);
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "jit engine: create and destroy" {
    var engine = try JitEngine.init(testing.allocator);
    defer engine.deinit();
}

test "jit engine: execute literal expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var engine = try JitEngine.init(alloc);
    defer engine.deinit();

    // Build a trivial GRIN program: replExpr__ = return (Lit 42)
    const body = try alloc.create(grin_ast.Expr);
    body.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const defs = try alloc.alloc(grin_ast.Def, 1);
    defs[0] = .{
        .name = .{ .base = "replExpr__", .unique = .{ .value = 0 } },
        .params = &.{},
        .body = body,
    };

    const program = grin_ast.Program{
        .defs = defs,
        .field_types = .{},
        .arities = .{},
    };

    const result = try engine.execute(&program);
    try testing.expectEqualStrings("42", result.value);
}

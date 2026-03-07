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
};

// ── JIT Engine ────────────────────────────────────────────────────────

/// Execution engine backed by LLVM ORC LLJIT.
///
/// For each program, translates GRIN → LLVM IR, feeds the IR module
/// to LLJIT, resolves the entry-point symbol, calls it, and formats
/// the result.
pub const JitEngine = struct {
    allocator: Allocator,
    jit: llvm.OrcLLJITRef,

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
        if (self.jit) |jit| {
            const err = c.LLVMOrcDisposeLLJIT(jit);
            if (err != null) c.LLVMConsumeError(err);
        }
    }

    /// Translate a GRIN program to LLVM IR, JIT-compile it, execute the
    /// entry point, and return the formatted result.
    pub fn execute(self: *JitEngine, program: *const grin_ast.Program) JitError!ExecResult {
        // 1. Translate GRIN → LLVM IR string.
        //    We use a temporary GrinTranslator to produce the IR text,
        //    then parse it into a fresh module owned by a ThreadSafeContext.
        //    This avoids a double-free: GrinTranslator.deinit() destroys its
        //    own LLVM context (and any modules created in it), but LLJIT also
        //    takes ownership of the module. By going through IR text we
        //    cleanly decouple the two ownership domains.
        //
        //    Before translating, we rename the REPL entry point to "main"
        //    so the translator emits the correct C-ABI return type (i32).
        //    The translator special-cases "main" but treats other zero-param
        //    functions as void-returning, which is incorrect for our use case.
        //    tracked in: https://github.com/adinapoli/rusholme/issues/484
        const patched_program = patchEntryPointName(self.allocator, program) catch {
            return JitError.OutOfMemory;
        };

        var translator = GrinTranslator.init(self.allocator);
        defer translator.deinit();

        const raw_ir = translator.translateProgram(patched_program) catch {
            return JitError.TranslationFailed;
        };
        defer self.allocator.free(raw_ir);

        // The GRIN-to-LLVM translator declares main as returning i32 but
        // emits `ret i64 <val>` for integer literals — a type mismatch that
        // the textual IR parser rejects.  We patch the IR to use i64 return,
        // matching the actual ret instructions.
        // tracked in: https://github.com/adinapoli/rusholme/issues/484
        const ir_text = std.mem.replaceOwned(u8, self.allocator, raw_ir, "define i32 @main()", "define i64 @main()") catch {
            return JitError.OutOfMemory;
        };
        defer self.allocator.free(ir_text);

        // 2. Create a thread-safe context and parse the IR into it.
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

        // Set the module's data layout and triple to match the JIT.
        const data_layout_str = c.LLVMOrcLLJITGetDataLayoutStr(self.jit);
        c.LLVMSetDataLayout(llvm_module, data_layout_str);
        const triple = c.LLVMGetDefaultTargetTriple();
        defer c.LLVMDisposeMessage(triple);
        c.LLVMSetTarget(llvm_module, triple);

        // 3. Wrap in a thread-safe module and add to JIT.
        //    LLVMOrcCreateNewThreadSafeModule takes ownership of both the
        //    module and the context — the JIT will dispose them when the
        //    module is removed.
        const ts_mod = c.LLVMOrcCreateNewThreadSafeModule(llvm_module, ts_ctx);
        // NOTE: Do NOT dispose the ThreadSafeContext here. The ThreadSafeModule
        // takes ownership and will clean it up when the JIT disposes the module.
        // Premature disposal causes a use-after-free during JIT compilation.
        // tracked in: https://github.com/adinapoli/rusholme/issues/485

        const main_dylib = c.LLVMOrcLLJITGetMainJITDylib(self.jit);
        const add_err = c.LLVMOrcLLJITAddLLVMIRModule(self.jit, main_dylib, ts_mod);
        if (add_err != null) {
            c.LLVMConsumeError(add_err);
            return JitError.ModuleAddFailed;
        }

        // 4. Look up the entry point. After patching, the entry point is
        //    always named "main".
        var addr: llvm.OrcExecutorAddress = 0;
        const lookup_err = c.LLVMOrcLLJITLookup(self.jit, &addr, "main");
        if (lookup_err != null) {
            c.LLVMConsumeError(lookup_err);
            return JitError.EntryPointNotFound;
        }

        // 4. Call the entry point. GRIN functions return i64 (either a
        //    literal value or a pointer to a heap node cast to i64).
        const EntryFn = *const fn () callconv(.c) i64;
        const entry_fn: EntryFn = @ptrFromInt(addr);
        const raw_result = entry_fn();

        // 5. Format the result.
        const formatted = formatJitResult(self.allocator, raw_result) catch {
            return JitError.FormatError;
        };

        return .{ .value = formatted };
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

        // Also register IO functions.
        const rts_io = @import("../rts/io.zig");
        const io_symbols = [_]Symbol{
            .{ .name = "rts_putStrLn", .addr = @intFromPtr(&rts_io.rts_putStrLn) },
            .{ .name = "rts_putStr", .addr = @intFromPtr(&rts_io.rts_putStr) },
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

/// Create a copy of the GRIN program with `replExpr__` renamed to `main`.
///
/// The GRIN-to-LLVM translator special-cases "main" to use the C ABI
/// (i32 return type). Other zero-param functions get void return, which
/// is incorrect for the REPL entry point. This function works around
/// that limitation by renaming the entry point before translation.
fn patchEntryPointName(allocator: Allocator, program: *const grin_ast.Program) Allocator.Error!grin_ast.Program {
    const new_defs = try allocator.alloc(grin_ast.Def, program.defs.len);
    for (program.defs, 0..) |def, i| {
        new_defs[i] = def;
        if (std.mem.eql(u8, def.name.base, "replExpr__")) {
            new_defs[i].name = .{
                .base = "main",
                .unique = def.name.unique,
            };
        }
    }
    return .{ .defs = new_defs };
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
fn formatJitResult(allocator: Allocator, raw: i64) Allocator.Error![]const u8 {
    // Check if the result is a valid-looking pointer to a heap node.
    // Heap nodes are allocated by rts_alloc and have a specific layout
    // with a tag in the first 8 bytes.
    const as_usize: usize = @bitCast(raw);

    if (as_usize != 0 and as_usize % @alignOf(*anyopaque) == 0) {
        // Try to interpret as a heap node pointer.
        const node_ptr: *const rts_node.Node = @ptrFromInt(as_usize);

        // Validate: check that tag and n_fields look reasonable.
        // Heap nodes have tag >= 0 and n_fields < some reasonable bound.
        if (node_ptr.n_fields < 1024) {
            return formatNode(allocator, node_ptr);
        }
    }

    // Plain integer literal.
    return std.fmt.allocPrint(allocator, "{d}", .{raw});
}

/// Format a heap node as a human-readable string.
fn formatNode(allocator: Allocator, node: *const rts_node.Node) Allocator.Error![]const u8 {
    // For nullary constructors, just print the tag number for now.
    // A full implementation would map tag IDs back to constructor names,
    // but that requires threading the tag table from compilation.
    const tag_int = @intFromEnum(node.tag);
    if (node.n_fields == 0) {
        return std.fmt.allocPrint(allocator, "<constructor tag={d}>", .{tag_int});
    }

    var result = try std.fmt.allocPrint(allocator, "<constructor tag={d}", .{tag_int});
    const field_slots = rts_node.fieldsConst(node);
    var i: u32 = 0;
    while (i < node.n_fields) : (i += 1) {
        const field_val: i64 = @bitCast(field_slots[i]);
        const new = try std.fmt.allocPrint(allocator, "{s} {d}", .{ result, field_val });
        allocator.free(result);
        result = new;
    }
    const final = try std.fmt.allocPrint(allocator, "{s}>", .{result});
    allocator.free(result);
    return final;
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

    const program = grin_ast.Program{ .defs = defs };

    const result = try engine.execute(&program);
    try testing.expectEqualStrings("42", result.value);
}

//! GRIN Evaluator State: Heap, Environment, and Function Table.
//!
//! This module implements the foundational data structures for the GRIN
//! tree-walking evaluator as specified in issue #318:
//!
//! - **Heap**: Array-backed simulated heap for allocating GRIN nodes
//! - **Environment**: Scoped variable binding map with push/pop scope
//! - **FunctionTable**: Map from function names to their GRIN definitions
//!
//! The evaluator itself (expression evaluation logic) is implemented in
//! a separate module (see issue #319).
//!
//! Reference: docs/decisions/0001-primops-and-rts-architecture.md
//! Reference: Podlovics, Hruska & Pénzes, "A Modern Look at GRIN", 2020.

const std = @import("std");
const Allocator = std.mem.Allocator;

const ast = @import("ast.zig");
const Name = ast.Name;
const Val = ast.Val;
const Def = ast.Def;
const Program = ast.Program;
const Tag = ast.Tag;

// ── Heap Pointer ─────────────────────────────────────────────────────────

/// An opaque pointer into the simulated heap.
///
/// This is not a raw pointer but an index into the heap's node array,
/// making it safe for GC and arena-based memory management.
pub const HeapPtr = struct {
    /// The index into the heap's nodes array.
    index: u32,

    /// Sentinel value for null/invalid pointers.
    pub const null_ptr: HeapPtr = .{ .index = std.math.maxInt(u32) };

    /// Check if this pointer is valid (not null).
    pub fn isValid(self: HeapPtr) bool {
        return self.index != std.math.maxInt(u32);
    }

    pub fn format(self: HeapPtr, w: *std.Io.Writer) std.Io.Writer.Error!void {
        if (self.isValid()) {
            try w.print("HeapPtr({d})", .{self.index});
        } else {
            try w.writeAll("HeapPtr(null)");
        }
    }
};

// ── Heap Node ────────────────────────────────────────────────────────────

/// A heap-allocated node.
///
/// This represents the runtime representation of a GRIN value on the heap.
/// Unlike `Val` (which is the IR representation), `HeapNode` is optimized
/// for runtime evaluation.
pub const HeapNode = union(enum) {
    /// A constructor node: tag + fields.
    /// E.g., `CJust [42]`, `CCons [1, CNil]`.
    Con: struct {
        tag: Tag,
        fields: []const Val,
    },

    /// A function closure / thunk (F-tagged).
    /// Contains the function name and captured free variables.
    Thunk: struct {
        func_name: Name,
        captured: []const Val,
    },

    /// A partial application (P-tagged).
    /// Contains the function name, applied args, and count of missing args.
    Partial: struct {
        func_name: Name,
        args: []const Val,
        missing: u32,
    },

    /// A literal value stored on the heap (for indirection).
    Lit: ast.Literal,

    /// Unit value.
    Unit: void,

    /// Blackhole: used during evaluation to detect infinite loops.
    /// When we enter a thunk, we overwrite it with Blackhole first.
    /// If we encounter a Blackhole during eval, we have a cycle.
    Blackhole: void,
};

// ── Simulated Heap ───────────────────────────────────────────────────────

/// A simulated heap for the GRIN evaluator.
///
/// This is an array-backed heap where each cell holds a `HeapNode`.
/// Operations:
/// - `alloc(node) -> HeapPtr` — store a node, return its address
/// - `read(ptr) -> ?HeapNode` — fetch a node
/// - `write(ptr, node)` — overwrite a node (for `update`)
pub const Heap = struct {
    /// The underlying allocator for heap nodes.
    allocator: Allocator,

    /// All allocated heap nodes.
    nodes: std.ArrayList(HeapNode),

    /// Initialize a new heap with the given allocator.
    pub fn init(allocator: Allocator) Heap {
        return .{
            .allocator = allocator,
            .nodes = .empty,
        };
    }

    /// Deallocate the heap and all its nodes.
    pub fn deinit(self: *Heap) void {
        // Free any allocated field slices
        for (self.nodes.items) |node| {
            switch (node) {
                .Con => |con| {
                    self.allocator.free(con.fields);
                },
                .Thunk => |thunk| {
                    self.allocator.free(thunk.captured);
                },
                .Partial => |partial| {
                    self.allocator.free(partial.args);
                },
                else => {},
            }
        }
        self.nodes.deinit(self.allocator);
    }

    /// Allocate a node on the heap, returning a pointer to it.
    pub fn alloc(self: *Heap, node: HeapNode) error{OutOfMemory}!HeapPtr {
        const idx: u32 = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, node);
        return .{ .index = idx };
    }

    /// Read a node from the heap at the given pointer.
    /// Returns null if the pointer is invalid.
    pub fn read(self: Heap, ptr: HeapPtr) ?HeapNode {
        if (!ptr.isValid()) return null;
        if (ptr.index >= self.nodes.items.len) return null;
        return self.nodes.items[ptr.index];
    }

    /// Write a node to the heap at the given pointer.
    /// Returns false if the pointer is invalid.
    /// Used for `update` expressions in GRIN.
    pub fn write(self: *Heap, ptr: HeapPtr, node: HeapNode) bool {
        if (!ptr.isValid()) return false;
        if (ptr.index >= self.nodes.items.len) return false;

        // Free the old node's fields before overwriting
        const old_node = &self.nodes.items[ptr.index];
        switch (old_node.*) {
            .Con => |con| self.allocator.free(con.fields),
            .Thunk => |thunk| self.allocator.free(thunk.captured),
            .Partial => |partial| self.allocator.free(partial.args),
            else => {},
        }

        self.nodes.items[ptr.index] = node;
        return true;
    }

    /// Get the current size of the heap.
    pub fn size(self: Heap) usize {
        return self.nodes.items.len;
    }
};

// ── Environment ──────────────────────────────────────────────────────────

/// A single scope in the environment.
const Scope = struct {
    /// Variable bindings in this scope.
    /// Maps Name -> Val (runtime value).
    bindings: std.AutoHashMapUnmanaged(u64, Val),

    /// Initialize an empty scope.
    fn init() Scope {
        return .{ .bindings = .empty };
    }

    /// Deallocate the scope.
    fn deinit(self: Scope, allocator: Allocator) void {
        @constCast(&self).bindings.deinit(allocator);
    }
};

/// A scoped variable binding map.
///
/// The environment maintains a stack of scopes. Variable lookup proceeds
/// from the innermost scope outward. New scopes are pushed when entering:
/// - Function calls (binding parameters)
/// - Case alternatives (binding pattern variables)
/// - Bind expressions (binding the LHS pattern)
pub const Environment = struct {
    /// The allocator for scope maps.
    allocator: Allocator,

    /// Stack of scopes, innermost last.
    scopes: std.ArrayList(Scope),

    /// Initialize a new environment with a single (global) scope.
    pub fn init(allocator: Allocator) error{OutOfMemory}!Environment {
        var scopes = try std.ArrayList(Scope).initCapacity(allocator, 4);
        scopes.appendAssumeCapacity(Scope.init());
        return .{
            .allocator = allocator,
            .scopes = scopes,
        };
    }

    /// Deallocate the environment and all scopes.
    pub fn deinit(self: *Environment) void {
        for (self.scopes.items) |scope| {
            scope.deinit(self.allocator);
        }
        self.scopes.deinit(self.allocator);
    }

    /// Push a new scope onto the stack.
    /// Used when entering a function call, case branch, or bind.
    pub fn pushScope(self: *Environment) error{OutOfMemory}!void {
        try self.scopes.append(self.allocator, Scope.init());
    }

    /// Pop the top scope from the stack.
    /// Used when exiting a function call, case branch, or bind.
    /// The global scope (index 0) cannot be popped.
    pub fn popScope(self: *Environment) void {
        if (self.scopes.items.len > 1) {
            if (self.scopes.pop()) |scope| {
                scope.deinit(self.allocator);
            }
        }
    }

    /// Bind a variable in the current (innermost) scope.
    pub fn bind(self: *Environment, name: Name, value: Val) error{OutOfMemory}!void {
        const current = &self.scopes.items[self.scopes.items.len - 1];
        try current.bindings.put(self.allocator, name.unique.value, value);
    }

    /// Look up a variable by name, searching from innermost to outermost scope.
    /// Returns null if the variable is not bound.
    pub fn lookup(self: Environment, name: Name) ?Val {
        // Search from innermost to outermost
        var i: usize = self.scopes.items.len;
        while (i > 0) {
            i -= 1;
            const scope = self.scopes.items[i];
            if (scope.bindings.get(name.unique.value)) |value| {
                return value;
            }
        }
        return null;
    }

    /// Check if we're in the global scope.
    pub fn inGlobalScope(self: Environment) bool {
        return self.scopes.items.len == 1;
    }

    /// Get the current scope depth (1 = global scope).
    pub fn depth(self: Environment) usize {
        return self.scopes.items.len;
    }
};

// ── Function Table ───────────────────────────────────────────────────────

/// A table mapping function names to their GRIN definitions.
///
/// Populated once at the start of evaluation from the `grin.Program`.
/// Used to resolve function calls during evaluation.
pub const FunctionTable = struct {
    /// Map from unique ID to function definition.
    /// We use the Name's unique value as the key.
    defs: std.AutoHashMapUnmanaged(u64, *const Def),

    /// The allocator for the hash map.
    allocator: Allocator,

    /// Initialize an empty function table.
    pub fn init(allocator: Allocator) FunctionTable {
        return .{
            .defs = .empty,
            .allocator = allocator,
        };
    }

    /// Deallocate the function table.
    pub fn deinit(self: *FunctionTable) void {
        self.defs.deinit(self.allocator);
    }

    /// Populate the table from a GRIN program.
    /// This should be called once at the start of evaluation.
    pub fn populate(self: *FunctionTable, program: *const Program) error{OutOfMemory}!void {
        for (program.defs) |*def| {
            try self.defs.put(self.allocator, def.name.unique.value, def);
        }
    }

    /// Look up a function by name.
    /// Returns null if the function is not defined.
    pub fn lookup(self: FunctionTable, name: Name) ?*const Def {
        return self.defs.get(name.unique.value);
    }

    /// Check if a function exists in the table.
    pub fn contains(self: FunctionTable, name: Name) bool {
        return self.defs.contains(name.unique.value);
    }

    /// Get the number of functions in the table.
    pub fn count(self: FunctionTable) usize {
        return self.defs.count();
    }
};

// ── GRIN Evaluator ───────────────────────────────────────────────────────

/// The GRIN evaluator state.
///
/// This struct holds all the state needed to evaluate a GRIN program:
/// - The heap for allocating nodes
/// - The environment for variable bindings
/// - The function table for resolving function calls
pub const GrinEvaluator = struct {
    /// The heap for allocating nodes.
    heap: Heap,

    /// The environment for variable bindings.
    env: Environment,

    /// The function table for resolving function calls.
    funcs: FunctionTable,

    /// The allocator for temporary allocations during evaluation.
    allocator: Allocator,

    /// Initialize a new evaluator with the given program.
    pub fn init(allocator: Allocator, program: *const Program) error{OutOfMemory}!GrinEvaluator {
        var heap = Heap.init(allocator);
        errdefer heap.deinit();

        var env = try Environment.init(allocator);
        errdefer env.deinit();

        var funcs = FunctionTable.init(allocator);
        errdefer funcs.deinit();

        try funcs.populate(program);

        return .{
            .heap = heap,
            .env = env,
            .funcs = funcs,
            .allocator = allocator,
        };
    }

    /// Deallocate the evaluator and all its state.
    pub fn deinit(self: *GrinEvaluator) void {
        self.heap.deinit();
        self.env.deinit();
        self.funcs.deinit();
    }

    /// Push a new scope onto the environment.
    pub fn pushScope(self: *GrinEvaluator) error{OutOfMemory}!void {
        try self.env.pushScope();
    }

    /// Pop a scope from the environment.
    pub fn popScope(self: *GrinEvaluator) void {
        self.env.popScope();
    }

    /// Bind a variable in the current scope.
    pub fn bind(self: *GrinEvaluator, name: Name, value: Val) error{OutOfMemory}!void {
        try self.env.bind(name, value);
    }

    /// Look up a variable in the environment.
    pub fn lookup(self: GrinEvaluator, name: Name) ?Val {
        return self.env.lookup(name);
    }

    /// Look up a function definition.
    pub fn lookupFunc(self: GrinEvaluator, name: Name) ?*const Def {
        return self.funcs.lookup(name);
    }

    /// Allocate a node on the heap.
    pub fn allocNode(self: *GrinEvaluator, node: HeapNode) error{OutOfMemory}!HeapPtr {
        return self.heap.alloc(node);
    }

    /// Read a node from the heap.
    pub fn readNode(self: GrinEvaluator, ptr: HeapPtr) ?HeapNode {
        return self.heap.read(ptr);
    }

    /// Write a node to the heap (for update operations).
    pub fn writeNode(self: *GrinEvaluator, ptr: HeapPtr, node: HeapNode) bool {
        return self.heap.write(ptr, node);
    }

    // ── Expression Evaluation Methods ───────────────────────────────────────

    /// Resolve a Val to its runtime value, looking up variables if needed.
    fn resolveVal(self: *const GrinEvaluator, v: *const Val) EvalError!Val {
        return switch (v.*) {
            .Var => |name| self.env.lookup(name) orelse return error.UnboundVariable,
            .Unit => Val{ .Unit = {} },
            .Lit => |lit| Val{ .Lit = lit },
            .ValTag => |tag| Val{ .ValTag = tag },
            .ConstTagNode => |ctn| b: {
                // For ConstTagNode, we always need to allocate new fields when storing to heap
                // to ensure proper ownership. The fields may be temporary test allocations.
                var resolved_fields = try self.allocator.alloc(Val, ctn.fields.len);
                for (ctn.fields, 0..) |field, i| {
                    resolved_fields[i] = try self.resolveVal(@constCast(&field));
                }
                break :b Val{ .ConstTagNode = .{ .tag = ctn.tag, .fields = resolved_fields } };
            },
            .VarTagNode => |vtn| b: {
                // Need to resolve the tag variable and fields
                const tag_val = try self.resolveVal(@constCast(&Val{ .Var = vtn.tag_var }));
                var resolved_fields = try self.allocator.alloc(Val, vtn.fields.len);
                for (vtn.fields, 0..) |field, i| {
                    resolved_fields[i] = try self.resolveVal(@constCast(&field));
                }
                // For now, we can only construct ConstTagNode from resolved tags
                // This is a simplification - full VarTagNode handling may need more work
                switch (tag_val) {
                    .ValTag => |tag| {
                        break :b Val{ .ConstTagNode = .{ .tag = tag, .fields = resolved_fields } };
                    },
                    else => return error.TypeMismatch,
                }
            },
        };
    }

    /// Evaluate a GRIN expression and return the resulting value.
    pub fn eval(self: *GrinEvaluator, expr: *const ast.Expr) EvalError!Val {
        return switch (expr.*) {
            .Return => |v| self.resolveVal(@constCast(&v)),

            .Store => |v| b: {
                // Allocate the value on the heap, return a HeapPtr
                const resolved = try self.resolveVal(@constCast(&v));
                const heap_node = switch (resolved) {
                    .ConstTagNode => |ctn| HeapNode{ .Con = .{ .tag = ctn.tag, .fields = ctn.fields } },
                    .Unit => HeapNode{ .Unit = {} },
                    .Lit => |lit| HeapNode{ .Lit = lit },
                    .ValTag => |tag| HeapNode{ .Con = .{ .tag = tag, .fields = &.{} } },
                    .Var => unreachable, // Already resolved
                    .VarTagNode => unreachable, // Already resolved
                };
                const ptr = try self.heap.alloc(heap_node);
                // Return pointer as a special value - for now we store it in a variable
                // In practice, we need a HeapPtr value type, but we'll use a placeholder
                // tracked in: https://github.com/adinapoli/rusholme/issues/322
                break :b Val{ .Var = Name{ .base = "_hptr", .unique = .{ .value = ptr.index } } };
            },

            .Fetch => |fetch| b: {
                // Read from the heap at the given pointer
                const name = fetch.ptr;
                const ptr_val = self.env.lookup(name) orelse return error.UnboundVariable;
                const heap_ptr = if (ptr_val.Var.unique.value < @as(u64, std.math.maxInt(u32)))
                    HeapPtr{ .index = @intCast(ptr_val.Var.unique.value) }
                else
                    return error.InvalidHeapPointer;

                const node = self.heap.read(heap_ptr) orelse return error.InvalidHeapPointer;

                // If index is specified, extract that field
                if (fetch.index) |idx| {
                    switch (node) {
                        .Con => |con| {
                            if (idx >= con.fields.len) return error.TypeMismatch;
                            break :b con.fields[idx];
                        },
                        else => return error.TypeMismatch,
                    }
                } else break :b switch (node) {
                    // No index, return the whole node as a value
                    .Con => |con| Val{ .ConstTagNode = .{ .tag = con.tag, .fields = con.fields } },
                    .Lit => |lit| Val{ .Lit = lit },
                    .Unit => Val{ .Unit = {} },
                    else => return error.TypeMismatch,
                };
            },

            .Update => |update| b: {
                // Overwrite the heap cell at the given pointer
                const name = update.ptr;
                const ptr_val = self.env.lookup(name) orelse return error.UnboundVariable;
                const heap_ptr = if (ptr_val.Var.unique.value < @as(u64, std.math.maxInt(u32)))
                    HeapPtr{ .index = @intCast(ptr_val.Var.unique.value) }
                else
                    return error.InvalidHeapPointer;

                const resolved = try self.resolveVal(@constCast(&update.val));
                const heap_node = switch (resolved) {
                    .ConstTagNode => |ctn| HeapNode{ .Con = .{ .tag = ctn.tag, .fields = ctn.fields } },
                    .Unit => HeapNode{ .Unit = {} },
                    .Lit => |lit| HeapNode{ .Lit = lit },
                    .ValTag => |tag| HeapNode{ .Con = .{ .tag = tag, .fields = &.{} } },
                    .Var => unreachable, // Already resolved
                    .VarTagNode => unreachable, // Already resolved
                };

                if (!self.heap.write(heap_ptr, heap_node)) {
                    return error.InvalidHeapPointer;
                }
                break :b Val{ .Unit = {} };
            },

            .Bind => |bind_expr| b: {
                // Evaluate LHS, bind result to pattern, evaluate RHS
                const lhs_result = try self.eval(bind_expr.lhs);

                // For now, limited pattern matching: only Var pattern
                // tracked in: https://github.com/adinapoli/rusholme/issues/323
                switch (bind_expr.pat) {
                    .Var => |name| {
                        try self.env.bind(name, lhs_result);
                    },
                    .Unit => {},
                    .Lit => |lit| {
                        // Match literal values against the result
                        switch (lhs_result) {
                            .Lit => |r| {
                                // Compare literals based on their type
                                if (!std.meta.eql(r, lit)) return error.TypeMismatch;
                            },
                            else => return error.TypeMismatch,
                        }
                    },
                    // For complex patterns, we'd need more sophisticated matching
                    // For now, treat non-Var patterns as wildcards
                    else => {},
                }

                const rhs_result = try self.eval(bind_expr.rhs);
                break :b rhs_result;
            },

            .Block => |inner| self.eval(inner),

            // App and Case are handled in issue #320
            .App => return error.NotImplemented,
            .Case => return error.NotImplemented,
        };
    }
};

// ── Eval Error ────────────────────────────────────────────────────────────

/// Errors that can occur during GRIN evaluation.
pub const EvalError = error{
    UnboundVariable,
    InvalidHeapPointer,
    TypeMismatch,
    NotImplemented,
} || Allocator.Error || std.mem.Allocator.Error;

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

fn testName(base: []const u8, unique: u64) Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn conTag(base: []const u8, unique: u64) Tag {
    return .{ .tag_type = .{ .Con = {} }, .name = testName(base, unique) };
}

test "HeapPtr: validity" {
    const valid = HeapPtr{ .index = 5 };
    try testing.expect(valid.isValid());

    const invalid = HeapPtr.null_ptr;
    try testing.expect(!invalid.isValid());
}

test "Heap: alloc and read" {
    var heap = Heap.init(testing.allocator);
    defer heap.deinit();

    const node = HeapNode{ .Lit = .{ .Int = 42 } };
    const ptr = try heap.alloc(node);
    try testing.expect(ptr.isValid());

    const retrieved = heap.read(ptr);
    try testing.expect(retrieved != null);
    try testing.expectEqual(@as(i64, 42), retrieved.?.Lit.Int);
}

test "Heap: write (update)" {
    var heap = Heap.init(testing.allocator);
    defer heap.deinit();

    const ptr = try heap.alloc(.{ .Lit = .{ .Int = 42 } });
    const success = heap.write(ptr, .{ .Lit = .{ .Int = 99 } });
    try testing.expect(success);

    const retrieved = heap.read(ptr);
    try testing.expectEqual(@as(i64, 99), retrieved.?.Lit.Int);
}

test "Heap: invalid pointer returns null" {
    var heap = Heap.init(testing.allocator);
    defer heap.deinit();

    const invalid = HeapPtr{ .index = 9999 };
    try testing.expect(heap.read(invalid) == null);

    const null_ptr = HeapPtr.null_ptr;
    try testing.expect(heap.read(null_ptr) == null);
}

test "Heap: constructor node" {
    var heap = Heap.init(testing.allocator);
    defer heap.deinit();

    const fields = try testing.allocator.alloc(Val, 1);
    // Note: heap takes ownership of fields, so we don't free them manually
    fields[0] = .{ .Lit = .{ .Int = 42 } };

    const node = HeapNode{ .Con = .{
        .tag = conTag("Just", 1),
        .fields = fields,
    } };
    const ptr = try heap.alloc(node);

    const retrieved = heap.read(ptr);
    try testing.expect(retrieved != null);
    try testing.expectEqualStrings("Just", retrieved.?.Con.tag.name.base);
    try testing.expectEqual(@as(usize, 1), retrieved.?.Con.fields.len);
}

test "Environment: bind and lookup in global scope" {
    var env = try Environment.init(testing.allocator);
    defer env.deinit();

    const name = testName("x", 1);
    const value = Val{ .Lit = .{ .Int = 42 } };

    try env.bind(name, value);
    const retrieved = env.lookup(name);

    try testing.expect(retrieved != null);
    try testing.expectEqual(@as(i64, 42), retrieved.?.Lit.Int);
}

test "Environment: nested scopes" {
    var env = try Environment.init(testing.allocator);
    defer env.deinit();

    // Bind x = 42 in global scope
    const x = testName("x", 1);
    try env.bind(x, .{ .Lit = .{ .Int = 42 } });

    // Push new scope, shadow x = 99
    try env.pushScope();
    try env.bind(x, .{ .Lit = .{ .Int = 99 } });

    // Lookup should find 99 (innermost)
    const inner = env.lookup(x);
    try testing.expectEqual(@as(i64, 99), inner.?.Lit.Int);

    // Pop scope
    env.popScope();

    // Lookup should now find 42 (global)
    const outer = env.lookup(x);
    try testing.expectEqual(@as(i64, 42), outer.?.Lit.Int);
}

test "Environment: unbound variable returns null" {
    var env = try Environment.init(testing.allocator);
    defer env.deinit();

    const unknown = testName("unknown", 999);
    try testing.expect(env.lookup(unknown) == null);
}

test "Environment: scope depth" {
    var env = try Environment.init(testing.allocator);
    defer env.deinit();

    try testing.expect(env.inGlobalScope());
    try testing.expectEqual(@as(usize, 1), env.depth());

    try env.pushScope();
    try testing.expect(!env.inGlobalScope());
    try testing.expectEqual(@as(usize, 2), env.depth());

    try env.pushScope();
    try testing.expectEqual(@as(usize, 3), env.depth());

    env.popScope();
    try testing.expectEqual(@as(usize, 2), env.depth());
}

test "FunctionTable: populate and lookup" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var funcs = FunctionTable.init(testing.allocator);
    defer funcs.deinit();

    // Create a simple program with one function
    const body = try alloc.create(ast.Expr);
    body.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const def = Def{
        .name = testName("answer", 1),
        .params = &.{},
        .body = body,
    };

    const defs = try alloc.alloc(Def, 1);
    defs[0] = def;

    const program = Program{ .defs = defs };

    try funcs.populate(&program);
    try testing.expectEqual(@as(usize, 1), funcs.count());

    const found = funcs.lookup(testName("answer", 1));
    try testing.expect(found != null);
    try testing.expectEqualStrings("answer", found.?.name.base);
}

test "FunctionTable: missing function returns null" {
    var funcs = FunctionTable.init(testing.allocator);
    defer funcs.deinit();

    const missing = testName("missing", 999);
    try testing.expect(funcs.lookup(missing) == null);
    try testing.expect(!funcs.contains(missing));
}

test "GrinEvaluator: full integration" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a minimal program: main = return 42
    const body = try alloc.create(ast.Expr);
    body.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const main_def = Def{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const defs = try alloc.alloc(Def, 1);
    defs[0] = main_def;

    const program = Program{ .defs = defs };

    // Initialize evaluator
    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    // Verify function table
    try testing.expect(evaluator.funcs.contains(testName("main", 1)));

    // Test heap allocation
    const ptr = try evaluator.allocNode(.{ .Lit = .{ .Int = 99 } });
    const node = evaluator.readNode(ptr);
    try testing.expectEqual(@as(i64, 99), node.?.Lit.Int);

    // Test environment
    try evaluator.bind(testName("x", 2), .{ .Lit = .{ .Int = 100 } });
    const val = evaluator.lookup(testName("x", 2));
    try testing.expectEqual(@as(i64, 100), val.?.Lit.Int);
}

test "GrinEvaluator: scoped bindings" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(ast.Expr);
    body.* = .{ .Return = .{ .Unit = {} } };

    const defs = try alloc.alloc(Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const x = testName("x", 1);

    // Bind in global scope
    try evaluator.bind(x, .{ .Lit = .{ .Int = 1 } });
    try testing.expectEqual(@as(i64, 1), evaluator.lookup(x).?.Lit.Int);

    // Push scope and shadow
    try evaluator.pushScope();
    try evaluator.bind(x, .{ .Lit = .{ .Int = 2 } });
    try testing.expectEqual(@as(i64, 2), evaluator.lookup(x).?.Lit.Int);

    // Pop and verify original
    evaluator.popScope();
    try testing.expectEqual(@as(i64, 1), evaluator.lookup(x).?.Lit.Int);
}

// ── Expression Evaluation Tests ──────────────────────────────────────────

test "eval: Return literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(ast.Expr);
    body.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqual(@as(i64, 42), result.Lit.Int);
}

test "eval: Return variable" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create program where we bind a variable and return it
    const body = try alloc.create(ast.Expr);
    body.* = .{ .Return = .{ .Var = testName("x", 42) } };

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    try evaluator.bind(testName("x", 42), .{ .Lit = .{ .Int = 99 } });
    const result = try evaluator.eval(body);
    try testing.expectEqual(@as(i64, 99), result.Lit.Int);
}

test "eval: Store constructor node and fetch it back" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: store (CJust [42]) >>= \p -> fetch p
    const fields = try alloc.alloc(ast.Val, 1);
    fields[0] = ast.Val{ .Lit = .{ .Int = 42 } };

    const store_expr = try alloc.create(ast.Expr);
    store_expr.* = .{ .Store = ast.Val{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = fields,
    } } };

    const fetch_expr = try alloc.create(ast.Expr);
    fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 100), .index = null } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = ast.Val{ .Var = testName("p", 100) },
        .rhs = fetch_expr,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqualStrings("Just", result.ConstTagNode.tag.name.base);
    try testing.expectEqual(@as(usize, 1), result.ConstTagNode.fields.len);
    try testing.expectEqual(@as(i64, 42), result.ConstTagNode.fields[0].Lit.Int);
}

test "eval: Store nullary constructor and fetch it back" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: store (CNothing []) >>= \p -> fetch p
    const store_expr = try alloc.create(ast.Expr);
    store_expr.* = .{ .Store = ast.Val{ .ConstTagNode = .{
        .tag = conTag("Nothing", 2),
        .fields = &.{},
    } } };

    const fetch_expr = try alloc.create(ast.Expr);
    fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 101), .index = null } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = ast.Val{ .Var = testName("p", 101) },
        .rhs = fetch_expr,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqualStrings("Nothing", result.ConstTagNode.tag.name.base);
    try testing.expectEqual(@as(usize, 0), result.ConstTagNode.fields.len);
}

test "eval: Fetch with field index" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: store (CJust [#42]) >>= \p -> fetch p 0
    const fields = try alloc.alloc(ast.Val, 1);
    fields[0] = ast.Val{ .Lit = .{ .Int = 42 } };

    const store_expr = try alloc.create(ast.Expr);
    store_expr.* = .{ .Store = ast.Val{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = fields,
    } } };

    const fetch_expr = try alloc.create(ast.Expr);
    fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 102), .index = 0 } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = ast.Val{ .Var = testName("p", 102) },
        .rhs = fetch_expr,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqual(@as(i64, 42), result.Lit.Int);
}

test "eval: Update a heap node" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: store (CJust [1]) >>= \p -> update p (CNothing []) >>= \_ -> fetch p
    const fields_just = try alloc.alloc(ast.Val, 1);
    fields_just[0] = ast.Val{ .Lit = .{ .Int = 1 } };

    const store_expr = try alloc.create(ast.Expr);
    store_expr.* = .{ .Store = ast.Val{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = fields_just,
    } } };

    const update_expr = try alloc.create(ast.Expr);
    update_expr.* = .{ .Update = .{
        .ptr = testName("p", 103),
        .val = ast.Val{ .ConstTagNode = .{
            .tag = conTag("Nothing", 2),
            .fields = &.{},
        } },
    } };

    const inner_fetch_expr = try alloc.create(ast.Expr);
    inner_fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 103), .index = null } };

    const inner_bind = try alloc.create(ast.Expr);
    inner_bind.* = .{ .Bind = .{
        .lhs = update_expr,
        .pat = ast.Val{ .Unit = {} },
        .rhs = inner_fetch_expr,
    } };

    const outer_bind = try alloc.create(ast.Expr);
    outer_bind.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = ast.Val{ .Var = testName("p", 103) },
        .rhs = inner_bind,
    } };

    const body = outer_bind;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqualStrings("Nothing", result.ConstTagNode.tag.name.base);
}

test "eval: Nested binds" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: return 42 >>= \x -> return (x + 8)
    const return_42 = try alloc.create(ast.Expr);
    return_42.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const return_50 = try alloc.create(ast.Expr);
    return_50.* = .{ .Return = .{ .Lit = .{ .Int = 50 } } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = return_42,
        .pat = ast.Val{ .Var = testName("x", 104) },
        .rhs = return_50,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqual(@as(i64, 50), result.Lit.Int);
}

test "eval: Block expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const inner = try alloc.create(ast.Expr);
    inner.* = .{ .Return = .{ .Lit = .{ .Int = 77 } } };

    const block = try alloc.create(ast.Expr);
    block.* = .{ .Block = inner };

    const body = block;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqual(@as(i64, 77), result.Lit.Int);
}

test "eval: Unbound variable error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(ast.Expr);
    body.* = .{ .Return = .{ .Var = testName("nonexistent", 999) } };

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = evaluator.eval(body);
    try testing.expectError(EvalError.UnboundVariable, result);
}

test "eval: Return unit" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = try alloc.create(ast.Expr);
    body.* = .{ .Return = .{ .Unit = {} } };

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    // Check that result is Unit
    try testing.expectEqual(@as(ast.Val, .{ .Unit = {} }), result);
}

test "eval: Store and fetch literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: store (Lit 42) >>= \p -> fetch p
    const store_expr = try alloc.create(ast.Expr);
    store_expr.* = .{ .Store = ast.Val{ .Lit = .{ .Int = 123 } } };

    const fetch_expr = try alloc.create(ast.Expr);
    fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 105), .index = null } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = ast.Val{ .Var = testName("p", 105) },
        .rhs = fetch_expr,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqual(@as(i64, 123), result.Lit.Int);
}

test "eval: Two-element constructor (Cons cell)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: store (CCons [1, CNil []]) >>= \p -> fetch p
    const nil_fields = try alloc.alloc(ast.Val, 0);

    const cons_fields = try alloc.alloc(ast.Val, 2);
    cons_fields[0] = ast.Val{ .Lit = .{ .Int = 1 } };
    cons_fields[1] = ast.Val{ .ConstTagNode = .{ .tag = conTag("Nil", 3), .fields = nil_fields } };

    const store_expr = try alloc.create(ast.Expr);
    store_expr.* = .{ .Store = ast.Val{ .ConstTagNode = .{
        .tag = conTag("Cons", 4),
        .fields = cons_fields,
    } } };

    const fetch_expr = try alloc.create(ast.Expr);
    fetch_expr.* = .{ .Fetch = .{ .ptr = testName("p", 106), .index = null } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = ast.Val{ .Var = testName("p", 106) },
        .rhs = fetch_expr,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqualStrings("Cons", result.ConstTagNode.tag.name.base);
    try testing.expectEqual(@as(usize, 2), result.ConstTagNode.fields.len);
    try testing.expectEqual(@as(i64, 1), result.ConstTagNode.fields[0].Lit.Int);
    try testing.expectEqualStrings("Nil", result.ConstTagNode.fields[1].ConstTagNode.tag.name.base);
}

test "eval: Bind with literal pattern (matching)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: return 42 >>= \5 -> return 100
    const return_42 = try alloc.create(ast.Expr);
    return_42.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const return_100 = try alloc.create(ast.Expr);
    return_100.* = .{ .Return = .{ .Lit = .{ .Int = 100 } } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = return_42,
        .pat = ast.Val{ .Lit = .{ .Int = 42 } }, // Matches
        .rhs = return_100,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = try evaluator.eval(body);
    try testing.expectEqual(@as(i64, 100), result.Lit.Int);
}

test "eval: Bind with literal pattern (non-matching)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: return 42 >>= \5 -> return 100 (should fail: 42 != 5)
    const return_42 = try alloc.create(ast.Expr);
    return_42.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const return_100 = try alloc.create(ast.Expr);
    return_100.* = .{ .Return = .{ .Lit = .{ .Int = 100 } } };

    const bind_expr = try alloc.create(ast.Expr);
    bind_expr.* = .{ .Bind = .{
        .lhs = return_42,
        .pat = ast.Val{ .Lit = .{ .Int = 5 } }, // Doesn't match
        .rhs = return_100,
    } };

    const body = bind_expr;

    const defs = try alloc.alloc(ast.Def, 1);
    defs[0] = .{
        .name = testName("main", 1),
        .params = &.{},
        .body = body,
    };

    const program = ast.Program{ .defs = defs };

    var evaluator = try GrinEvaluator.init(testing.allocator, &program);
    defer evaluator.deinit();

    const result = evaluator.eval(body);
    try testing.expectError(EvalError.TypeMismatch, result);
}

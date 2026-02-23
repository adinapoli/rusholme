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
};

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
    var eval = try GrinEvaluator.init(testing.allocator, &program);
    defer eval.deinit();

    // Verify function table
    try testing.expect(eval.funcs.contains(testName("main", 1)));

    // Test heap allocation
    const ptr = try eval.allocNode(.{ .Lit = .{ .Int = 99 } });
    const node = eval.readNode(ptr);
    try testing.expectEqual(@as(i64, 99), node.?.Lit.Int);

    // Test environment
    try eval.bind(testName("x", 2), .{ .Lit = .{ .Int = 100 } });
    const val = eval.lookup(testName("x", 2));
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

    var eval = try GrinEvaluator.init(testing.allocator, &program);
    defer eval.deinit();

    const x = testName("x", 1);

    // Bind in global scope
    try eval.bind(x, .{ .Lit = .{ .Int = 1 } });
    try testing.expectEqual(@as(i64, 1), eval.lookup(x).?.Lit.Int);

    // Push scope and shadow
    try eval.pushScope();
    try eval.bind(x, .{ .Lit = .{ .Int = 2 } });
    try testing.expectEqual(@as(i64, 2), eval.lookup(x).?.Lit.Int);

    // Pop and verify original
    eval.popScope();
    try testing.expectEqual(@as(i64, 1), eval.lookup(x).?.Lit.Int);
}

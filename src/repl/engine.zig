//! REPL Execution Engine
//!
//! Wraps the GRIN tree-walking evaluator for use as a REPL execution
//! backend. Takes a compiled GRIN `Program`, evaluates the entry point
//! (either `main` or the REPL-generated `replExpr__`), and formats
//! the result as a human-readable string.
//!
//! This is the WASM execution backend. The native backend will use
//! LLVM ORC JIT instead (see Task 10).
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");
const Allocator = std.mem.Allocator;

const grin_ast = @import("../grin/ast.zig");
const evaluator_mod = @import("../grin/evaluator.zig");
const GrinEvaluator = evaluator_mod.GrinEvaluator;

const testing_io = testing.io;

// ── Result types ──────────────────────────────────────────────────────

/// Result of executing a GRIN program.
pub const ExecResult = struct {
    /// Human-readable string representation of the result value.
    value: []const u8,
};

/// Errors that can occur during execution.
pub const ExecError = evaluator_mod.EvalError || error{
    /// The entry-point function was not found in the program.
    EntryPointNotFound,
    /// Formatting the result value failed.
    FormatError,
};

// ── GRIN Engine ───────────────────────────────────────────────────────

/// Execution engine backed by the GRIN tree-walking evaluator.
///
/// For each program, creates a fresh `GrinEvaluator`, looks up the
/// entry point, evaluates it, and formats the result.
pub const GrinEngine = struct {
    allocator: Allocator,
    io: std.Io,

    pub fn init(allocator: Allocator, io: std.Io) GrinEngine {
        return .{ .allocator = allocator, .io = io };
    }

    /// Execute the entry-point function of a GRIN program and return
    /// its value as a formatted string.
    ///
    /// The entry point is looked up by name: first `replExpr__` (for
    /// expression inputs), then `main` (for declaration modules that
    /// define main). If neither is found, returns `EntryPointNotFound`.
    pub fn execute(self: *GrinEngine, program: *const grin_ast.Program) ExecError!ExecResult {
        var grin_eval = GrinEvaluator.init(self.allocator, program, self.io) catch {
            return ExecError.OutOfMemory;
        };
        defer grin_eval.deinit();

        // Find the entry point by scanning defs for matching base name.
        // The renamer assigns unique IDs, so we match by base name rather
        // than exact Name (which includes the unique suffix).
        const entry = findDefByBaseName(program, "replExpr__") orelse
            findDefByBaseName(program, "main") orelse
            return ExecError.EntryPointNotFound;

        const val = try grin_eval.eval(entry.body);
        
        const formatted = formatVal(self.allocator, val) catch {
            return ExecError.FormatError;
        };

        return .{ .value = formatted };
    }

    /// Find a GRIN definition by its base name (ignoring the unique suffix).
    fn findDefByBaseName(program: *const grin_ast.Program, base: []const u8) ?*const grin_ast.Def {
        for (program.defs) |*def| {
            if (std.mem.eql(u8, def.name.base, base)) return def;
        }
        return null;
    }
};

// ── Value formatting ──────────────────────────────────────────────────

/// Format a GRIN `Val` as a human-readable string.
///
/// Examples:
///   - `Lit(.Int(42))`    -> `"42"`
///   - `Lit(.String("x"))` -> `"\"x\""`
///   - `Lit(.Char('a'))`  -> `"'a'"`
///   - `Lit(.Float(3.14))` -> `"3.14"`
///   - `Unit`             -> `"()"`
///   - `ConstTagNode(CTrue, [])` -> `"True"`
///   - `ConstTagNode(CJust, [Lit(42)])` -> `"Just 42"`
///   - `ValTag(CTrue)`    -> `"True"`
fn formatVal(allocator: Allocator, val: grin_ast.Val) Allocator.Error![]const u8 {
    return switch (val) {
        .Lit => |lit| formatLit(allocator, lit),
        .Unit => try allocator.dupe(u8, ""),
        .ValTag => |tag| try allocator.dupe(u8, tag.name.base),
        .ConstTagNode => |ctn| formatConstTagNode(allocator, ctn),
        .Var => |name| try allocator.dupe(u8, name.base),
        .VarTagNode => try allocator.dupe(u8, "<var-tag-node>"),
    };
}

fn formatLit(allocator: Allocator, lit: grin_ast.Literal) Allocator.Error![]const u8 {
    return switch (lit) {
        .Int => |i| std.fmt.allocPrint(allocator, "{d}", .{i}),
        .Float => |f| std.fmt.allocPrint(allocator, "{d}", .{f}),
        .Bool => |b| try allocator.dupe(u8, if (b) "True" else "False"),
        .Char => |c| std.fmt.allocPrint(allocator, "'{u}'", .{c}),
        .String => |s| std.fmt.allocPrint(allocator, "\"{s}\"", .{s}),
    };
}

fn formatConstTagNode(
    allocator: Allocator,
    ctn: anytype,
) Allocator.Error![]const u8 {
    if (ctn.fields.len == 0) {
        return try allocator.dupe(u8, ctn.tag.name.base);
    }

    // Format as: ConstructorName field1 field2 ...
    // Build incrementally by concatenating formatted fields.
    var result = try allocator.dupe(u8, ctn.tag.name.base);
    for (ctn.fields) |field| {
        const field_str = try formatVal(allocator, field);
        defer allocator.free(field_str);
        const new = try std.fmt.allocPrint(allocator, "{s} {s}", .{ result, field_str });
        allocator.free(result);
        result = new;
    }

    return result;
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "engine: format integer literal" {
    const val = grin_ast.Val{ .Lit = .{ .Int = 42 } };
    const result = try formatVal(testing.allocator, val);
    defer testing.allocator.free(result);
    try testing.expectEqualStrings("42", result);
}

test "engine: format string literal" {
    const val = grin_ast.Val{ .Lit = .{ .String = "hello" } };
    const result = try formatVal(testing.allocator, val);
    defer testing.allocator.free(result);
    try testing.expectEqualStrings("\"hello\"", result);
}

test "engine: format unit" {
    const val = grin_ast.Val{ .Unit = {} };
    const result = try formatVal(testing.allocator, val);
    defer testing.allocator.free(result);
    // Unit formats to empty string for REPL - IO actions only show side effects
    try testing.expectEqualStrings("", result);
}

test "engine: format bare tag" {
    const val = grin_ast.Val{ .ValTag = .{
        .tag_type = .{ .Con = {} },
        .name = .{ .base = "True", .unique = .{ .value = 0 } },
    } };
    const result = try formatVal(testing.allocator, val);
    defer testing.allocator.free(result);
    try testing.expectEqualStrings("True", result);
}

test "engine: format constructor with fields" {
    const field = grin_ast.Val{ .Lit = .{ .Int = 42 } };
    const val = grin_ast.Val{ .ConstTagNode = .{
        .tag = .{
            .tag_type = .{ .Con = {} },
            .name = .{ .base = "Just", .unique = .{ .value = 0 } },
        },
        .fields = &.{field},
    } };
    const result = try formatVal(testing.allocator, val);
    defer testing.allocator.free(result);
    try testing.expectEqualStrings("Just 42", result);
}

test "engine: execute trivial GRIN program" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Build: replExpr__ = return (Lit 42)
    const body = try alloc.create(grin_ast.Expr);
    body.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const defs = try alloc.alloc(grin_ast.Def, 1);
    defs[0] = .{
        .name = .{ .base = "replExpr__", .unique = .{ .value = 0 } },
        .params = &.{},
        .body = body,
    };

    const program = grin_ast.Program{ .defs = defs };

    var engine = GrinEngine.init(alloc, testing_io);
    const result = try engine.execute(&program);

    try testing.expectEqualStrings("42", result.value);
}

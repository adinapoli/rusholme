//! Module dependency graph and topological compilation order.
//!
//! Given a set of Haskell source files, the compiler must determine the order
//! in which to compile them: if module A imports module B, then B must be
//! compiled first.  This module provides:
//!
//! 1. **`ModuleGraph`** — a directed graph keyed on module names, with an
//!    adjacency list representation (module → modules it imports).
//!
//! 2. **`topoSort`** — Kahn's algorithm over `ModuleGraph`, returning the
//!    compilation order (dependencies first).  Import cycles are detected and
//!    reported as structured diagnostics using Tarjan's SCC algorithm.
//!
//! 3. **`discoverModules`** — given a root module file path and a search path
//!    list, scans import declarations (header-only parse) and walks transitively
//!    to build the complete `ModuleGraph` for a compilation session.
//!
//! ## Algorithm references
//!
//! - Kahn, A.B. (1962). "Topological sorting of large networks."
//!   *Communications of the ACM*, 5(11), 558–562.
//! - Tarjan, R.E. (1972). "Depth-first search and linear graph algorithms."
//!   *SIAM Journal on Computing*, 1(2), 146–160.
//!
//! ## M2 scope / known limitations
//!
//! - Mutual recursion (`.hs-boot` files) is out of scope for M2. An import
//!   cycle always yields a hard error.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/433
//!
//! - Module search paths are specified by the caller; the compiler does not
//!   yet honour `--package-db` or cabal-style paths.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/368

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const lexer_mod = @import("../frontend/lexer.zig");
const layout_mod = @import("../frontend/layout.zig");
const parser_mod = @import("../frontend/parser.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");
const span_mod = @import("../diagnostics/span.zig");

pub const DiagnosticCollector = diag_mod.DiagnosticCollector;
pub const Diagnostic = diag_mod.Diagnostic;
pub const DiagnosticCode = diag_mod.DiagnosticCode;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;

// ── ModuleGraph ──────────────────────────────────────────────────────────

/// A directed graph of module dependencies.
///
/// Vertices are module names (e.g. `"Data.Map"`, `"Main"`).
/// An edge A → B means "module A imports module B" (B must compile before A).
///
/// All strings are owned by the `alloc` passed to `init` (expected arena).
pub const ModuleGraph = struct {
    alloc: std.mem.Allocator,
    /// Module name → vertex index.
    indices: std.StringHashMapUnmanaged(u32),
    /// Vertex index → module name.
    names: std.ArrayListUnmanaged([]const u8),
    /// Adjacency list: vertex index → indices of imported modules.
    /// edges[i] is the list of modules that module i imports.
    edges: std.ArrayListUnmanaged(std.ArrayListUnmanaged(u32)),

    pub fn init(alloc: std.mem.Allocator) ModuleGraph {
        return .{
            .alloc = alloc,
            .indices = .{},
            .names = .{},
            .edges = .{},
        };
    }

    pub fn deinit(self: *ModuleGraph) void {
        self.indices.deinit(self.alloc);
        self.names.deinit(self.alloc);
        for (self.edges.items) |*e| e.deinit(self.alloc);
        self.edges.deinit(self.alloc);
    }

    /// Add a module vertex if not already present.  Returns the vertex index.
    pub fn addModule(self: *ModuleGraph, name: []const u8) std.mem.Allocator.Error!u32 {
        if (self.indices.get(name)) |idx| return idx;
        const idx: u32 = @intCast(self.names.items.len);
        const owned = try self.alloc.dupe(u8, name);
        try self.names.append(self.alloc, owned);
        try self.edges.append(self.alloc, .{});
        try self.indices.put(self.alloc, owned, idx);
        return idx;
    }

    /// Record that module `from` imports module `to`.
    ///
    /// Both modules are added as vertices if not already present.
    pub fn addEdge(self: *ModuleGraph, from: []const u8, to: []const u8) std.mem.Allocator.Error!void {
        const from_idx = try self.addModule(from);
        const to_idx = try self.addModule(to);
        // Avoid duplicate edges.
        for (self.edges.items[from_idx].items) |existing| {
            if (existing == to_idx) return;
        }
        try self.edges.items[from_idx].append(self.alloc, to_idx);
    }

    /// Total number of vertices (modules) in the graph.
    pub fn len(self: *const ModuleGraph) usize {
        return self.names.items.len;
    }
};

// ── Topological sort (Kahn's algorithm) ─────────────────────────────────

/// The result of a topological sort.
pub const TopoResult = struct {
    /// Compilation order: dependencies first, dependents last.
    /// Each entry is a module name owned by the graph's allocator.
    order: []const []const u8,
    /// True iff the graph contains no cycles.
    /// When false, `order` is partial and `diags` contains the cycle errors.
    is_complete: bool,
};

/// Topologically sort `graph` using Kahn's algorithm.
///
/// Returns the full compilation order when the graph is acyclic.
/// When a cycle is detected, emits structured diagnostics via `diags`
/// (one per strongly-connected component that forms a cycle) and returns
/// a partial order for the acyclic portion.
///
/// `alloc` is used for the returned `order` slice (caller owns).
pub fn topoSort(
    graph: *const ModuleGraph,
    alloc: std.mem.Allocator,
    diags: *DiagnosticCollector,
) std.mem.Allocator.Error!TopoResult {
    const n = graph.names.items.len;
    if (n == 0) {
        return TopoResult{ .order = &.{}, .is_complete = true };
    }

    // ── Build reverse adjacency list ────────────────────────────────────
    //
    // edges[u] lists modules that u *imports* (u → v means "u depends on v").
    // For compilation order (dependencies first) we run Kahn's on the transposed
    // graph: edge v → u, meaning "v must be compiled before u".
    //
    // In the transposed graph:
    //   - in-degree[v] = number of modules that v imports (i.e. v's own deps).
    //   - Nodes with in-degree 0 have no dependencies → compile first.
    //   - When v is emitted, we decrement in-degree for each module that imports v.
    //
    // `rev[v]` = list of modules u such that u imports v (u ∈ edges[v] in original).
    const rev = try alloc.alloc(std.ArrayListUnmanaged(u32), n);
    defer {
        for (rev) |*r| r.deinit(alloc);
        alloc.free(rev);
    }
    @memset(rev, .{});

    // in_degree[u] = number of modules u imports = out-degree in original graph.
    const in_degree = try alloc.alloc(u32, n);
    defer alloc.free(in_degree);
    @memset(in_degree, 0);

    for (graph.edges.items, 0..) |adj, u| {
        in_degree[u] += @intCast(adj.items.len);
        for (adj.items) |v| {
            // Record that u imports v: in the transposed graph, v → u.
            try rev[v].append(alloc, @intCast(u));
        }
    }

    // ── Initialise queue with zero-dependency vertices ──────────────────
    var queue: std.ArrayListUnmanaged(u32) = .{};
    defer queue.deinit(alloc);
    for (in_degree, 0..) |deg, i| {
        if (deg == 0) try queue.append(alloc, @intCast(i));
    }

    // ── Kahn's main loop ────────────────────────────────────────────────
    var order: std.ArrayListUnmanaged([]const u8) = .{};
    errdefer order.deinit(alloc);

    while (queue.items.len > 0) {
        // Pop front (FIFO gives a deterministic BFS-style ordering).
        const u = queue.orderedRemove(0);
        try order.append(alloc, graph.names.items[u]);

        // u is compiled: unblock modules that import u.
        for (rev[u].items) |w| {
            in_degree[w] -= 1;
            if (in_degree[w] == 0) try queue.append(alloc, w);
        }
    }

    const is_complete = order.items.len == n;

    // ── Cycle detection via Tarjan's SCC (on residual graph) ────────────
    if (!is_complete) {
        // Find all SCCs with size > 1 (or self-loops) — these are the cycles.
        const sccs = try tarjanScc(graph, alloc);
        defer {
            for (sccs) |scc| alloc.free(scc);
            alloc.free(sccs);
        }

        // Use invalid spans for synthetic cycle diagnostics — no source
        // location is available since cycles span multiple files.
        const zero_span = SourceSpan.init(SourcePos.invalid(), SourcePos.invalid());

        for (sccs) |scc| {
            if (scc.len < 2) {
                // Check for self-loop.
                const v = scc[0];
                var has_self_loop = false;
                for (graph.edges.items[v].items) |to| {
                    if (to == v) { has_self_loop = true; break; }
                }
                if (!has_self_loop) continue;
            }

            // Build a human-readable cycle description.
            var msg_buf: std.ArrayListUnmanaged(u8) = .{};
            defer msg_buf.deinit(alloc);
            try msg_buf.appendSlice(alloc, "import cycle detected: ");
            for (scc, 0..) |v, i| {
                if (i > 0) try msg_buf.appendSlice(alloc, " → ");
                try msg_buf.appendSlice(alloc, graph.names.items[v]);
            }
            // Close the cycle.
            try msg_buf.appendSlice(alloc, " → ");
            try msg_buf.appendSlice(alloc, graph.names.items[scc[0]]);

            const msg = try alloc.dupe(u8, msg_buf.items);
            try diags.add(alloc, .{
                .severity = .@"error",
                .code = .import_cycle,
                .span = zero_span,
                .message = msg,
            });
        }
    }

    return TopoResult{
        .order = try order.toOwnedSlice(alloc),
        .is_complete = is_complete,
    };
}

// ── Tarjan's SCC algorithm ────────────────────────────────────────────────

/// Compute all strongly-connected components of `graph` using Tarjan's
/// algorithm.
///
/// Returns a slice of SCCs, each SCC being a slice of vertex indices.
/// SCCs are returned in reverse topological order (leaves first).
/// Caller owns all returned memory.
fn tarjanScc(graph: *const ModuleGraph, alloc: std.mem.Allocator) std.mem.Allocator.Error![][]u32 {
    const n = graph.names.items.len;

    var state = TarjanState{
        .alloc = alloc,
        .graph = graph,
        .index_counter = 0,
        .stack = .{},
        .on_stack = try alloc.alloc(bool, n),
        .indices = try alloc.alloc(i64, n),
        .lowlinks = try alloc.alloc(u32, n),
        .sccs = .{},
    };
    defer {
        state.stack.deinit(alloc);
        alloc.free(state.on_stack);
        alloc.free(state.indices);
        alloc.free(state.lowlinks);
    }
    @memset(state.indices, -1); // -1 = unvisited
    @memset(state.on_stack, false);

    for (0..n) |v| {
        if (state.indices[v] == -1) {
            try tarjanVisit(&state, @intCast(v));
        }
    }

    return state.sccs.toOwnedSlice(alloc);
}

const TarjanState = struct {
    alloc: std.mem.Allocator,
    graph: *const ModuleGraph,
    index_counter: u32,
    stack: std.ArrayListUnmanaged(u32),
    on_stack: []bool,
    indices: []i64, // -1 = unvisited
    lowlinks: []u32,
    sccs: std.ArrayListUnmanaged([]u32),
};

fn tarjanVisit(s: *TarjanState, v: u32) std.mem.Allocator.Error!void {
    s.indices[v] = s.index_counter;
    s.lowlinks[v] = s.index_counter;
    s.index_counter += 1;
    try s.stack.append(s.alloc, v);
    s.on_stack[v] = true;

    for (s.graph.edges.items[v].items) |w| {
        if (s.indices[w] == -1) {
            try tarjanVisit(s, w);
            s.lowlinks[v] = @min(s.lowlinks[v], s.lowlinks[w]);
        } else if (s.on_stack[w]) {
            s.lowlinks[v] = @min(s.lowlinks[v], @as(u32, @intCast(s.indices[w])));
        }
    }

    // Root of an SCC.
    if (s.lowlinks[v] == @as(u32, @intCast(s.indices[v]))) {
        var scc: std.ArrayListUnmanaged(u32) = .{};
        while (true) {
            const w = s.stack.pop().?;
            s.on_stack[w] = false;
            try scc.append(s.alloc, w);
            if (w == v) break;
        }
        try s.sccs.append(s.alloc, try scc.toOwnedSlice(s.alloc));
    }
}

// ── Module discovery ─────────────────────────────────────────────────────

/// A discovered module: its name and the path to its source file.
pub const DiscoveredModule = struct {
    /// Fully-qualified module name (e.g. `"Data.Map"`).
    module_name: []const u8,
    /// Absolute or relative path to the `.hs` source file.
    file_path: []const u8,
};

/// Scan a root `.hs` file and transitively discover all imported modules,
/// building the full `ModuleGraph`.
///
/// `root_path` is the path to the root module's source file.
/// `search_paths` is a list of directories to search for imported modules
/// (e.g. `&.{".", "lib/"}` — tried in order).
///
/// For each imported module name `Foo.Bar`, the resolver looks for
/// `Foo/Bar.hs` under each search path.  Modules not found on the search
/// path are recorded in the graph as external/unknown but do not trigger
/// a discovery error (they will fail at compile time when needed).
///
/// `alloc` is used for all allocations (expected arena).
/// The returned `ModuleGraph` and discovered module list are owned by `alloc`.
pub fn discoverModules(
    alloc: std.mem.Allocator,
    root_path: []const u8,
    search_paths: []const []const u8,
) std.mem.Allocator.Error!struct { graph: ModuleGraph, modules: []DiscoveredModule } {
    var graph = ModuleGraph.init(alloc);
    var discovered: std.ArrayListUnmanaged(DiscoveredModule) = .{};
    var visited_files: std.StringHashMapUnmanaged(void) = .{};
    defer visited_files.deinit(alloc);

    // Work-list: (module_name, file_path) pairs to process.
    var worklist: std.ArrayListUnmanaged(struct { name: []const u8, path: []const u8 }) = .{};
    defer worklist.deinit(alloc);

    const root_name = try inferModuleName(alloc, root_path);
    try worklist.append(alloc, .{ .name = root_name, .path = root_path });

    while (worklist.items.len > 0) {
        const item = worklist.orderedRemove(0);

        // Skip already-visited files.
        if (visited_files.contains(item.path)) continue;
        try visited_files.put(alloc, item.path, {});

        // Ensure the vertex exists.
        _ = try graph.addModule(item.name);
        try discovered.append(alloc, .{
            .module_name = item.name,
            .file_path = item.path,
        });

        // Header-parse to extract import declarations.
        const imports = parseImportHeaders(alloc, item.path) catch continue;

        for (imports) |imp_name| {
            // Add the dependency edge.
            try graph.addEdge(item.name, imp_name);

            // Try to locate the source file on the search path.
            if (try resolveModule(alloc, imp_name, search_paths)) |imp_path| {
                if (!visited_files.contains(imp_path)) {
                    try worklist.append(alloc, .{ .name = imp_name, .path = imp_path });
                }
            }
            // If not found, the vertex is still in the graph (as an external dep).
        }
    }

    return .{ .graph = graph, .modules = try discovered.toOwnedSlice(alloc) };
}

/// Parse only the import declarations from a `.hs` file, returning the list
/// of imported module names.  Does a full parse of the module header but
/// stops after imports (does not parse declarations).
///
/// Returns an empty slice on read or parse error (discovery is best-effort).
fn parseImportHeaders(alloc: std.mem.Allocator, file_path: []const u8) std.mem.Allocator.Error![]const []const u8 {
    // Read the source.
    const source = std.fs.cwd().readFileAlloc(alloc, file_path, 10 * 1024 * 1024) catch return &.{};
    defer alloc.free(source);

    var lexer = lexer_mod.Lexer.init(alloc, source, 0);
    var layout = layout_mod.LayoutProcessor.init(alloc, &lexer);
    var dummy_diags = diag_mod.DiagnosticCollector.init();
    defer dummy_diags.deinit(alloc);
    layout.setDiagnostics(&dummy_diags);

    var parser = parser_mod.Parser.init(alloc, &layout, &dummy_diags) catch return &.{};
    const module = parser.parseModule() catch return &.{};

    var names: std.ArrayListUnmanaged([]const u8) = .{};
    for (module.imports) |imp| {
        try names.append(alloc, try alloc.dupe(u8, imp.module_name));
    }
    return names.toOwnedSlice(alloc);
}

/// Infer the module name from a file path.
///
/// `Data/Map/Strict.hs` → `"Data.Map.Strict"`.
/// If the file has no directory component, returns the stem: `Main.hs` → `"Main"`.
pub fn inferModuleName(alloc: std.mem.Allocator, path: []const u8) std.mem.Allocator.Error![]const u8 {
    const base = std.fs.path.basename(path);
    const stem = if (std.mem.endsWith(u8, base, ".hs"))
        base[0 .. base.len - 3]
    else
        base;

    // Replace path separators with dots in the full path stem.
    const dir = std.fs.path.dirname(path) orelse return alloc.dupe(u8, stem);
    const full_stem = if (std.mem.endsWith(u8, path, ".hs"))
        path[0 .. path.len - 3]
    else
        path;
    _ = dir;

    // Normalise: replace `/` with `.`, strip leading `./`.
    var result = try alloc.dupe(u8, full_stem);
    if (std.mem.startsWith(u8, result, "./")) result = result[2..];
    for (result) |*c| {
        if (c.* == '/') c.* = '.';
    }
    return result;
}

/// Resolve a module name to a file path by searching `search_paths`.
///
/// `"Data.Map"` → looks for `Data/Map.hs` in each search path.
/// Returns `null` if not found.
fn resolveModule(
    alloc: std.mem.Allocator,
    module_name: []const u8,
    search_paths: []const []const u8,
) std.mem.Allocator.Error!?[]const u8 {
    // Convert "Data.Map" → "Data/Map.hs".
    const rel = try std.mem.replaceOwned(u8, alloc, module_name, ".", std.fs.path.sep_str);
    defer alloc.free(rel);
    const filename = try std.fmt.allocPrint(alloc, "{s}.hs", .{rel});
    defer alloc.free(filename);

    for (search_paths) |sp| {
        const full = try std.fs.path.join(alloc, &.{ sp, filename });
        defer alloc.free(full);

        std.fs.cwd().access(full, .{}) catch continue;
        return try alloc.dupe(u8, full);
    }
    return null;
}

// ── Tests ─────────────────────────────────────────────────────────────────

const testing = std.testing;

test "ModuleGraph: addModule is idempotent" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();

    const idx1 = try g.addModule("Main");
    const idx2 = try g.addModule("Main");
    try testing.expectEqual(idx1, idx2);
    try testing.expectEqual(@as(usize, 1), g.len());
}

test "ModuleGraph: addEdge creates vertices" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();

    try g.addEdge("Main", "Data.Map");
    try testing.expectEqual(@as(usize, 2), g.len());
    try testing.expect(g.indices.contains("Main"));
    try testing.expect(g.indices.contains("Data.Map"));
}

test "ModuleGraph: addEdge is idempotent" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();

    try g.addEdge("A", "B");
    try g.addEdge("A", "B");
    const a_idx = g.indices.get("A").?;
    try testing.expectEqual(@as(usize, 1), g.edges.items[a_idx].items.len);
}

// ── Topological sort tests ────────────────────────────────────────────────

test "topoSort: empty graph" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const result = try topoSort(&g, alloc, &diags);
    defer alloc.free(result.order);

    try testing.expectEqual(@as(usize, 0), result.order.len);
    try testing.expect(result.is_complete);
    try testing.expect(!diags.hasErrors());
}

test "topoSort: single module, no deps" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();
    _ = try g.addModule("Main");

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const result = try topoSort(&g, alloc, &diags);
    defer alloc.free(result.order);

    try testing.expectEqual(@as(usize, 1), result.order.len);
    try testing.expectEqualStrings("Main", result.order[0]);
    try testing.expect(result.is_complete);
}

test "topoSort: linear chain A → B → C compiles C, B, A" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // A imports B, B imports C.
    var g = ModuleGraph.init(alloc);
    defer g.deinit();
    try g.addEdge("A", "B");
    try g.addEdge("B", "C");

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const result = try topoSort(&g, alloc, &diags);
    defer alloc.free(result.order);

    try testing.expect(result.is_complete);
    try testing.expect(!diags.hasErrors());
    try testing.expectEqual(@as(usize, 3), result.order.len);

    // C must come before B, B before A.
    const pos = struct {
        fn of(order: []const []const u8, name: []const u8) usize {
            for (order, 0..) |n, i| if (std.mem.eql(u8, n, name)) return i;
            unreachable;
        }
    };
    try testing.expect(pos.of(result.order, "C") < pos.of(result.order, "B"));
    try testing.expect(pos.of(result.order, "B") < pos.of(result.order, "A"));
}

test "topoSort: diamond A → {B,C}, B → D, C → D — D compiles first" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();
    try g.addEdge("A", "B");
    try g.addEdge("A", "C");
    try g.addEdge("B", "D");
    try g.addEdge("C", "D");

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const result = try topoSort(&g, alloc, &diags);
    defer alloc.free(result.order);

    try testing.expect(result.is_complete);
    try testing.expect(!diags.hasErrors());
    try testing.expectEqual(@as(usize, 4), result.order.len);

    const pos = struct {
        fn of(order: []const []const u8, name: []const u8) usize {
            for (order, 0..) |n, i| if (std.mem.eql(u8, n, name)) return i;
            unreachable;
        }
    };
    // D before B and C; B and C before A.
    try testing.expect(pos.of(result.order, "D") < pos.of(result.order, "B"));
    try testing.expect(pos.of(result.order, "D") < pos.of(result.order, "C"));
    try testing.expect(pos.of(result.order, "B") < pos.of(result.order, "A"));
    try testing.expect(pos.of(result.order, "C") < pos.of(result.order, "A"));
}

test "topoSort: cycle A → B → A emits import_cycle diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();
    try g.addEdge("A", "B");
    try g.addEdge("B", "A");

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const result = try topoSort(&g, alloc, &diags);
    defer alloc.free(result.order);

    try testing.expect(!result.is_complete);
    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
    const d = diags.diagnostics.items[0];
    try testing.expectEqual(DiagnosticCode.import_cycle, d.code);
    try testing.expect(std.mem.indexOf(u8, d.message, "import cycle") != null);
}

test "topoSort: three-way cycle A → B → C → A" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();
    try g.addEdge("A", "B");
    try g.addEdge("B", "C");
    try g.addEdge("C", "A");

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const result = try topoSort(&g, alloc, &diags);
    defer alloc.free(result.order);

    try testing.expect(!result.is_complete);
    try testing.expect(diags.hasErrors());
}

test "topoSort: self-loop A → A emits import_cycle diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var g = ModuleGraph.init(alloc);
    defer g.deinit();
    try g.addEdge("A", "A");

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const result = try topoSort(&g, alloc, &diags);
    defer alloc.free(result.order);

    try testing.expect(!result.is_complete);
    try testing.expect(diags.hasErrors());
}

// ── inferModuleName tests ─────────────────────────────────────────────────

test "inferModuleName: simple file" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const name = try inferModuleName(alloc, "Main.hs");
    try testing.expectEqualStrings("Main", name);
}

test "inferModuleName: nested path" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const name = try inferModuleName(alloc, "Data/Map/Strict.hs");
    try testing.expectEqualStrings("Data.Map.Strict", name);
}

test "inferModuleName: relative path prefix stripped" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const name = try inferModuleName(alloc, "./Foo/Bar.hs");
    try testing.expectEqualStrings("Foo.Bar", name);
}

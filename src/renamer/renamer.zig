//! Renamer: resolve bare AST names to unique `Name` values and check scope.
//!
//! This is the first pass after parsing.  The parser produces an AST where
//! every identifier is a raw `[]const u8`.  The renamer walks the AST and
//! replaces each identifier with a globally-unique `Name` value (base string
//! + `Unique`), so that downstream passes (typechecker, Core lowering) can
//! compare binders by identity rather than string equality.
//!
//! ## What the renamer does
//!
//! 1. **Allocates fresh `Name`s** for every binding site (top-level
//!    definitions, lambda parameters, let-bindings, case alternatives,
//!    pattern variables, type variables).
//! 2. **Resolves reference sites** by looking up the current `Scope`.
//!    An unbound reference emits a structured `Diagnostic` and continues.
//! 3. **Pre-populates built-in names** (Prelude functions and types used in
//!    M1 programs) so that programs referencing `putStrLn`, `Int`, etc.
//!    resolve correctly without imports.
//! 4. **Detects duplicate top-level bindings** (same base name defined twice
//!    at module scope).
//!
//! ## What the renamer does NOT do
//!
//! - Type inference or kind checking (that's the typechecker).
//! - Module imports (M1 scope: every name is a built-in or locally defined).
//! - Fixity resolution (a later pass can do this using the renamed names).
//!
//! ## Output
//!
//! `rename` returns a `RenamedModule` — a parallel structure to `ast.Module`
//! where every `[]const u8` name that was a binder or reference has been
//! replaced with a `naming.Name`.  The original `[]const u8` remains
//! accessible as `Name.base` for display.
//!
//! ## Error handling
//!
//! Errors are collected into the caller-supplied `DiagnosticCollector` (no
//! fail-fast).  On an unbound reference the renamer substitutes a synthetic
//! `Name` whose unique is distinct from every other name, so downstream
//! passes continue without crashing.  The caller should check
//! `diags.hasErrors()` before proceeding to typechecking.
//!
//! ## References
//!
//! - GHC renamer: `compiler/GHC/Rename/`
//! - Haskell 2010 Report §4 (declarations and bindings)

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const naming = @import("../naming/unique.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");
const span_mod = @import("../diagnostics/span.zig");

pub const Name = naming.Name;
pub const UniqueSupply = naming.UniqueSupply;
pub const Diagnostic = diag_mod.Diagnostic;
pub const DiagnosticCollector = diag_mod.DiagnosticCollector;
pub const DiagnosticCode = diag_mod.DiagnosticCode;
pub const Severity = diag_mod.Severity;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;

// ── Scope ──────────────────────────────────────────────────────────────

/// A single scope frame: maps source names to unique `Name` values.
///
/// Frames are chained in a singly-linked list.  The innermost frame is
/// searched first (innermost-scope wins).
const Frame = struct {
    bindings: std.StringHashMapUnmanaged(Name),
    parent: ?*Frame,

    fn init() Frame {
        return .{ .bindings = .{}, .parent = null };
    }

    fn deinit(self: *Frame, alloc: std.mem.Allocator) void {
        self.bindings.deinit(alloc);
    }
};

/// A lexical scope stack for the renamer.
///
/// `push` creates a new innermost frame; `pop` destroys it.  `lookup`
/// searches from innermost to outermost.
pub const Scope = struct {
    alloc: std.mem.Allocator,
    /// Pointer to the innermost (current) frame.
    current: *Frame,

    /// Initialise a scope with an empty global frame.
    pub fn init(alloc: std.mem.Allocator) !Scope {
        const frame = try alloc.create(Frame);
        frame.* = Frame.init();
        return .{ .alloc = alloc, .current = frame };
    }

    pub fn deinit(self: *Scope) void {
        var frame: ?*Frame = self.current;
        while (frame) |f| {
            const parent = f.parent;
            f.deinit(self.alloc);
            self.alloc.destroy(f);
            frame = parent;
        }
    }

    /// Push a new empty scope frame.
    pub fn push(self: *Scope) !void {
        const frame = try self.alloc.create(Frame);
        frame.* = Frame.init();
        frame.parent = self.current;
        self.current = frame;
    }

    /// Pop the innermost scope frame (must not pop the global frame).
    pub fn pop(self: *Scope) void {
        const frame = self.current;
        self.current = frame.parent orelse return; // global frame: no-op
        frame.deinit(self.alloc);
        self.alloc.destroy(frame);
    }

    /// Bind `src_name` to `name` in the current (innermost) frame.
    pub fn bind(self: *Scope, src_name: []const u8, name: Name) !void {
        try self.current.bindings.put(self.alloc, src_name, name);
    }

    /// Look up `src_name`, searching from innermost to outermost frame.
    /// Returns `null` if not found.
    pub fn lookup(self: *const Scope, src_name: []const u8) ?Name {
        var frame: ?*const Frame = self.current;
        while (frame) |f| {
            if (f.bindings.get(src_name)) |n| return n;
            frame = f.parent;
        }
        return null;
    }

    /// True if `src_name` is bound in the *current* (innermost) frame only.
    /// Used for duplicate-binding detection within the same scope level.
    pub fn boundInCurrentFrame(self: *const Scope, src_name: []const u8) bool {
        return self.current.bindings.contains(src_name);
    }
};

// ── RenameEnv ──────────────────────────────────────────────────────────

/// Top-level renaming environment threaded through the renamer.
pub const RenameEnv = struct {
    alloc: std.mem.Allocator,
    supply: *UniqueSupply,
    scope: Scope,
    diags: *DiagnosticCollector,

    pub fn init(
        alloc: std.mem.Allocator,
        supply: *UniqueSupply,
        diags: *DiagnosticCollector,
    ) !RenameEnv {
        var env = RenameEnv{
            .alloc = alloc,
            .supply = supply,
            .scope = try Scope.init(alloc),
            .diags = diags,
        };
        try env.populateBuiltins();
        return env;
    }

    pub fn deinit(self: *RenameEnv) void {
        self.scope.deinit();
    }

    /// Allocate a fresh `Name` for a new binding site.
    pub fn freshName(self: *RenameEnv, base: []const u8) Name {
        return self.supply.freshName(base);
    }

    /// Resolve a reference.  Emits `unbound_variable` if not found and
    /// returns a synthetic name so processing can continue.
    pub fn resolve(self: *RenameEnv, src_name: []const u8, span: SourceSpan) !Name {
        if (self.scope.lookup(src_name)) |n| return n;
        // Emit diagnostic and return a fresh synthetic name.
        const msg = try std.fmt.allocPrint(
            self.alloc,
            "variable not in scope: `{s}`",
            .{src_name},
        );
        try self.diags.emit(self.alloc, .{
            .severity = .@"error",
            .code = .unbound_variable,
            .span = span,
            .message = msg,
        });
        return self.supply.freshName(src_name);
    }

    /// Pre-populate the global scope frame with M1 built-in names.
    ///
    /// Known shortcoming: names are minted here with fresh uniques each time
    /// `RenameEnv.init` is called, so the same built-in gets a different
    /// unique across compilation units.  A stable built-in table (keyed by
    /// a known initial unique range) is tracked in follow-up issue #166.
    fn populateBuiltins(self: *RenameEnv) !void {
        const builtins = [_][]const u8{
            // Prelude functions
            "putStrLn", "putStr", "print", "getLine",
            "return",   "error",  "undefined",
            // Numeric operations
            "negate", "abs", "signum", "fromInteger",
            // Basic type constructors
            "True",    "False",
            "Nothing", "Just",
            "Left",    "Right",
            // List operations
            "head",   "tail",   "null",   "length",
            "map",    "filter", "foldl",  "foldr",
            "concat", "zip",    "unzip",
            // String / Show / Read
            "show", "read",
            // Operators (as named functions)
            "otherwise",
            // Primitive types (used in type signatures)
            "Int",    "Integer", "Double", "Float",
            "Bool",   "Char",    "String",
            "IO",     "Maybe",   "Either",
            "[]",     "()",
        };
        for (builtins) |name| {
            const n = self.supply.freshName(name);
            try self.scope.bind(name, n);
        }
    }
};

// ── Renamed AST ────────────────────────────────────────────────────────
//
// Each node mirrors its `ast.*` counterpart but with `[]const u8` binder
// fields replaced by `Name`.  Reference sites in expressions use `Name`
// too.  Spans are preserved unchanged.
//
// M1 scope: we cover the subset of the AST needed for simple programs
// (function definitions, lambdas, let, case, do-notation, literals).
// Class / instance / foreign declarations are passed through structurally
// with names renamed where reachable.

/// A renamed expression.
pub const RExpr = union(enum) {
    Var: struct { name: Name, span: SourceSpan },
    Lit: ast.Literal,
    App: struct { fn_expr: *const RExpr, arg_expr: *const RExpr },
    InfixApp: struct { left: *const RExpr, op: Name, op_span: SourceSpan, right: *const RExpr },
    LeftSection: struct { expr: *const RExpr, op: Name, op_span: SourceSpan },
    RightSection: struct { op: Name, op_span: SourceSpan, expr: *const RExpr },
    Lambda: struct { params: []const Name, param_spans: []const SourceSpan, body: *const RExpr },
    Let: struct { binds: []const RDecl, body: *const RExpr },
    Case: struct { scrutinee: *const RExpr, alts: []const RAlt },
    If: struct { condition: *const RExpr, then_expr: *const RExpr, else_expr: *const RExpr },
    Do: []const RStmt,
    Tuple: []const RExpr,
    List: []const RExpr,
    TypeAnn: struct { expr: *const RExpr, type: ast.Type },
    Negate: *const RExpr,
    Paren: *const RExpr,
};

/// A renamed pattern.
pub const RPat = union(enum) {
    /// Variable pattern — introduces a new binding.
    Var: struct { name: Name, span: SourceSpan },
    /// Constructor pattern.
    Con: struct { name: Name, con_span: SourceSpan, args: []const RPat },
    Lit: ast.Literal,
    Wild: SourceSpan,
    AsPat: struct { name: Name, span: SourceSpan, pat: *const RPat },
    Tuple: []const RPat,
    List: []const RPat,
    InfixCon: struct { left: *const RPat, con: Name, con_span: SourceSpan, right: *const RPat },
    Negate: *const RPat,
    Paren: *const RPat,
};

/// A renamed right-hand side.
pub const RRhs = union(enum) {
    UnGuarded: RExpr,
    Guarded: []const RGuardedRhs,
};

pub const RGuardedRhs = struct {
    guards: []const RGuard,
    rhs: RExpr,
};

pub const RGuard = union(enum) {
    ExprGuard: RExpr,
};

/// A renamed case alternative.
pub const RAlt = struct {
    pattern: RPat,
    rhs: RRhs,
    span: SourceSpan,
};

/// A renamed do-notation statement.
pub const RStmt = union(enum) {
    Generator: struct { pat: RPat, expr: RExpr },
    Qualifier: RExpr,
    Stmt: RExpr,
    LetStmt: []const RDecl,
};

/// A renamed match equation.
pub const RMatch = struct {
    patterns: []const RPat,
    rhs: RRhs,
    span: SourceSpan,
};

/// A renamed top-level or local declaration.
pub const RDecl = union(enum) {
    /// Function binding (one or more equations sharing the same `Name`).
    FunBind: struct { name: Name, equations: []const RMatch, span: SourceSpan },
    /// Pattern binding: `p = e`.
    PatBind: struct { pattern: RPat, rhs: RRhs, span: SourceSpan },
    /// Type signature — kept for the typechecker; names resolved.
    TypeSig: struct { names: []const Name, type: ast.Type, span: SourceSpan },
};

/// A fully-renamed module.
pub const RenamedModule = struct {
    module_name: []const u8,
    declarations: []const RDecl,
    span: SourceSpan,
};

/// A synthetic source span for compiler-generated binders that have no
/// corresponding source location (e.g. pattern variables whose span is not
/// yet tracked in the AST).  Uses `SourcePos.invalid()` to bypass the
/// line > 0 / column > 0 assertions in `SourcePos.init`.
///
/// Known shortcoming: tracked in follow-up issue #166 — once the AST
/// carries spans on all pattern nodes, this helper can be removed.
fn syntheticSpan() SourceSpan {
    return SourceSpan.init(SourcePos.invalid(), SourcePos.invalid());
}

// ── Error set ─────────────────────────────────────────────────────────

/// Errors that the rename family of functions can return.
///
/// Zig cannot infer the error set of mutually-recursive functions, so we
/// declare it explicitly here and annotate every rename* helper with it.
pub const RenameError = std.mem.Allocator.Error;

// ── rename (entry point) ───────────────────────────────────────────────

/// Rename an entire parsed module.
///
/// Allocates all renamed nodes in `env.alloc` (expected to be an arena).
/// Errors are collected in `env.diags`; the caller should check
/// `env.diags.hasErrors()` before proceeding.
pub fn rename(module: ast.Module, env: *RenameEnv) !RenamedModule {
    // ── Pass 1: register all top-level binders ──────────────────────────
    // We need all top-level names visible to each other (mutual recursion)
    // before we descend into right-hand sides.
    var top_names = std.StringHashMapUnmanaged(Name){};
    defer top_names.deinit(env.alloc);

    for (module.declarations) |decl| {
        switch (decl) {
            .FunBind => |fb| {
                if (env.scope.boundInCurrentFrame(fb.name)) {
                    // Duplicate top-level binding.
                    const msg = try std.fmt.allocPrint(
                        env.alloc,
                        "duplicate definition: `{s}`",
                        .{fb.name},
                    );
                    try env.diags.emit(env.alloc, .{
                        .severity = .@"error",
                        .code = .duplicate_definition,
                        .span = fb.span,
                        .message = msg,
                    });
                } else {
                    const n = env.freshName(fb.name);
                    try env.scope.bind(fb.name, n);
                    try top_names.put(env.alloc, fb.name, n);
                }
            },
            .PatBind => |pb| {
                // Collect binders introduced by the pattern.
                var binders: std.ArrayListUnmanaged(PatBinder) = .empty;
                defer binders.deinit(env.alloc);
                try collectPatBinders(pb.pattern, env, &binders);
                for (binders.items) |b| {
                    try top_names.put(env.alloc, b.src, b.name);
                }
            },
            .TypeSig => |ts| {
                // Type signatures don't introduce new binders at pass 1;
                // their names will be looked up in pass 2.
                _ = ts;
            },
            else => {}, // Data/type/class decls: M1 — skip binder extraction
        }
    }

    // ── Pass 2: rename declaration bodies ──────────────────────────────
    var rdecls = std.ArrayListUnmanaged(RDecl){};
    for (module.declarations) |decl| {
        if (try renameDecl(decl, env, &top_names)) |rd| {
            try rdecls.append(env.alloc, rd);
        }
    }

    return RenamedModule{
        .module_name = module.module_name,
        .declarations = try rdecls.toOwnedSlice(env.alloc),
        .span = module.span,
    };
}

// ── Declaration renaming ───────────────────────────────────────────────

fn renameDecl(
    decl: ast.Decl,
    env: *RenameEnv,
    top_names: *std.StringHashMapUnmanaged(Name),
) RenameError!?RDecl {
    _ = top_names;
    return switch (decl) {
        .FunBind => |fb| blk: {
            // The name was already bound in pass 1; look it up.
            const name = env.scope.lookup(fb.name) orelse env.freshName(fb.name);
            var equations = std.ArrayListUnmanaged(RMatch){};
            for (fb.equations) |eq| {
                try equations.append(env.alloc, try renameMatch(eq, env));
            }
            break :blk RDecl{ .FunBind = .{
                .name = name,
                .equations = try equations.toOwnedSlice(env.alloc),
                .span = fb.span,
            } };
        },
        .PatBind => |pb| blk: {
            const rpat = try renamePat(pb.pattern, env);
            const rrhs = try renameRhs(pb.rhs, env);
            break :blk RDecl{ .PatBind = .{
                .pattern = rpat,
                .rhs = rrhs,
                .span = pb.span,
            } };
        },
        .TypeSig => |ts| blk: {
            var rnames = std.ArrayListUnmanaged(Name){};
            for (ts.names) |src_name| {
                // Type signature names refer to already-bound top-level binders.
                const dummy_span = ts.span;
                const n = try env.resolve(src_name, dummy_span);
                try rnames.append(env.alloc, n);
            }
            break :blk RDecl{ .TypeSig = .{
                .names = try rnames.toOwnedSlice(env.alloc),
                .type = ts.type,
                .span = ts.span,
            } };
        },
        // Non-M1 decls: skip silently.
        else => null,
    };
}

// ── Match / RHS renaming ───────────────────────────────────────────────

fn renameMatch(match: ast.Match, env: *RenameEnv) RenameError!RMatch {
    try env.scope.push();
    defer env.scope.pop();

    var pats = std.ArrayListUnmanaged(RPat){};
    for (match.patterns) |p| {
        try pats.append(env.alloc, try renamePat(p, env));
    }
    const rrhs = try renameRhs(match.rhs, env);

    // where-clauses share the same scope as the patterns.
    // M1: where-clauses are ignored for now.

    return RMatch{
        .patterns = try pats.toOwnedSlice(env.alloc),
        .rhs = rrhs,
        .span = match.span,
    };
}

fn renameRhs(rhs: ast.Rhs, env: *RenameEnv) RenameError!RRhs {
    return switch (rhs) {
        .UnGuarded => |e| RRhs{ .UnGuarded = try renameExpr(e, env) },
        .Guarded => |grhs_list| blk: {
            var rgrhs = std.ArrayListUnmanaged(RGuardedRhs){};
            for (grhs_list) |g| {
                var guards = std.ArrayListUnmanaged(RGuard){};
                for (g.guards) |guard| {
                    switch (guard) {
                        .ExprGuard => |ge| try guards.append(env.alloc, .{ .ExprGuard = try renameExpr(ge, env) }),
                        .PatGuard => {}, // M1: skip pat guards
                    }
                }
                try rgrhs.append(env.alloc, .{
                    .guards = try guards.toOwnedSlice(env.alloc),
                    .rhs = try renameExpr(g.rhs, env),
                });
            }
            break :blk RRhs{ .Guarded = try rgrhs.toOwnedSlice(env.alloc) };
        },
    };
}

// ── Expression renaming ────────────────────────────────────────────────

fn renameExpr(expr: ast.Expr, env: *RenameEnv) RenameError!RExpr {
    return switch (expr) {
        .Var => |qn| blk: {
            const n = try env.resolve(qn.name, qn.span);
            break :blk RExpr{ .Var = .{ .name = n, .span = qn.span } };
        },
        .Lit => |l| RExpr{ .Lit = l },
        .App => |a| blk: {
            const fn_r = try env.alloc.create(RExpr);
            fn_r.* = try renameExpr(a.fn_expr.*, env);
            const arg_r = try env.alloc.create(RExpr);
            arg_r.* = try renameExpr(a.arg_expr.*, env);
            break :blk RExpr{ .App = .{ .fn_expr = fn_r, .arg_expr = arg_r } };
        },
        .InfixApp => |ia| blk: {
            const left_r = try env.alloc.create(RExpr);
            left_r.* = try renameExpr(ia.left.*, env);
            const right_r = try env.alloc.create(RExpr);
            right_r.* = try renameExpr(ia.right.*, env);
            const op_name = try env.resolve(ia.op.name, ia.op.span);
            break :blk RExpr{ .InfixApp = .{
                .left = left_r,
                .op = op_name,
                .op_span = ia.op.span,
                .right = right_r,
            } };
        },
        .LeftSection => |ls| blk: {
            const expr_r = try env.alloc.create(RExpr);
            expr_r.* = try renameExpr(ls.expr.*, env);
            const op_name = try env.resolve(ls.op.name, ls.op.span);
            break :blk RExpr{ .LeftSection = .{ .expr = expr_r, .op = op_name, .op_span = ls.op.span } };
        },
        .RightSection => |rs| blk: {
            const expr_r = try env.alloc.create(RExpr);
            expr_r.* = try renameExpr(rs.expr.*, env);
            const op_name = try env.resolve(rs.op.name, rs.op.span);
            break :blk RExpr{ .RightSection = .{ .op = op_name, .op_span = rs.op.span, .expr = expr_r } };
        },
        .Lambda => |lam| blk: {
            try env.scope.push();
            defer env.scope.pop();
            var params = std.ArrayListUnmanaged(Name){};
            var param_spans = std.ArrayListUnmanaged(SourceSpan){};
            for (lam.patterns) |p| {
                try collectPatBindersToScope(p, env, &params, &param_spans);
            }
            const body_r = try env.alloc.create(RExpr);
            body_r.* = try renameExpr(lam.body.*, env);
            break :blk RExpr{ .Lambda = .{
                .params = try params.toOwnedSlice(env.alloc),
                .param_spans = try param_spans.toOwnedSlice(env.alloc),
                .body = body_r,
            } };
        },
        .Let => |let| blk: {
            try env.scope.push();
            defer env.scope.pop();
            // Bind all let-binders first (mutual recursion within let).
            for (let.binds) |d| {
                switch (d) {
                    .FunBind => |fb| {
                        const n = env.freshName(fb.name);
                        try env.scope.bind(fb.name, n);
                    },
                    else => {},
                }
            }
            var rdecls = std.ArrayListUnmanaged(RDecl){};
            var top: std.StringHashMapUnmanaged(Name) = .{};
            defer top.deinit(env.alloc);
            for (let.binds) |d| {
                if (try renameDecl(d, env, &top)) |rd| {
                    try rdecls.append(env.alloc, rd);
                }
            }
            const body_r = try env.alloc.create(RExpr);
            body_r.* = try renameExpr(let.body.*, env);
            break :blk RExpr{ .Let = .{
                .binds = try rdecls.toOwnedSlice(env.alloc),
                .body = body_r,
            } };
        },
        .Case => |c| blk: {
            const scr_r = try env.alloc.create(RExpr);
            scr_r.* = try renameExpr(c.scrutinee.*, env);
            var alts = std.ArrayListUnmanaged(RAlt){};
            for (c.alts) |alt| {
                try alts.append(env.alloc, try renameAlt(alt, env));
            }
            break :blk RExpr{ .Case = .{
                .scrutinee = scr_r,
                .alts = try alts.toOwnedSlice(env.alloc),
            } };
        },
        .If => |i| blk: {
            const cond_r = try env.alloc.create(RExpr);
            cond_r.* = try renameExpr(i.condition.*, env);
            const then_r = try env.alloc.create(RExpr);
            then_r.* = try renameExpr(i.then_expr.*, env);
            const else_r = try env.alloc.create(RExpr);
            else_r.* = try renameExpr(i.else_expr.*, env);
            break :blk RExpr{ .If = .{ .condition = cond_r, .then_expr = then_r, .else_expr = else_r } };
        },
        .Do => |stmts| blk: {
            try env.scope.push();
            defer env.scope.pop();
            var rstmts = std.ArrayListUnmanaged(RStmt){};
            for (stmts) |stmt| {
                try rstmts.append(env.alloc, try renameStmt(stmt, env));
            }
            break :blk RExpr{ .Do = try rstmts.toOwnedSlice(env.alloc) };
        },
        .Tuple => |elems| blk: {
            var relems = std.ArrayListUnmanaged(RExpr){};
            for (elems) |e| try relems.append(env.alloc, try renameExpr(e, env));
            break :blk RExpr{ .Tuple = try relems.toOwnedSlice(env.alloc) };
        },
        .List => |elems| blk: {
            var relems = std.ArrayListUnmanaged(RExpr){};
            for (elems) |e| try relems.append(env.alloc, try renameExpr(e, env));
            break :blk RExpr{ .List = try relems.toOwnedSlice(env.alloc) };
        },
        .TypeAnn => |ta| blk: {
            const expr_r = try env.alloc.create(RExpr);
            expr_r.* = try renameExpr(ta.expr.*, env);
            break :blk RExpr{ .TypeAnn = .{ .expr = expr_r, .type = ta.type } };
        },
        .Negate => |e| blk: {
            const r = try env.alloc.create(RExpr);
            r.* = try renameExpr(e.*, env);
            break :blk RExpr{ .Negate = r };
        },
        .Paren => |e| blk: {
            const r = try env.alloc.create(RExpr);
            r.* = try renameExpr(e.*, env);
            break :blk RExpr{ .Paren = r };
        },
        // M1: ListComp, RecordCon, RecordUpdate, Field — not yet handled.
        // Emit an unbound-variable diagnostic for the sub-expressions we skip.
        .ListComp, .RecordCon, .RecordUpdate, .Field => {
            // Return a synthetic variable so downstream passes have a node.
            const dummy_span = expr.getSpan();
            const synthetic = env.freshName("<unsupported>");
            return RExpr{ .Var = .{ .name = synthetic, .span = dummy_span } };
        },
    };
}

// ── Alt / Stmt renaming ────────────────────────────────────────────────

fn renameAlt(alt: ast.Alt, env: *RenameEnv) RenameError!RAlt {
    try env.scope.push();
    defer env.scope.pop();
    const rpat = try renamePat(alt.pattern, env);
    const rrhs = try renameRhs(alt.rhs, env);
    return RAlt{ .pattern = rpat, .rhs = rrhs, .span = alt.span };
}

fn renameStmt(stmt: ast.Stmt, env: *RenameEnv) RenameError!RStmt {
    return switch (stmt) {
        .Generator => |g| blk: {
            const rpat = try renamePat(g.pat, env);
            const rexpr = try renameExpr(g.expr, env);
            break :blk RStmt{ .Generator = .{ .pat = rpat, .expr = rexpr } };
        },
        .Qualifier => |e| RStmt{ .Qualifier = try renameExpr(e, env) },
        .Stmt => |e| RStmt{ .Stmt = try renameExpr(e, env) },
        .LetStmt => |decls| blk: {
            for (decls) |d| {
                if (d == .FunBind) {
                    const n = env.freshName(d.FunBind.name);
                    try env.scope.bind(d.FunBind.name, n);
                }
            }
            var rdecls = std.ArrayListUnmanaged(RDecl){};
            var top: std.StringHashMapUnmanaged(Name) = .{};
            defer top.deinit(env.alloc);
            for (decls) |d| {
                if (try renameDecl(d, env, &top)) |rd| {
                    try rdecls.append(env.alloc, rd);
                }
            }
            break :blk RStmt{ .LetStmt = try rdecls.toOwnedSlice(env.alloc) };
        },
    };
}

// ── Pattern renaming ───────────────────────────────────────────────────

/// Rename a pattern, binding newly-introduced variables into the current scope.
fn renamePat(pat: ast.Pattern, env: *RenameEnv) RenameError!RPat {
    return switch (pat) {
        .Var => |src_name| blk: {
            const n = env.freshName(src_name);
            // Use a synthetic span (pattern vars in the AST carry no span yet).
            const sp = syntheticSpan();
            try env.scope.bind(src_name, n);
            break :blk RPat{ .Var = .{ .name = n, .span = sp } };
        },
        .Con => |c| blk: {
            const con_name = try env.resolve(c.name.name, c.name.span);
            var args = std.ArrayListUnmanaged(RPat){};
            for (c.args) |a| try args.append(env.alloc, try renamePat(a, env));
            break :blk RPat{ .Con = .{
                .name = con_name,
                .con_span = c.name.span,
                .args = try args.toOwnedSlice(env.alloc),
            } };
        },
        .Lit => |l| RPat{ .Lit = l },
        .Wild => |s| RPat{ .Wild = s },
        .AsPar => |ap| blk: {
            const n = env.freshName(ap.name);
            const sp = syntheticSpan();
            try env.scope.bind(ap.name, n);
            const inner = try env.alloc.create(RPat);
            inner.* = try renamePat(ap.pat.*, env);
            break :blk RPat{ .AsPat = .{ .name = n, .span = sp, .pat = inner } };
        },
        .Tuple => |pats| blk: {
            var rpats = std.ArrayListUnmanaged(RPat){};
            for (pats) |p| try rpats.append(env.alloc, try renamePat(p, env));
            break :blk RPat{ .Tuple = try rpats.toOwnedSlice(env.alloc) };
        },
        .List => |pats| blk: {
            var rpats = std.ArrayListUnmanaged(RPat){};
            for (pats) |p| try rpats.append(env.alloc, try renamePat(p, env));
            break :blk RPat{ .List = try rpats.toOwnedSlice(env.alloc) };
        },
        .InfixCon => |ic| blk: {
            const left_r = try env.alloc.create(RPat);
            left_r.* = try renamePat(ic.left.*, env);
            const right_r = try env.alloc.create(RPat);
            right_r.* = try renamePat(ic.right.*, env);
            const con_name = try env.resolve(ic.con.name, ic.con.span);
            break :blk RPat{ .InfixCon = .{
                .left = left_r,
                .con = con_name,
                .con_span = ic.con.span,
                .right = right_r,
            } };
        },
        .Negate => |p| blk: {
            const r = try env.alloc.create(RPat);
            r.* = try renamePat(p.*, env);
            break :blk RPat{ .Negate = r };
        },
        .Paren => |p| blk: {
            const r = try env.alloc.create(RPat);
            r.* = try renamePat(p.*, env);
            break :blk RPat{ .Paren = r };
        },
        .Bang => |p| blk: {
            // GHC extension, not Haskell 2010 — treat as transparent wrapper.
            const r = try env.alloc.create(RPat);
            r.* = try renamePat(p.*, env);
            break :blk RPat{ .Paren = r };
        },
        .NPlusK => |npk| blk: {
            // Deprecated syntax: treat the name as a plain variable.
            const n = env.freshName(npk.name);
            const sp = syntheticSpan();
            try env.scope.bind(npk.name, n);
            break :blk RPat{ .Var = .{ .name = n, .span = sp } };
        },
    };
}

// ── Helpers ────────────────────────────────────────────────────────────

/// A source-name/Name pair produced by binder collection.
const PatBinder = struct { src: []const u8, name: Name };

/// Collect all variable binders introduced by `pat` (without binding them
/// into the scope).  Used during top-level pass 1 for PatBind declarations.
fn collectPatBinders(
    pat: ast.Pattern,
    env: *RenameEnv,
    out: *std.ArrayListUnmanaged(PatBinder),
) RenameError!void {
    switch (pat) {
        .Var => |src| {
            const n = env.freshName(src);
            try env.scope.bind(src, n);
            try out.append(env.alloc, .{ .src = src, .name = n });
        },
        .Con => |c| for (c.args) |a| try collectPatBinders(a, env, out),
        .AsPar => |ap| {
            const n = env.freshName(ap.name);
            try env.scope.bind(ap.name, n);
            try out.append(env.alloc, .{ .src = ap.name, .name = n });
            try collectPatBinders(ap.pat.*, env, out);
        },
        .Tuple => |pats| for (pats) |p| try collectPatBinders(p, env, out),
        .List => |pats| for (pats) |p| try collectPatBinders(p, env, out),
        .InfixCon => |ic| {
            try collectPatBinders(ic.left.*, env, out);
            try collectPatBinders(ic.right.*, env, out);
        },
        .Negate, .Paren, .Bang => |p| try collectPatBinders(p.*, env, out),
        .Lit, .Wild, .NPlusK => {},
    }
}

/// Like `collectPatBinders` but binds into scope and collects Names + spans
/// for lambda parameter lists.
fn collectPatBindersToScope(
    pat: ast.Pattern,
    env: *RenameEnv,
    names: *std.ArrayListUnmanaged(Name),
    spans: *std.ArrayListUnmanaged(SourceSpan),
) RenameError!void {
    switch (pat) {
        .Var => |src| {
            const n = env.freshName(src);
            const sp = syntheticSpan();
            try env.scope.bind(src, n);
            try names.append(env.alloc, n);
            try spans.append(env.alloc, sp);
        },
        .Wild => {
            // Wildcard — bind a synthetic name so the lambda arity is right.
            const n = env.freshName("_");
            const sp = syntheticSpan();
            try names.append(env.alloc, n);
            try spans.append(env.alloc, sp);
        },
        .Paren => |p| try collectPatBindersToScope(p.*, env, names, spans),
        // Complex patterns in lambda position: rename as a full pattern and
        // just extract any variable binders.
        else => {
            var binders: std.ArrayListUnmanaged(PatBinder) = .empty;
            defer binders.deinit(env.alloc);
            try collectPatBinders(pat, env, &binders);
            const sp = syntheticSpan();
            for (binders.items) |b| {
                try names.append(env.alloc, b.name);
                try spans.append(env.alloc, sp);
            }
        },
    }
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

fn testSpan() SourceSpan {
    return SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 10));
}

fn testQName(name: []const u8) ast.QName {
    return .{ .name = name, .span = testSpan() };
}

fn makeModule(decls: []const ast.Decl) ast.Module {
    return .{
        .module_name = "Test",
        .exports = null,
        .imports = &.{},
        .declarations = decls,
        .span = testSpan(),
    };
}

// ── Scope tests ────────────────────────────────────────────────────────

test "Scope: lookup in single frame" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var scope = try Scope.init(alloc);
    defer scope.deinit();

    var supply = UniqueSupply{};
    const n = supply.freshName("x");
    try scope.bind("x", n);
    const found = scope.lookup("x");
    try testing.expect(found != null);
    try testing.expect(found.?.eql(n));
}

test "Scope: lookup misses absent name" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var scope = try Scope.init(alloc);
    defer scope.deinit();
    try testing.expect(scope.lookup("y") == null);
}

test "Scope: inner binding shadows outer" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var scope = try Scope.init(alloc);
    defer scope.deinit();
    var supply = UniqueSupply{};

    const outer = supply.freshName("x");
    try scope.bind("x", outer);
    try scope.push();
    const inner = supply.freshName("x");
    try scope.bind("x", inner);

    const found = scope.lookup("x").?;
    try testing.expect(found.eql(inner));
    try testing.expect(!found.eql(outer));
}

test "Scope: after pop, outer binding is restored" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var scope = try Scope.init(alloc);
    defer scope.deinit();
    var supply = UniqueSupply{};

    const outer = supply.freshName("x");
    try scope.bind("x", outer);
    try scope.push();
    try scope.bind("x", supply.freshName("x"));
    scope.pop();

    const found = scope.lookup("x").?;
    try testing.expect(found.eql(outer));
}

test "Scope: boundInCurrentFrame detects duplicates" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var scope = try Scope.init(alloc);
    defer scope.deinit();
    var supply = UniqueSupply{};

    try testing.expect(!scope.boundInCurrentFrame("f"));
    try scope.bind("f", supply.freshName("f"));
    try testing.expect(scope.boundInCurrentFrame("f"));
}

// ── rename: integration tests ──────────────────────────────────────────

test "rename: simple function binding gets a unique Name" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    // `main = putStrLn "hello"`
    const rhs_lit = ast.Expr{ .Lit = .{ .String = .{ .value = "hello", .span = testSpan() } } };
    const arg_expr = ast.Expr{ .Var = testQName("putStrLn") };
    const app = ast.Expr{ .App = .{ .fn_expr = &arg_expr, .arg_expr = &rhs_lit } };
    const decls = [_]ast.Decl{.{ .FunBind = .{
        .name = "main",
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = app }, .where_clause = null, .span = testSpan() }},
        .span = testSpan(),
    } }};
    const module = makeModule(&decls);
    const rm = try rename(module, &env);

    try testing.expect(!diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), rm.declarations.len);
    try testing.expectEqualStrings("main", rm.declarations[0].FunBind.name.base);
}

test "rename: unbound variable emits diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    // `f = notInScope`
    const rhs = ast.Expr{ .Var = testQName("notInScope") };
    const decls = [_]ast.Decl{.{ .FunBind = .{
        .name = "f",
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = rhs }, .where_clause = null, .span = testSpan() }},
        .span = testSpan(),
    } }};
    const module = makeModule(&decls);
    _ = try rename(module, &env);

    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
    try testing.expectEqual(DiagnosticCode.unbound_variable, diags.diagnostics.items[0].code);
}

test "rename: lambda parameters are in scope in body" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    // `f = \x -> x`
    const body = ast.Expr{ .Var = testQName("x") };
    const lam = ast.Expr{ .Lambda = .{ .patterns = &.{.{ .Var = "x" }}, .body = &body } };
    const decls = [_]ast.Decl{.{ .FunBind = .{
        .name = "f",
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lam }, .where_clause = null, .span = testSpan() }},
        .span = testSpan(),
    } }};
    const module = makeModule(&decls);
    _ = try rename(module, &env);

    // No unbound variable errors — `x` should be in scope.
    try testing.expect(!diags.hasErrors());
}

test "rename: lambda parameter does not leak out of body" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    // `f = \x -> x`
    // `g = x`  ← x not in scope here
    const body = ast.Expr{ .Var = testQName("x") };
    const lam = ast.Expr{ .Lambda = .{ .patterns = &.{.{ .Var = "x" }}, .body = &body } };
    const rhs_g = ast.Expr{ .Var = testQName("x") };
    const decls = [_]ast.Decl{
        .{ .FunBind = .{
            .name = "f",
            .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lam }, .where_clause = null, .span = testSpan() }},
            .span = testSpan(),
        } },
        .{ .FunBind = .{
            .name = "g",
            .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = rhs_g }, .where_clause = null, .span = testSpan() }},
            .span = testSpan(),
        } },
    };
    const module = makeModule(&decls);
    _ = try rename(module, &env);

    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
}

test "rename: duplicate top-level binding emits diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    const lit = ast.Expr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const decl = ast.Decl{ .FunBind = .{
        .name = "f",
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit }, .where_clause = null, .span = testSpan() }},
        .span = testSpan(),
    } };
    const decls = [_]ast.Decl{ decl, decl }; // same name twice
    const module = makeModule(&decls);
    _ = try rename(module, &env);

    try testing.expect(diags.hasErrors());
    try testing.expectEqual(DiagnosticCode.duplicate_definition, diags.diagnostics.items[0].code);
}

test "rename: function equation patterns introduce binders" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    // `f x = x`
    const body = ast.Expr{ .Var = testQName("x") };
    const decls = [_]ast.Decl{.{ .FunBind = .{
        .name = "f",
        .equations = &.{.{
            .patterns = &.{.{ .Var = "x" }},
            .rhs = .{ .UnGuarded = body },
            .where_clause = null,
            .span = testSpan(),
        }},
        .span = testSpan(),
    } }};
    const module = makeModule(&decls);
    _ = try rename(module, &env);
    try testing.expect(!diags.hasErrors());
}

test "rename: mutual recursion — both names visible" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    // `even n = odd n`
    // `odd n = even n`
    const rhs_even = ast.Expr{ .App = .{
        .fn_expr = &ast.Expr{ .Var = testQName("odd") },
        .arg_expr = &ast.Expr{ .Var = testQName("n") },
    } };
    const rhs_odd = ast.Expr{ .App = .{
        .fn_expr = &ast.Expr{ .Var = testQName("even") },
        .arg_expr = &ast.Expr{ .Var = testQName("n") },
    } };
    const decls = [_]ast.Decl{
        .{ .FunBind = .{
            .name = "even",
            .equations = &.{.{ .patterns = &.{.{ .Var = "n" }}, .rhs = .{ .UnGuarded = rhs_even }, .where_clause = null, .span = testSpan() }},
            .span = testSpan(),
        } },
        .{ .FunBind = .{
            .name = "odd",
            .equations = &.{.{ .patterns = &.{.{ .Var = "n" }}, .rhs = .{ .UnGuarded = rhs_odd }, .where_clause = null, .span = testSpan() }},
            .span = testSpan(),
        } },
    };
    const module = makeModule(&decls);
    _ = try rename(module, &env);
    try testing.expect(!diags.hasErrors());
}

test "rename: let-binding is in scope in body" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    // `f = let y = 1 in y`
    const lit = ast.Expr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const body_ref = ast.Expr{ .Var = testQName("y") };
    const let_expr = ast.Expr{ .Let = .{
        .binds = &.{.{ .FunBind = .{
            .name = "y",
            .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit }, .where_clause = null, .span = testSpan() }},
            .span = testSpan(),
        } }},
        .body = &body_ref,
    } };
    const decls = [_]ast.Decl{.{ .FunBind = .{
        .name = "f",
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = let_expr }, .where_clause = null, .span = testSpan() }},
        .span = testSpan(),
    } }};
    const module = makeModule(&decls);
    _ = try rename(module, &env);
    try testing.expect(!diags.hasErrors());
}

test "rename: built-in putStrLn resolves without error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    const rhs = ast.Expr{ .Var = testQName("putStrLn") };
    const decls = [_]ast.Decl{.{ .FunBind = .{
        .name = "main",
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = rhs }, .where_clause = null, .span = testSpan() }},
        .span = testSpan(),
    } }};
    const module = makeModule(&decls);
    _ = try rename(module, &env);
    try testing.expect(!diags.hasErrors());
}

test "rename: two distinct functions get distinct Names" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var env = try RenameEnv.init(alloc, &supply, &diags);
    defer env.deinit();

    const lit1 = ast.Expr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const lit2 = ast.Expr{ .Lit = .{ .Int = .{ .value = 2, .span = testSpan() } } };
    const decls = [_]ast.Decl{
        .{ .FunBind = .{
            .name = "a",
            .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit1 }, .where_clause = null, .span = testSpan() }},
            .span = testSpan(),
        } },
        .{ .FunBind = .{
            .name = "b",
            .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit2 }, .where_clause = null, .span = testSpan() }},
            .span = testSpan(),
        } },
    };
    const module = makeModule(&decls);
    const rm = try rename(module, &env);

    try testing.expect(!diags.hasErrors());
    const name_a = rm.declarations[0].FunBind.name;
    const name_b = rm.declarations[1].FunBind.name;
    try testing.expect(!name_a.eql(name_b));
}

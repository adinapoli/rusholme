//! AST Pretty-Printer for Haskell source code.
//!
//! Renders the AST back to readable Haskell source. Output is deterministic
//! and suitable for golden test comparison. Where possible, the output is
//! valid Haskell (modulo comments, which are not preserved in the AST).
//!
//! Usage:
//!   const pp = PrettyPrinter.init(allocator);
//!   const source = try pp.printModule(module);
//!   defer allocator.free(source);

const std = @import("std");
const ast = @import("ast.zig");

/// Returns true when `current` is a function/pattern binding whose name
/// matches a type signature in `prev`. This is used to suppress the blank
/// line between a type signature and its implementation, mirroring how
/// Haskell source is conventionally formatted.
fn isBindingForPreviousSig(prev: ast.Decl, current: ast.Decl) bool {
    const sig_names = switch (prev) {
        .TypeSig => |ts| ts.names,
        else => return false,
    };
    const bind_name: []const u8 = switch (current) {
        .FunBind => |fb| fb.name,
        .PatBind => |pb| switch (pb.pattern) {
            .Var => |v| v.name,
            else => return false,
        },
        else => return false,
    };
    for (sig_names) |name| {
        if (std.mem.eql(u8, name, bind_name)) return true;
    }
    return false;
}

/// Pretty-printer for Haskell AST nodes.
///
/// Renders AST nodes to a string buffer using Zig's ArrayList writer.
/// All output is deterministic and suitable for golden tests.
pub const PrettyPrinter = struct {
    allocator: std.mem.Allocator,
    indent_level: u32 = 0,
    buf: std.ArrayListUnmanaged(u8) = .empty,

    const INDENT_WIDTH = 2;

    pub fn init(allocator: std.mem.Allocator) PrettyPrinter {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *PrettyPrinter) void {
        self.buf.deinit(self.allocator);
    }

    /// Return the accumulated output and reset the buffer.
    /// Caller owns the returned slice.
    pub fn toOwnedSlice(self: *PrettyPrinter) ![]u8 {
        return self.buf.toOwnedSlice(self.allocator);
    }

    // ── Writing helpers ────────────────────────────────────────────────

    const Error = std.mem.Allocator.Error;

    fn write(self: *PrettyPrinter, bytes: []const u8) Error!void {
        try self.buf.appendSlice(self.allocator, bytes);
    }

    fn writeByte(self: *PrettyPrinter, byte: u8) Error!void {
        try self.buf.append(self.allocator, byte);
    }

    fn writeIndent(self: *PrettyPrinter) Error!void {
        const spaces = self.indent_level * INDENT_WIDTH;
        for (0..spaces) |_| {
            try self.writeByte(' ');
        }
    }

    fn newline(self: *PrettyPrinter) Error!void {
        try self.writeByte('\n');
    }

    fn indent(self: *PrettyPrinter) void {
        self.indent_level += 1;
    }

    fn dedent(self: *PrettyPrinter) void {
        self.indent_level -= 1;
    }

    // ── Module ─────────────────────────────────────────────────────────

    pub fn printModule(self: *PrettyPrinter, mod: ast.Module) ![]u8 {
        try self.write("module ");
        try self.write(mod.module_name);

        if (mod.exports) |exports| {
            try self.write(" (");
            for (exports, 0..) |exp, i| {
                if (i > 0) try self.write(", ");
                try self.printExportSpec(exp);
            }
            try self.write(")");
        }

        try self.write(" where");
        try self.newline();

        for (mod.imports) |imp| {
            try self.newline();
            try self.printImportDecl(imp);
        }

        if (mod.imports.len > 0 and mod.declarations.len > 0) {
            try self.newline();
        }

        for (mod.declarations, 0..) |decl, i| {
            // Separate declarations with a blank line, except when a type
            // signature is immediately followed by its binding.
            if (i > 0 and !isBindingForPreviousSig(mod.declarations[i - 1], decl)) {
                try self.newline();
            }
            try self.newline();
            try self.printDecl(decl);
        }
        if (mod.declarations.len > 0) {
            try self.newline();
        }

        return self.toOwnedSlice();
    }

    // ── Exports ────────────────────────────────────────────────────────

    fn printExportSpec(self: *PrettyPrinter, spec: ast.ExportSpec) Error!void {
        switch (spec) {
            .Var => |name| try self.write(name),
            .Con => |name| try self.write(name),
            .Type => |ts| {
                try self.write(ts.name);
                if (ts.with_constructors) {
                    try self.write("(..)");
                }
            },
            .Module => |name| {
                try self.write("module ");
                try self.write(name);
            },
        }
    }

    // ── Imports ────────────────────────────────────────────────────────

    fn printImportDecl(self: *PrettyPrinter, imp: ast.ImportDecl) Error!void {
        try self.write("import ");
        if (imp.qualified) {
            try self.write("qualified ");
        }
        try self.write(imp.module_name);
        if (imp.as_alias) |alias| {
            try self.write(" as ");
            try self.write(alias);
        }
        if (imp.specs) |specs| {
            if (specs.hiding) {
                try self.write(" hiding");
            }
            try self.write(" (");
            for (specs.items, 0..) |item, i| {
                if (i > 0) try self.write(", ");
                try self.printImportSpec(item);
            }
            try self.write(")");
        }
        try self.newline();
    }

    fn printImportSpec(self: *PrettyPrinter, spec: ast.ImportSpec) Error!void {
        switch (spec) {
            .Var => |name| try self.write(name),
            .Con => |name| try self.write(name),
            .TyCon => |name| try self.write(name),
            .Class => |name| try self.write(name),
        }
    }

    // ── Declarations ───────────────────────────────────────────────────

    fn printDecl(self: *PrettyPrinter, decl: ast.Decl) Error!void {
        switch (decl) {
            .TypeSig => |ts| try self.printTypeSig(ts),
            .FunBind => |fb| try self.printFunBinding(fb),
            .PatBind => |pb| try self.printPatBinding(pb),
            .Type => |td| try self.printTypeDecl(td),
            .Data => |dd| try self.printDataDecl(dd),
            .Newtype => |nd| try self.printNewtypeDecl(nd),
            .Class => |cd| try self.printClassDecl(cd),
            .Instance => |id_| try self.printInstanceDecl(id_),
            .Default => |dd| try self.printDefaultDecl(dd),
            .Deriving => |dd| try self.printDerivingDecl(dd),
            .Foreign => |fd| try self.printForeignDecl(fd),
        }
    }

    fn printTypeSig(self: *PrettyPrinter, ts: ast.TypeSigDecl) Error!void {
        try self.writeIndent();
        for (ts.names, 0..) |name, i| {
            if (i > 0) try self.write(", ");
            try self.write(name);
        }
        try self.write(" :: ");
        try self.printType(ts.type);
    }

    fn printFunBinding(self: *PrettyPrinter, fb: ast.FunBinding) Error!void {
        for (fb.equations) |eq| {
            try self.writeIndent();
            try self.write(fb.name);
            for (eq.patterns) |*pat| {
                try self.writeByte(' ');
                try self.printPattern(pat);
            }
            try self.printRhs(eq.rhs);
            if (eq.where_clause) |wc| {
                try self.printWhereClause(wc);
            }
            try self.newline();
        }
    }

    fn printPatBinding(self: *PrettyPrinter, pb: ast.PatBinding) Error!void {
        try self.writeIndent();
        try self.printPattern(&pb.pattern);
        try self.printRhs(pb.rhs);
        if (pb.where_clause) |wc| {
            try self.printWhereClause(wc);
        }
    }

    fn printTypeDecl(self: *PrettyPrinter, td: ast.TypeDecl) Error!void {
        try self.writeIndent();
        try self.write("type ");
        try self.write(td.name);
        for (td.tyvars) |tv| {
            try self.writeByte(' ');
            try self.write(tv);
        }
        try self.write(" = ");
        try self.printType(td.type);
    }

    fn printDataDecl(self: *PrettyPrinter, dd: ast.DataDecl) Error!void {
        try self.writeIndent();
        try self.write("data ");
        try self.write(dd.name);
        for (dd.tyvars) |tv| {
            try self.writeByte(' ');
            try self.write(tv);
        }
        if (dd.constructors.len > 0) {
            try self.newline();
            self.indent();
            for (dd.constructors, 0..) |con, i| {
                try self.writeIndent();
                if (i == 0) {
                    try self.write("= ");
                } else {
                    try self.write("| ");
                }
                try self.printConDecl(con);
                try self.newline();
            }
            self.dedent();
        }
        if (dd.deriving.len > 0) {
            try self.writeIndent();
            try self.write("  deriving (");
            for (dd.deriving, 0..) |cls, i| {
                if (i > 0) try self.write(", ");
                try self.write(cls);
            }
            try self.write(")");
        }
    }

    fn printConDecl(self: *PrettyPrinter, con: ast.ConDecl) Error!void {
        try self.write(con.name);
        if (con.fields.len == 0) return;

        // Check if all fields are Record type - if so, print as a single record block
        const all_records = for (con.fields) |field| {
            if (field != .Record) break false;
        } else true;

        if (all_records) {
            try self.write(" { ");
            for (con.fields, 0..) |field, i| {
                if (i > 0) try self.write(", ");
                switch (field) {
                    .Record => |r| {
                        try self.write(r.name);
                        try self.write(" :: ");
                        try self.printType(r.type);
                    },
                    .Plain => unreachable, // Already checked all_records
                }
            }
            try self.write(" }");
        } else {
            // Regular constructor: print fields with spaces
            for (con.fields) |field| {
                try self.writeByte(' ');
                try self.printFieldDecl(field);
            }
        }
    }

    fn printFieldDecl(self: *PrettyPrinter, field: ast.FieldDecl) Error!void {
        switch (field) {
            .Plain => |ty| try self.printTypeAtom(ty),
            .Record => |r| {
                try self.write("{ ");
                try self.write(r.name);
                try self.write(" :: ");
                try self.printType(r.type);
                try self.write(" }");
            },
        }
    }

    fn printNewtypeDecl(self: *PrettyPrinter, nd: ast.NewtypeDecl) Error!void {
        try self.writeIndent();
        try self.write("newtype ");
        try self.write(nd.name);
        for (nd.tyvars) |tv| {
            try self.writeByte(' ');
            try self.write(tv);
        }
        try self.write(" = ");
        try self.printConDecl(nd.constructor);
        if (nd.deriving.len > 0) {
            try self.newline();
            try self.writeIndent();
            try self.write("  deriving (");
            for (nd.deriving, 0..) |cls, i| {
                if (i > 0) try self.write(", ");
                try self.write(cls);
            }
            try self.write(")");
        }
    }

    fn printClassDecl(self: *PrettyPrinter, cd: ast.ClassDecl) Error!void {
        try self.writeIndent();
        try self.write("class ");
        if (cd.context) |ctx| {
            try self.printContext(ctx);
            try self.write(" => ");
        }
        try self.write(cd.class_name);
        for (cd.tyvars) |tv| {
            try self.writeByte(' ');
            try self.write(tv);
        }
        if (cd.methods.len > 0) {
            try self.write(" where");
            try self.newline();
            self.indent();
            for (cd.methods) |method| {
                try self.writeIndent();
                try self.write(method.name);
                try self.write(" :: ");
                try self.printType(method.type);
                try self.newline();
                if (method.default_implementation) |impl| {
                    try self.writeIndent();
                    try self.write(method.name);
                    for (impl.patterns) |*pat| {
                        try self.writeByte(' ');
                        try self.printPattern(pat);
                    }
                    try self.printRhs(impl.rhs);
                    try self.newline();
                }
            }
            self.dedent();
        }
    }

    fn printInstanceDecl(self: *PrettyPrinter, inst: ast.InstanceDecl) Error!void {
        try self.writeIndent();
        try self.write("instance ");
        if (inst.context) |ctx| {
            try self.printContext(ctx);
            try self.write(" => ");
        }
        try self.printType(inst.constructor_type);
        if (inst.bindings.len > 0) {
            try self.write(" where");
            try self.newline();
            self.indent();
            for (inst.bindings) |binding| {
                try self.printFunBinding(binding);
            }
            self.dedent();
        }
    }

    fn printDefaultDecl(self: *PrettyPrinter, dd: ast.DefaultDecl) Error!void {
        try self.writeIndent();
        try self.write("default (");
        for (dd.types, 0..) |ty, i| {
            if (i > 0) try self.write(", ");
            try self.printType(ty);
        }
        try self.write(")");
    }

    fn printDerivingDecl(self: *PrettyPrinter, dd: ast.DerivingDecl) Error!void {
        try self.writeIndent();
        if (dd.standalone) {
            try self.write("deriving ");
            if (dd.deriving_strategy) |strat| {
                switch (strat) {
                    .Stock => try self.write("stock "),
                    .Newtype => try self.write("newtype "),
                    .Anyclass => try self.write("anyclass "),
                }
            }
            try self.write("instance ");
            try self.printType(dd.type);
        } else {
            try self.write("deriving (");
            for (dd.classes, 0..) |cls, i| {
                if (i > 0) try self.write(", ");
                try self.write(cls);
            }
            try self.write(")");
        }
    }

    fn printForeignDecl(self: *PrettyPrinter, fd: ast.ForeignDecl) Error!void {
        try self.writeIndent();
        try self.write("foreign import ");
        try self.write(fd.calling_convention);
        try self.writeByte(' ');
        try self.write(fd.name);
        try self.write(" :: ");
        try self.printType(fd.type);
    }

    // ── Context ────────────────────────────────────────────────────────

    fn printContext(self: *PrettyPrinter, ctx: ast.Context) Error!void {
        if (ctx.constraints.len == 1) {
            try self.printAssertion(ctx.constraints[0]);
        } else {
            try self.write("(");
            for (ctx.constraints, 0..) |constraint, i| {
                if (i > 0) try self.write(", ");
                try self.printAssertion(constraint);
            }
            try self.write(")");
        }
    }

    fn printAssertion(self: *PrettyPrinter, assertion: ast.Assertion) Error!void {
        try self.write(assertion.class_name);
        for (assertion.types) |ty| {
            try self.writeByte(' ');
            try self.printTypeAtom(ty);
        }
    }

    // ── Right-hand side & where ────────────────────────────────────────

    /// Print an RHS separator: '=' for function bindings, '->' for case alternatives
    const RhsSeparator = enum { equals, arrow };

    fn printRhs(self: *PrettyPrinter, rhs: ast.Rhs) Error!void {
        try self.printRhsWithSep(rhs, .equals);
    }

    fn printRhsWithSep(self: *PrettyPrinter, rhs: ast.Rhs, sep: RhsSeparator) Error!void {
        const sep_str = if (sep == .equals) " = " else " -> ";
        switch (rhs) {
            .UnGuarded => |expr| {
                try self.write(sep_str);
                try self.printExpr(expr);
            },
            .Guarded => |guards| {
                try self.newline();
                self.indent();
                for (guards) |grhs| {
                    try self.writeIndent();
                    try self.write("| ");
                    for (grhs.guards, 0..) |guard, i| {
                        if (i > 0) try self.write(", ");
                        try self.printGuard(guard);
                    }
                    try self.write(sep_str);
                    try self.printExpr(grhs.rhs);
                    try self.newline();
                }
                self.dedent();
            },
        }
    }

    fn printGuard(self: *PrettyPrinter, guard: ast.Guard) Error!void {
        switch (guard) {
            .PatGuard => |pats| {
                for (pats, 0..) |*pat, i| {
                    if (i > 0) try self.write(", ");
                    try self.printPattern(pat);
                }
            },
            .ExprGuard => |expr| try self.printExpr(expr),
        }
    }

    fn printWhereClause(self: *PrettyPrinter, decls: []const ast.Decl) Error!void {
        try self.newline();
        self.indent();
        try self.writeIndent();
        try self.write("where");
        try self.newline();
        self.indent();
        for (decls) |decl| {
            try self.printDecl(decl);
            try self.newline();
        }
        self.dedent();
        self.dedent();
    }

    // ── Expressions ────────────────────────────────────────────────────

    pub fn printExpr(self: *PrettyPrinter, expr: ast.Expr) Error!void {
        switch (expr) {
            .Var => |qname| try self.printQName(qname),
            .Lit => |lit| try self.printLiteral(lit),
            .App => |app| {
                try self.printExpr(app.fn_expr.*);
                try self.writeByte(' ');
                try self.printExprAtom(app.arg_expr.*);
            },
            .InfixApp => |infix| {
                try self.printExpr(infix.left.*);
                try self.writeByte(' ');
                try self.printQName(infix.op);
                try self.writeByte(' ');
                try self.printExpr(infix.right.*);
            },
            .LeftSection => |sec| {
                try self.write("(");
                try self.printExpr(sec.expr.*);
                try self.writeByte(' ');
                try self.printQName(sec.op);
                try self.write(")");
            },
            .RightSection => |sec| {
                try self.write("(");
                try self.printQName(sec.op);
                try self.writeByte(' ');
                try self.printExpr(sec.expr.*);
                try self.write(")");
            },
            .Lambda => |lam| {
                try self.write("\\");
                for (lam.patterns, 0..) |*pat, i| {
                    if (i > 0) try self.writeByte(' ');
                    try self.printPattern(pat);
                }
                try self.write(" -> ");
                try self.printExpr(lam.body.*);
            },
            .Let => |let_| {
                try self.write("let ");
                self.indent();
                for (let_.binds, 0..) |decl, i| {
                    if (i > 0) {
                        try self.newline();
                        try self.writeIndent();
                    }
                    try self.printDecl(decl);
                }
                self.dedent();
                try self.write(" in ");
                try self.printExpr(let_.body.*);
            },
            .Case => |case_| {
                try self.write("case ");
                try self.printExpr(case_.scrutinee.*);
                try self.write(" of");
                try self.newline();
                self.indent();
                for (case_.alts) |alt_| {
                    try self.writeIndent();
                    try self.printAlt(alt_);
                    try self.newline();
                }
                self.dedent();
            },
            .If => |if_| {
                try self.write("if ");
                try self.printExpr(if_.condition.*);
                try self.write(" then ");
                try self.printExpr(if_.then_expr.*);
                try self.write(" else ");
                try self.printExpr(if_.else_expr.*);
            },
            .Do => |stmts| {
                try self.write("do");
                try self.newline();
                self.indent();
                for (stmts) |stmt| {
                    try self.writeIndent();
                    try self.printStmt(stmt);
                    try self.newline();
                }
                self.dedent();
            },
            .Tuple => |exprs| {
                try self.write("(");
                for (exprs, 0..) |e, i| {
                    if (i > 0) try self.write(", ");
                    try self.printExpr(e);
                }
                try self.write(")");
            },
            .List => |exprs| {
                try self.write("[");
                for (exprs, 0..) |e, i| {
                    if (i > 0) try self.write(", ");
                    try self.printExpr(e);
                }
                try self.write("]");
            },
            .EnumFrom => |e| {
                try self.write("[");
                try self.printExpr(e.from.*);
                try self.write(" ..]");
            },
            .EnumFromThen => |e| {
                try self.write("[");
                try self.printExpr(e.from.*);
                try self.write(", ");
                try self.printExpr(e.then.*);
                try self.write(" ..]");
            },
            .EnumFromTo => |e| {
                try self.write("[");
                try self.printExpr(e.from.*);
                try self.write(" .. ");
                try self.printExpr(e.to.*);
                try self.write("]");
            },
            .EnumFromThenTo => |e| {
                try self.write("[");
                try self.printExpr(e.from.*);
                try self.write(", ");
                try self.printExpr(e.then.*);
                try self.write(" .. ");
                try self.printExpr(e.to.*);
                try self.write("]");
            },
            .ListComp => |lc| {
                try self.write("[");
                try self.printExpr(lc.expr.*);
                try self.write(" | ");
                for (lc.qualifiers, 0..) |qual, i| {
                    if (i > 0) try self.write(", ");
                    try self.printQualifier(qual);
                }
                try self.write("]");
            },
            .TypeAnn => |ann| {
                try self.printExpr(ann.expr.*);
                try self.write(" :: ");
                try self.printType(ann.type);
            },
            .Negate => |inner| {
                try self.write("-");
                try self.printExprAtom(inner.*);
            },
            .Paren => |inner| {
                try self.write("(");
                try self.printExpr(inner.*);
                try self.write(")");
            },
            .RecordCon => |rc| {
                try self.printQName(rc.con);
                try self.write(" { ");
                for (rc.fields, 0..) |field, i| {
                    if (i > 0) try self.write(", ");
                    try self.printFieldUpdate(field);
                }
                try self.write(" }");
            },
            .RecordUpdate => |ru| {
                try self.printExpr(ru.expr.*);
                try self.write(" { ");
                for (ru.fields, 0..) |field, i| {
                    if (i > 0) try self.write(", ");
                    try self.printFieldUpdate(field);
                }
                try self.write(" }");
            },
            .Field => |f| {
                try self.printExpr(f.expr.*);
                try self.write(".");
                try self.write(f.field_name);
            },
        }
    }

    /// Print an expression that is in "atom" position (argument to function
    /// application). Wraps compound expressions in parens.
    fn printExprAtom(self: *PrettyPrinter, expr: ast.Expr) Error!void {
        switch (expr) {
            .Var, .Lit, .Tuple, .List, .EnumFrom, .EnumFromThen, .EnumFromTo, .EnumFromThenTo, .Paren, .RecordCon => try self.printExpr(expr),
            else => {
                try self.write("(");
                try self.printExpr(expr);
                try self.write(")");
            },
        }
    }

    fn printFieldUpdate(self: *PrettyPrinter, field: ast.FieldUpdate) Error!void {
        try self.write(field.field_name);
        try self.write(" = ");
        try self.printExpr(field.expr);
    }

    fn printAlt(self: *PrettyPrinter, alt_: ast.Alt) Error!void {
        try self.printPattern(&alt_.pattern);
        try self.printRhsWithSep(alt_.rhs, .arrow);
        if (alt_.where_clause) |wc| {
            try self.printWhereClause(wc);
        }
    }

    fn printStmt(self: *PrettyPrinter, stmt: ast.Stmt) Error!void {
        switch (stmt) {
            .Generator => |*gen| {
                try self.printPattern(&gen.pat);
                try self.write(" <- ");
                try self.printExpr(gen.expr);
            },
            .Qualifier => |expr| try self.printExpr(expr),
            .Stmt => |expr| try self.printExpr(expr),
            .LetStmt => |decls| {
                try self.write("let ");
                self.indent();
                for (decls, 0..) |decl, i| {
                    if (i > 0) {
                        try self.newline();
                        try self.writeIndent();
                    }
                    try self.printDecl(decl);
                }
                self.dedent();
            },
        }
    }

    fn printQualifier(self: *PrettyPrinter, qual: ast.Qualifier) Error!void {
        switch (qual) {
            .Generator => |*gen| {
                try self.printPattern(&gen.pat);
                try self.write(" <- ");
                try self.printExpr(gen.expr);
            },
            .Qualifier => |expr| try self.printExpr(expr),
        }
    }

    // ── Patterns ───────────────────────────────────────────────────────

    pub fn printPattern(self: *PrettyPrinter, pat: *const ast.Pattern) Error!void {
        switch (pat.*) {
            .Var => |v| try self.write(v.name),
            .Con => |con| {
                try self.printQName(con.name);
                for (con.args) |*arg| {
                    try self.writeByte(' ');
                    try self.printPatternAtom(arg);
                }
            },
            .Lit => |lit| try self.printLiteral(lit),
            .Wild => try self.write("_"),
            .AsPar => |as_| {
                try self.write(as_.name);
                try self.write("@");
                try self.printPatternAtom(as_.pat);
            },
            .Tuple => |t| {
                try self.write("(");
                for (t.patterns, 0..) |*p, i| {
                    if (i > 0) try self.write(", ");
                    try self.printPattern(p);
                }
                try self.write(")");
            },
            .List => |l| {
                try self.write("[");
                for (l.patterns, 0..) |*p, i| {
                    if (i > 0) try self.write(", ");
                    try self.printPattern(p);
                }
                try self.write("]");
            },
            .InfixCon => |infix| {
                try self.printPattern(infix.left);
                try self.writeByte(' ');
                try self.printQName(infix.con);
                try self.writeByte(' ');
                try self.printPattern(infix.right);
            },
            .Negate => |n| {
                try self.write("-");
                try self.printPatternAtom(n.pat);
            },
            .Paren => |p| {
                try self.write("(");
                try self.printPattern(p.pat);
                try self.write(")");
            },
            .Bang => |b| {
                try self.write("!");
                try self.printPatternAtom(b.pat);
            },
            .NPlusK => |npk| {
                try self.write(npk.name);
                try self.write("+");
                var int_buf: [20]u8 = undefined;
                const int_str = std.fmt.bufPrint(&int_buf, "{d}", .{npk.k}) catch unreachable;
                try self.write(int_str);
            },
            .RecPat => |rp| {
                try self.printQName(rp.con);
                try self.write(" {");
                for (rp.fields, 0..) |f, i| {
                    if (i > 0) try self.write(", ");
                    try self.write(f.field_name);
                    if (f.pat) |p| {
                        try self.write(" = ");
                        try self.printPatternAtom(&p);
                    }
                }
                try self.write("}");
            },
        }
    }

    /// Print a pattern in atom position — wraps constructor patterns in parens.
    fn printPatternAtom(self: *PrettyPrinter, pat: *const ast.Pattern) Error!void {
        switch (pat.*) {
            .Var, .Lit, .Wild, .Tuple, .List, .Paren => try self.printPattern(pat),
            .Con => |con| {
                if (con.args.len == 0) {
                    try self.printQName(con.name);
                } else {
                    try self.write("(");
                    try self.printPattern(pat);
                    try self.write(")");
                }
            },
            else => {
                try self.write("(");
                try self.printPattern(pat);
                try self.write(")");
            },
        }
    }

    // ── Types ──────────────────────────────────────────────────────────

    pub fn printType(self: *PrettyPrinter, ty: ast.Type) Error!void {
        switch (ty) {
            .Var => |name| try self.write(name),
            .Con => |qname| try self.printQName(qname),
            .App => |types| {
                for (types, 0..) |t, i| {
                    if (i > 0) try self.writeByte(' ');
                    if (i > 0) {
                        try self.printTypeAtom(t.*);
                    } else {
                        try self.printType(t.*);
                    }
                }
            },
            .Fun => |types| {
                for (types, 0..) |t, i| {
                    if (i > 0) try self.write(" -> ");
                    try self.printType(t.*);
                }
            },
            .Tuple => |types| {
                try self.write("(");
                for (types, 0..) |t, i| {
                    if (i > 0) try self.write(", ");
                    try self.printType(t.*);
                }
                try self.write(")");
            },
            .List => |inner| {
                try self.write("[");
                try self.printType(inner.*);
                try self.write("]");
            },
            .Forall => |fa| {
                try self.write("forall ");
                for (fa.tyvars, 0..) |tv, i| {
                    if (i > 0) try self.writeByte(' ');
                    try self.write(tv);
                }
                try self.write(". ");
                if (fa.context) |ctx| {
                    try self.printContext(ctx);
                    try self.write(" => ");
                }
                try self.printType(fa.type.*);
            },
            .Paren => |inner| {
                try self.write("(");
                try self.printType(inner.*);
                try self.write(")");
            },
            .IParam => |ip| {
                try self.write("?");
                try self.write(ip.ip_name);
                try self.write(" :: ");
                try self.printType(ip.type.*);
            },
        }
    }

    /// Print a type in atom position — wraps application/function types in parens.
    fn printTypeAtom(self: *PrettyPrinter, ty: ast.Type) Error!void {
        switch (ty) {
            .Var, .Con, .Tuple, .List, .Paren => try self.printType(ty),
            else => {
                try self.write("(");
                try self.printType(ty);
                try self.write(")");
            },
        }
    }

    // ── Literals ───────────────────────────────────────────────────────

    fn printLiteral(self: *PrettyPrinter, lit: ast.Literal) Error!void {
        switch (lit) {
            .Char => |c| {
                try self.writeByte('\'');
                try self.writeCharEscaped(c.value);
                try self.writeByte('\'');
            },
            .String => |s| {
                try self.writeByte('"');
                for (s.value) |ch| {
                    try self.writeStringCharEscaped(ch);
                }
                try self.writeByte('"');
            },
            .Int => |i| {
                var int_buf: [20]u8 = undefined;
                const int_str = std.fmt.bufPrint(&int_buf, "{d}", .{i.value}) catch unreachable;
                try self.write(int_str);
            },
            .Float => |f| {
                var float_buf: [32]u8 = undefined;
                const float_str = std.fmt.bufPrint(&float_buf, "{d}", .{f.value}) catch unreachable;
                try self.write(float_str);
            },
            .Rational => |r| {
                var buf: [50]u8 = undefined;
                const s = std.fmt.bufPrint(&buf, "{d} % {d}", .{ r.numerator, r.denominator }) catch unreachable;
                try self.write(s);
            },
        }
    }

    fn writeCharEscaped(self: *PrettyPrinter, c: u21) Error!void {
        switch (c) {
            '\\' => try self.write("\\\\"),
            '\'' => try self.write("\\'"),
            '\n' => try self.write("\\n"),
            '\t' => try self.write("\\t"),
            '\r' => try self.write("\\r"),
            else => {
                if (c < 128) {
                    const byte: u8 = @intCast(c);
                    if (std.ascii.isPrint(byte)) {
                        try self.writeByte(byte);
                    } else {
                        var buf: [10]u8 = undefined;
                        const s = std.fmt.bufPrint(&buf, "\\{d}", .{c}) catch unreachable;
                        try self.write(s);
                    }
                } else {
                    var buf: [10]u8 = undefined;
                    const s = std.fmt.bufPrint(&buf, "\\{d}", .{c}) catch unreachable;
                    try self.write(s);
                }
            },
        }
    }

    fn writeStringCharEscaped(self: *PrettyPrinter, c: u8) Error!void {
        switch (c) {
            '\\' => try self.write("\\\\"),
            '"' => try self.write("\\\""),
            '\n' => try self.write("\\n"),
            '\t' => try self.write("\\t"),
            '\r' => try self.write("\\r"),
            else => {
                if (std.ascii.isPrint(c)) {
                    try self.writeByte(c);
                } else {
                    var buf: [10]u8 = undefined;
                    const s = std.fmt.bufPrint(&buf, "\\{d}", .{c}) catch unreachable;
                    try self.write(s);
                }
            },
        }
    }

    // ── Names ──────────────────────────────────────────────────────────

    fn printQName(self: *PrettyPrinter, qname: ast.QName) Error!void {
        if (qname.module_name) |mod| {
            try self.write(mod);
            try self.writeByte('.');
        }
        try self.write(qname.name);
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

const span_mod = @import("../diagnostics/span.zig");
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;

fn testSpan() SourceSpan {
    return SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 1));
}

fn testPatternVar(name: []const u8) ast.Pattern {
    return .{ .Var = .{ .name = name, .span = testSpan() } };
}

test "printModule: simple module with no exports" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const mod = ast.Module{
        .module_name = "Main",
        .exports = null,
        .imports = &.{},
        .declarations = &.{},
        .span = testSpan(),
    };

    const result = try pp.printModule(mod);
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("module Main where\n", result);
}

test "printModule: module with exports" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const mod = ast.Module{
        .module_name = "Data.List",
        .exports = &.{
            .{ .Var = "map" },
            .{ .Var = "filter" },
        },
        .imports = &.{},
        .declarations = &.{},
        .span = testSpan(),
    };

    const result = try pp.printModule(mod);
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("module Data.List (map, filter) where\n", result);
}

test "printModule: module with import" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const mod = ast.Module{
        .module_name = "Main",
        .exports = null,
        .imports = &.{
            .{
                .module_name = "Data.Map",
                .qualified = true,
                .as_alias = "Map",
                .span = testSpan(),
            },
        },
        .declarations = &.{},
        .span = testSpan(),
    };

    const result = try pp.printModule(mod);
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings(
        \\module Main where
        \\
        \\import qualified Data.Map as Map
        \\
    , result);
}

test "printExpr: variable" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    try pp.printExpr(.{ .Var = .{ .name = "foo", .span = testSpan() } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("foo", result);
}

test "printExpr: function application" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const fn_expr = ast.Expr{ .Var = .{ .name = "putStrLn", .span = testSpan() } };
    const arg_expr = ast.Expr{ .Lit = .{ .String = .{ .value = "Hello", .span = testSpan() } } };

    try pp.printExpr(.{ .App = .{ .fn_expr = &fn_expr, .arg_expr = &arg_expr } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("putStrLn \"Hello\"", result);
}

test "printExpr: integer literal" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    try pp.printExpr(.{ .Lit = .{ .Int = .{ .value = 42, .span = testSpan() } } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("42", result);
}

test "printExpr: if-then-else" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const cond = ast.Expr{ .Var = .{ .name = "b", .span = testSpan() } };
    const then_ = ast.Expr{ .Var = .{ .name = "x", .span = testSpan() } };
    const else_ = ast.Expr{ .Var = .{ .name = "y", .span = testSpan() } };

    try pp.printExpr(.{ .If = .{ .condition = &cond, .then_expr = &then_, .else_expr = &else_ } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("if b then x else y", result);
}

test "printExpr: lambda" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const body = ast.Expr{ .Var = .{ .name = "x", .span = testSpan() } };
    try pp.printExpr(.{ .Lambda = .{ .patterns = &.{testPatternVar("x")}, .body = &body } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("\\x -> x", result);
}

test "printExpr: tuple" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    try pp.printExpr(.{ .Tuple = &.{
        .{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } },
        .{ .Lit = .{ .Int = .{ .value = 2, .span = testSpan() } } },
    } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("(1, 2)", result);
}

test "printExpr: list" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    try pp.printExpr(.{ .List = &.{
        .{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } },
        .{ .Lit = .{ .Int = .{ .value = 2, .span = testSpan() } } },
        .{ .Lit = .{ .Int = .{ .value = 3, .span = testSpan() } } },
    } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("[1, 2, 3]", result);
}

test "printPattern: constructor pattern" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const pat = ast.Pattern{ .Con = .{
        .name = .{ .name = "Just", .span = testSpan() },
        .args = &.{testPatternVar("x")},
        .span = testSpan(),
    } };
    try pp.printPattern(&pat);
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("Just x", result);
}

test "printPattern: wildcard" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const pat = ast.Pattern{ .Wild = testSpan() };
    try pp.printPattern(&pat);
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("_", result);
}

test "printExpr: do notation with generator" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const expr = ast.Expr{ .Do = &.{
        .{ .Generator = .{ .pat = testPatternVar("y"), .expr = .{ .Var = .{ .name = "getLine", .span = testSpan() } } } },
    } };
    try pp.printExpr(expr);
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("do\n  y <- getLine\n", result);
    const gen_pat = expr.Do[0].Generator.pat;
    try std.testing.expect(gen_pat == .Var);
    try std.testing.expectEqualStrings("y", gen_pat.Var.name);
}

test "printType: function type" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const int_type = ast.Type{ .Con = .{ .name = "Int", .span = testSpan() } };
    const string_type = ast.Type{ .Con = .{ .name = "String", .span = testSpan() } };

    try pp.printType(.{ .Fun = &.{ &int_type, &string_type } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Int -> String", result);
}

test "printType: type application" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const maybe = ast.Type{ .Con = .{ .name = "Maybe", .span = testSpan() } };
    const int_type = ast.Type{ .Con = .{ .name = "Int", .span = testSpan() } };

    try pp.printType(.{ .App = &.{ &maybe, &int_type } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("Maybe Int", result);
}

test "printType: list type" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const int_type = ast.Type{ .Con = .{ .name = "Int", .span = testSpan() } };
    try pp.printType(.{ .List = &int_type });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("[Int]", result);
}

test "printType: forall with context" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const a_type = ast.Type{ .Var = "a" };
    try pp.printType(.{ .Forall = .{
        .tyvars = &.{"a"},
        .context = .{ .constraints = &.{.{ .class_name = "Show", .types = &.{.{ .Var = "a" }} }} },
        .type = &a_type,
    } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("forall a. Show a => a", result);
}

test "printDecl: data declaration" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    try pp.printDecl(.{ .Data = .{
        .name = "Maybe",
        .tyvars = &.{"a"},
        .constructors = &.{
            .{ .name = "Nothing", .fields = &.{}, .span = testSpan() },
            .{ .name = "Just", .fields = &.{.{ .Plain = .{ .Var = "a" } }}, .span = testSpan() },
        },
        .deriving = &.{ "Show", "Eq" },
        .span = testSpan(),
    } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings(
        \\data Maybe a
        \\  = Nothing
        \\  | Just a
        \\  deriving (Show, Eq)
    , result);
}

test "printDecl: type signature" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const io_type = ast.Type{ .Con = .{ .name = "IO", .span = testSpan() } };
    const unit_type = ast.Type{ .Tuple = &.{} };
    try pp.printDecl(.{ .TypeSig = .{
        .names = &.{"main"},
        .type = .{ .App = &.{ &io_type, &unit_type } },
        .span = testSpan(),
    } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("main :: IO ()", result);
}

test "printDecl: simple function binding" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const fn_expr = ast.Expr{ .Var = .{ .name = "putStrLn", .span = testSpan() } };
    const arg_expr = ast.Expr{ .Lit = .{ .String = .{ .value = "Hello", .span = testSpan() } } };

    try pp.printDecl(.{ .FunBind = .{
        .name = "main",
        .equations = &.{
            .{
                .patterns = &.{},
                .rhs = .{ .UnGuarded = .{ .App = .{ .fn_expr = &fn_expr, .arg_expr = &arg_expr } } },
                .where_clause = null,
                .span = testSpan(),
            },
        },
        .span = testSpan(),
    } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("main = putStrLn \"Hello\"\n", result);
}

test "printExpr: do notation" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    try pp.printExpr(.{ .Do = &.{
        .{ .Stmt = .{ .Var = .{ .name = "putStrLn", .span = testSpan() } } },
    } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("do\n  putStrLn\n", result);
}

test "printExpr: negation" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    const inner = ast.Expr{ .Lit = .{ .Int = .{ .value = 5, .span = testSpan() } } };
    try pp.printExpr(.{ .Negate = &inner });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("-5", result);
}

test "printExpr: infix application" {
    const allocator = std.testing.allocator;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();

    const left = ast.Expr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const right = ast.Expr{ .Lit = .{ .Int = .{ .value = 2, .span = testSpan() } } };
    try pp.printExpr(.{ .InfixApp = .{
        .left = &left,
        .op = .{ .name = "+", .span = testSpan() },
        .right = &right,
    } });
    const result = try pp.toOwnedSlice();
    defer allocator.free(result);

    try std.testing.expectEqualStrings("1 + 2", result);
}

test "printExpr: string literal with escapes" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    try pp.printExpr(.{ .Lit = .{ .String = .{ .value = "hello\nworld", .span = testSpan() } } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("\"hello\\nworld\"", result);
}

test "printExpr: char literal" {
    var pp = PrettyPrinter.init(std.testing.allocator);
    defer pp.deinit();

    try pp.printExpr(.{ .Lit = .{ .Char = .{ .value = 'A', .span = testSpan() } } });
    const result = try pp.toOwnedSlice();
    defer std.testing.allocator.free(result);

    try std.testing.expectEqualStrings("'A'", result);
}

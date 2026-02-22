//! Abstract Syntax Tree for Haskell source code.
//!
//! This module defines the complete AST type hierarchy for parsed Haskell source,
//! following the structure of GHC's HsSyn but simplified for easier implementation.
//!
//! Every AST node carries a SourceSpan for precise error reporting and source
//! location tracking.

const std = @import("std");
const span_mod = @import("../diagnostics/span.zig");
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;

/// A qualified name (Module.Name or just Name)
pub const QName = struct {
    module_name: ?[]const u8 = null,
    name: []const u8,
    span: SourceSpan,

    pub fn format(self: QName, w: *std.Io.Writer) std.Io.Writer.Error!void {
        if (self.module_name) |mod| {
            try w.print("{s}.{s}", .{ mod, self.name });
        } else {
            try w.writeAll(self.name);
        }
    }
};

/// A fully-qualified name with a list of module names
pub const QualName = struct {
    qualifiers: []const []const u8,
    name: []const u8,
    span: SourceSpan,
};

/// Import declaration: `import qualified Data.Map as Map`
pub const ImportDecl = struct {
    module_name: []const u8,
    qualified: bool = false,
    as_alias: ?[]const u8 = null,
    specs: ?ImportSpecs = null,
    span: SourceSpan,
};

/// Import specifications
pub const ImportSpecs = struct {
    hiding: bool = false,
    items: []const ImportSpec,
};

pub const ImportSpec = union(enum) {
    Var: []const u8,
    Con: []const u8,
    TyCon: []const u8,
    Class: []const u8,
};

/// Export specification
pub const ExportSpec = union(enum) {
    Var: []const u8,
    Con: []const u8,
    Type: TypeSpec,
    Module: []const u8,
};

pub const TypeSpec = struct {
    name: []const u8,
    with_constructors: bool = false,
};

/// A Haskell module
pub const Module = struct {
    module_name: []const u8,
    exports: ?[]const ExportSpec,
    imports: []const ImportDecl,
    declarations: []const Decl,
    span: SourceSpan,
};

/// Top-level declarations
pub const Decl = union(enum) {
    TypeSig: TypeSigDecl,
    FunBind: FunBinding,
    PatBind: PatBinding,
    Type: TypeDecl,
    Data: DataDecl,
    Newtype: NewtypeDecl,
    Class: ClassDecl,
    Instance: InstanceDecl,
    Default: DefaultDecl,
    Deriving: DerivingDecl,
    Foreign: ForeignDecl,
};

/// Type signature: `foo :: Int -> Int`
pub const TypeSigDecl = struct {
    names: []const []const u8,
    type: Type,
    span: SourceSpan,
};

/// Function binding with one or more equations
pub const FunBinding = struct {
    name: []const u8,
    equations: []const Match,
    span: SourceSpan,
};

/// Pattern binding: `foo = 42`
pub const PatBinding = struct {
    pattern: Pattern,
    rhs: Rhs,
    where_clause: ?[]const Decl = null,
    span: SourceSpan,
};

/// Type alias: `type Point = (Int, Int)`
pub const TypeDecl = struct {
    name: []const u8,
    tyvars: []const []const u8,
    type: Type,
    span: SourceSpan,
};

/// Data declaration: `data Maybe a = Nothing | Just a`
pub const DataDecl = struct {
    name: []const u8,
    tyvars: []const []const u8,
    constructors: []const ConDecl,
    deriving: []const []const u8,
    span: SourceSpan,
};

/// Constructor declaration
///
/// Supports three forms:
///   H98 plain:       `Con t1 t2`
///   H98 existential: `forall a. Show a => Con a`
///   GADT:            `Con :: forall a. Show a => a -> T a`
pub const ConDecl = struct {
    name: []const u8,
    fields: []const FieldDecl,
    doc_comment: ?[]const u8 = null,
    span: SourceSpan,
    /// Existential type variables: `forall a b.` before the constructor name (H98 style)
    ex_tyvars: []const []const u8 = &.{},
    /// Existential context: `Show a =>` before the constructor name (H98 style)
    ex_context: ?Context = null,
    /// GADT-style explicit type annotation: `Con :: Type`
    gadt_type: ?Type = null,
};

pub const FieldDecl = union(enum) {
    Plain: Type,
    Record: struct { name: []const u8, type: Type },
};

/// Newtype declaration: `newtype Maybe a = Maybe (Either () a)`
pub const NewtypeDecl = struct {
    name: []const u8,
    tyvars: []const []const u8,
    constructor: ConDecl,
    deriving: []const []const u8,
    span: SourceSpan,
};

/// Type class declaration: `class Eq a where (==) :: a -> a -> Bool`
pub const ClassDecl = struct {
    context: ?Context,
    class_name: []const u8,
    tyvars: []const []const u8,
    /// Functional dependencies (GHC extension): e.g., `| c -> e` becomes `.{ .determiners = &.{"c"}, .determined = &.{"e"} }`
    fundeps: []const FunDep,
    methods: []const ClassMethod,
    span: SourceSpan,
};

/// Functional dependency: `a b -> c` means variables `a` and `b` determine `c`
pub const FunDep = struct {
    /// Left-hand side: determining type variables
    determiners: []const []const u8,
    /// Right-hand side: determined type variables
    determined: []const []const u8,
};

pub const ClassMethod = struct {
    name: []const u8,
    type: Type,
    /// Optional default implementation. Stored as a slice of `Match` equations so that
    /// multi-equation defaults (e.g., `foo True = 1; foo False = 0`) are preserved.
    /// For a no-argument default the patterns slice is empty.
    default_implementation: ?[]const Match,
};

/// Type class instance: `instance Eq Bool where`
pub const InstanceDecl = struct {
    context: ?Context,
    constructor_type: Type,
    bindings: []const FunBinding,
    span: SourceSpan,
};

/// Default declaration: `default (Double)`
pub const DefaultDecl = struct {
    types: []const Type,
    span: SourceSpan,
};

/// Standalone deriving: `deriving instance Show Point`
pub const DerivingDecl = struct {
    standalone: bool,
    deriving_strategy: ?DerivingStrategy,
    type: Type,
    classes: []const []const u8,
    span: SourceSpan,
};

pub const DerivingStrategy = enum {
    Stock,
    Newtype,
    Anyclass,
};

/// Foreign function interface declaration
pub const ForeignDecl = struct {
    calling_convention: []const u8,
    name: []const u8,
    type: Type,
    span: SourceSpan,
};

/// Match rule (the right-hand side of a binding)
pub const Match = struct {
    patterns: []const Pattern,
    rhs: Rhs,
    where_clause: ?[]const Decl,
    span: SourceSpan,
};

/// Right-hand side of a binding
pub const Rhs = union(enum) {
    UnGuarded: Expr,
    Guarded: []const GuardedRhs,
};

pub const GuardedRhs = struct {
    guards: []const Guard,
    rhs: Expr,
};

pub const Guard = union(enum) {
    /// Pattern guard: pat <- expr
    PatGuard: struct { pattern: Pattern, expr: Expr },
    /// Boolean guard: condition (expression evaluating to Bool)
    ExprGuard: Expr,
};

/// Type context (class constraints)
pub const Context = struct {
    constraints: []const Assertion,
};

pub const Assertion = struct {
    class_name: []const u8,
    types: []const Type,
};

/// Expressions
pub const Expr = union(enum) {
    /// Variable or data constructor
    Var: QName,
    /// Literal value
    Lit: Literal,
    /// Application: f x
    App: struct { fn_expr: *const Expr, arg_expr: *const Expr },
    /// Infix application: x + y
    InfixApp: struct { left: *const Expr, op: QName, right: *const Expr },
    /// Left section: (1 +)
    LeftSection: struct { expr: *const Expr, op: QName },
    /// Right section: (+ 1)
    RightSection: struct { op: QName, expr: *const Expr },
    /// Lambda: \x y -> x + y
    Lambda: struct { patterns: []const Pattern, body: *const Expr },
    /// Let expression: let x = 5 in x + 1
    Let: struct { binds: []const Decl, body: *const Expr },
    /// Case expression: case x of { 0 -> "zero"; _ -> "other" }
    Case: struct { scrutinee: *const Expr, alts: []const Alt },
    /// If expression: if b then t else f
    If: struct { condition: *const Expr, then_expr: *const Expr, else_expr: *const Expr },
    /// Do notation
    Do: []const Stmt,
    /// Tuple: (1, 2, 3)
    Tuple: []const Expr,
    /// List: [1, 2, 3]
    List: []const Expr,
    /// Arithmetic sequence: [e ..]  (Haskell 2010 §3.10)
    EnumFrom: struct { from: *const Expr, span: SourceSpan },
    /// Arithmetic sequence: [e, e' ..]
    EnumFromThen: struct { from: *const Expr, then: *const Expr, span: SourceSpan },
    /// Arithmetic sequence: [e .. e']
    EnumFromTo: struct { from: *const Expr, to: *const Expr, span: SourceSpan },
    /// Arithmetic sequence: [e, e' .. e'']
    EnumFromThenTo: struct { from: *const Expr, then: *const Expr, to: *const Expr, span: SourceSpan },
    /// List comprehension: [x * 2 | x <- xs]
    ListComp: struct { expr: *const Expr, qualifiers: []const Qualifier },
    /// Type annotation: 5 :: Int
    TypeAnn: struct { expr: *const Expr, type: Type },
    /// Type application: f @Int (GHC TypeApplications extension)
    TypeApp: struct { fn_expr: *const Expr, type: Type, span: SourceSpan },
    /// Negation: -x
    Negate: *const Expr,
    /// Parenthesized expression: (x + y)
    Paren: *const Expr,
    /// Record construction: Point {x = 1, y = 2}
    RecordCon: struct { con: QName, fields: []const FieldUpdate },
    /// Record update: p {x = 5} (GHC extension, not in Haskell 2010)
    RecordUpdate: struct { expr: *const Expr, fields: []const FieldUpdate, span: SourceSpan },
    /// Field selector: x .point (GHC extension, not in Haskell 2010)
    Field: struct { expr: *const Expr, field_name: []const u8, span: SourceSpan },

    pub fn getSpan(self: Expr) SourceSpan {
        return switch (self) {
            .Var => |q| q.span,
            .Lit => |l| l.getSpan(),
            .App => |a| a.fn_expr.getSpan().merge(a.arg_expr.getSpan()),
            .InfixApp => |a| a.left.getSpan().merge(a.right.getSpan()),
            .LeftSection => |a| a.expr.getSpan().merge(a.op.span),
            .RightSection => |a| a.op.span.merge(a.expr.getSpan()),
            .Lambda => |l| l.body.getSpan(),
            .Let => |l| l.body.getSpan(),
            .Case => |c| c.scrutinee.getSpan(),
            .If => |i| i.condition.getSpan().merge(i.else_expr.getSpan()),
            .Do, .Tuple, .List => unreachable, // Need span on container
            .EnumFrom => |e| e.span,
            .EnumFromThen => |e| e.span,
            .EnumFromTo => |e| e.span,
            .EnumFromThenTo => |e| e.span,
            .ListComp => |l| l.expr.getSpan(),
            .TypeAnn => |a| a.expr.getSpan(),
            .TypeApp => |a| a.fn_expr.getSpan().merge(a.span),
            .Negate, .Paren => |e| e.getSpan(),
            .RecordCon => |r| r.con.span,
            .RecordUpdate => |r| r.span,
            .Field => |f| f.span,
        };
    }
};

pub const FieldUpdate = struct {
    field_name: []const u8,
    expr: Expr,
};

/// Field pattern in record patterns: Point { x = a }
/// Field punning is supported: Point { x } is equivalent to Point { x = x }
pub const FieldPattern = struct {
    field_name: []const u8,
    /// None for field punning (x -> x = x), Some for explicit pattern (x = p)
    pat: ?Pattern,
};

/// Case alternative
pub const Alt = struct {
    pattern: Pattern,
    rhs: Rhs,
    where_clause: ?[]const Decl = null,
    span: SourceSpan,
};

/// Do notation statement
pub const Stmt = union(enum) {
    /// Generator: x <- action
    Generator: struct { pat: Pattern, expr: Expr },
    /// Qualifier (boolean guard): predicate
    Qualifier: Expr,
    /// Statement: action
    Stmt: Expr,
    /// Let binding: let x = 5
    LetStmt: []const Decl,
};

/// List comprehension qualifier
pub const Qualifier = union(enum) {
    /// Generator: pat <- expr
    Generator: struct { pat: Pattern, expr: Expr },
    /// Boolean guard: predicate expression
    Qualifier: Expr,
    /// Let qualifier: let { decls }
    LetQualifier: []const Decl,
};

/// Patterns
pub const Pattern = union(enum) {
    /// Variable pattern: x
    Var: struct { name: []const u8, span: SourceSpan },
    /// Constructor pattern: Just x
    Con: struct { name: QName, args: []const Pattern, span: SourceSpan },
    /// Literal pattern: 42
    Lit: Literal,
    /// Wildcard pattern: _
    Wild: SourceSpan,
    /// As-pattern: p@(Just x)
    AsPar: struct { name: []const u8, name_span: SourceSpan, pat: *const Pattern, span: SourceSpan },
    /// Tuple pattern: (x, y)
    Tuple: struct { patterns: []const Pattern, span: SourceSpan },
    /// List pattern: [x, y, xs]
    List: struct { patterns: []const Pattern, span: SourceSpan },
    /// Infix constructor pattern: x : xs
    InfixCon: struct { left: *const Pattern, con: QName, right: *const Pattern },
    /// Negation pattern: struct { pat: *const Pattern, span: SourceSpan }
    Negate: struct { pat: *const Pattern, span: SourceSpan },
    /// Parenthesized pattern: (Just x)
    Paren: struct { pat: *const Pattern, span: SourceSpan },
    /// Bang pattern: !x (GHC extension)
    Bang: struct { pat: *const Pattern, span: SourceSpan },
    /// N+K pattern (deprecated)
    NPlusK: struct { name: []const u8, name_span: SourceSpan, k: i32, span: SourceSpan },
    /// Record pattern: Point { x = a, y = b }
    /// Field punning is supported: Point { x } is equivalent to Point { x = x }
    RecPat: struct { con: QName, fields: []const FieldPattern, span: SourceSpan },

    pub fn getSpan(self: Pattern) SourceSpan {
        return switch (self) {
            .Var => |v| v.span,
            .Con => |c| c.span,
            .Lit => |l| l.getSpan(),
            .Wild => |s| s,
            .AsPar => |a| a.span,
            .Tuple => |t| t.span,
            .List => |l| l.span,
            .InfixCon => |ic| ic.left.getSpan().merge(ic.right.getSpan()),
            .Negate => |n| n.span,
            .Paren => |p| p.span,
            .Bang => |b| b.span,
            .NPlusK => |npk| npk.span,
            .RecPat => |rp| rp.span,
        };
    }
};

/// Literal values
pub const Literal = union(enum) {
    Char: struct { value: u21, span: SourceSpan },
    String: struct { value: []const u8, span: SourceSpan },
    Int: struct { value: i64, span: SourceSpan },
    Float: struct { value: f64, span: SourceSpan },
    /// Rational literals from GHC (not in Haskell 2010)
    Rational: struct { numerator: i64, denominator: u64, span: SourceSpan },

    pub fn getSpan(self: Literal) SourceSpan {
        return switch (self) {
            .Char => |c| c.span,
            .String => |s| s.span,
            .Int => |i| i.span,
            .Float => |f| f.span,
            .Rational => |r| r.span,
        };
    }
};

/// Types
pub const Type = union(enum) {
    /// Type variable: a
    Var: []const u8,
    /// Type constructor: Int
    Con: QName,
    /// Type application: Maybe Int
    App: []const *const Type,
    /// Function type: Int -> String
    Fun: []const *const Type,
    /// Tuple type: (Int, String)
    Tuple: []const *const Type,
    /// List type: [Int]
    List: *const Type,
    /// Forall type: forall a. a -> a
    Forall: struct { tyvars: []const []const u8, context: ?Context, type: *const Type },
    /// Parenthesized type: (Maybe Int)
    Paren: *const Type,
    /// Implicit parameter (?x::Int)
    IParam: struct { ip_name: []const u8, type: *const Type },

    pub fn getSpan(self: Type) SourceSpan {
        return switch (self) {
            .Var, .Con, .App, .Fun, .Tuple => unreachable, // TODO: Add span to these variants
            .List => |t| t.getSpan(),
            .Forall => |f| f.type.getSpan(),
            .Paren => |t| t.getSpan(),
            .IParam => |i| i.type.getSpan(),
        };
    }
};

/// Fixity information for operators.
/// Stores the precedence (0–9, higher binds tighter) and associativity.
pub const FixityInfo = struct {
    precedence: u8,
    fixity: Fixity,
};

/// Fixity declaration: infixl 6 +++
pub const Fixity = enum {
    InfixL,
    InfixR,
    InfixN, // non-associative
};

pub const FixityDecl = struct {
    fixity: Fixity,
    precedence: u8,
    operators: []const []const u8,
    span: SourceSpan,
};

test "QName format" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const name = try allocator.dupe(u8, "foo");
    const mod_name = try allocator.dupe(u8, "Data.Foo");

    const qname = QName{
        .module_name = mod_name,
        .name = name,
        .span = SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 10)),
    };

    var buf: [100]u8 = undefined;
    const formatted = try std.fmt.bufPrint(&buf, "{f}", .{qname});
    try std.testing.expectEqualStrings("Data.Foo.foo", formatted);
}

test "TypeDecl construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const name = try allocator.dupe(u8, "Point");

    const decl = TypeDecl{
        .name = name,
        .tyvars = &.{},
        .type = .{ .Var = "a" },
        .span = SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 10)),
    };

    try std.testing.expectEqualStrings("Point", decl.name);
}

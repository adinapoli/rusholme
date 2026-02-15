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

    pub fn format(self: QName, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        if (self.module_name) |mod| {
            try writer.print("{s}.{s}", .{ mod, self.name });
        } else {
            try writer.writeAll(self.name);
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
pub const ConDecl = struct {
    name: []const u8,
    fields: []const FieldDecl,
    doc_comment: ?[]const u8 = null,
    span: SourceSpan,
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
    methods: []const ClassMethod,
    span: SourceSpan,
};

pub const ClassMethod = struct {
    name: []const u8,
    type: Type,
    default_implementation: ?Rhs,
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
    PatGuard: []const Pattern,
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
    /// List comprehension: [x * 2 | x <- xs]
    ListComp: struct { expr: *const Expr, qualifiers: []const Qualifier },
    /// Type annotation: 5 :: Int
    TypeAnn: struct { expr: *const Expr, type: Type },
    /// Negation: -x
    Negate: *const Expr,
    /// Parenthesized expression: (x + y)
    Paren: *const Expr,
    /// Record construction: Point {x = 1, y = 2}
    RecordCon: struct { con: QName, fields: []const FieldUpdate },
    /// Record update: p {x = 5} (GHC extension, not in Haskell 2010)
    RecordUpdate: struct { expr: *const Expr, fields: []const FieldUpdate },
    /// Field selector: x .point (GHC extension, not in Haskell 2010)
    Field: struct { expr: *const Expr, field_name: []const u8 },

    pub fn getSpan(self: Expr) SourceSpan {
        return switch (self) {
            .Var => |q| q.span,
            .Lit => |l| l.span,
            .App => |a| a.fn_expr.getSpan().merge(a.arg_expr.getSpan()),
            .InfixApp => |a| a.left.getSpan().merge(a.right.getSpan()),
            .LeftSection => |a| a.expr.getSpan().merge(a.op.span),
            .RightSection => |a| a.op.span.merge(a.expr.getSpan()),
            .Lambda => |l| l.body.getSpan(),
            .Let => |l| l.body.getSpan(),
            .Case => |c| c.scrutinee.getSpan(),
            .If => |i| i.condition.getSpan().merge(i.else_expr.getSpan()),
            .Do, .Tuple, .List => unreachable, // Need span on container
            .ListComp => |l| l.expr.getSpan(),
            .TypeAnn => |a| a.expr.getSpan(),
            .Negate, .Paren => |e| e.getSpan(),
            .RecordCon => |r| r.con.span,
            .RecordUpdate, .Field => unreachable,
        };
    }
};

pub const FieldUpdate = struct {
    field_name: []const u8,
    expr: Expr,
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
    Generator: struct { pat: Pattern, expr: Expr },
    Qualifier: Expr,
};

/// Patterns
pub const Pattern = union(enum) {
    /// Variable pattern: x
    Var: []const u8,
    /// Constructor pattern: Just x
    Con: struct { name: QName, args: []const Pattern },
    /// Literal pattern: 42
    Lit: Literal,
    /// Wildcard pattern: _
    Wild: SourceSpan,
    /// As-pattern: p@(Just x)
    AsPar: struct { name: []const u8, pat: *const Pattern },
    /// Tuple pattern: (x, y)
    Tuple: []const Pattern,
    /// List pattern: [x, y, xs]
    List: []const Pattern,
    /// Infix constructor pattern: x : xs
    InfixCon: struct { left: Pattern, con: QName, right: Pattern },
    /// Negation pattern: -5
    Negate: *const Pattern,
    /// Parenthesized pattern: (Just x)
    Paren: *const Pattern,
    /// Bang pattern: !x (GHC extension)
    Bang: *const Pattern,
    /// N+K pattern (deprecated)
    NPlusK: struct { name: []const u8, k: i32 },

    pub fn getSpan(self: Pattern) SourceSpan {
        return switch (self) {
            .Var, .Con, .AsPar, .Tuple, .List, .InfixCon, .NPlusK => unreachable, // TODO: Add span to these variants
            .Lit => |l| l.span,
            .Wild => |s| s,
            .Negate, .Paren, .Bang => |p| p.getSpan(),
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
    App: []const Type,
    /// Function type: Int -> String
    Fun: []const Type,
    /// Tuple type: (Int, String)
    Tuple: []const Type,
    /// List type: [Int]
    List: Type,
    /// Forall type: forall a. a -> a
    Forall: struct { tyvars: []const []const u8, context: ?Context, type: Type },
    /// Parenthesized type: (Maybe Int)
    Paren: Type,
    /// Implicit parameter (?x::Int)
    IParam: struct { ip_name: []const u8, type: Type },

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
    const formatted = try std.fmt.bufPrint(&buf, "{}", .{qname});
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
        .type = .Var,
    };

    try std.testing.expectEqualStrings("Point", decl.name);
}

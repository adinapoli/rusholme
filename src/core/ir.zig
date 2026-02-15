//! Core IR types (System F_C-like intermediate representation).

pub const Expr = union(enum) {
    Var: []const u8,
    App: struct { fn_expr: *const Expr, arg_expr: *const Expr },
    Lam: struct { param: []const u8, body: *const Expr },
    Let: struct { name: []const u8, value: *const Expr, body: *const Expr },
    TypeApp: struct { expr: *const Expr, type_arg: Type },
    TypeLam: struct { kind_var: []const u8, body: *const Expr },
    Case: struct { scrutinee: *const Expr, alts: []const Alt },

    pub const Alt = struct {
        pat: Pattern,
        body: *const Expr,
    };

    pub const Pattern = union(enum) {
        Var: []const u8,
        Con: struct { name: []const u8, args: []const Pattern },
    };
};

pub const Type = union(enum) {
    Var: []const u8,
    Con: struct { name: []const u8, args: []const Type },
    Fun: []const Type, // [domain, codomain]
};

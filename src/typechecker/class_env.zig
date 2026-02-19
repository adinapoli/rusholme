//! Class and instance environments for type class resolution.
//!
//! This module provides the data structures needed for Wadler-Blott
//! dictionary-passing type class resolution (Haskell 2010 §4).
//!
//! The `ClassEnv` stores:
//! - **Class declarations**: name, type variable, superclasses, methods.
//! - **Instance declarations**: class, instance head type, context constraints.
//!
//! The constraint solver queries the `ClassEnv` to resolve class constraints
//! emitted during type inference.  For example, given a constraint `Eq Int`,
//! the solver looks up matching instances and (if found) discharges the
//! constraint.  Instance context constraints (e.g. `Eq a` from
//! `instance Eq a => Eq [a]`) are emitted as new constraints.
//!
//! ## Scope
//!
//! Single-parameter type classes only (Haskell 2010).  Multi-parameter type
//! classes and functional dependencies are deferred.
//!
//! ## References
//!
//! - Wadler & Blott, "How to make ad-hoc polymorphism less ad hoc", POPL 1989.
//! - Peyton Jones, "Typing Haskell in Haskell", 2000.

const std = @import("std");
const htype_mod = @import("htype.zig");
const span_mod = @import("../diagnostics/span.zig");
const naming_mod = @import("../naming/unique.zig");

pub const HType = htype_mod.HType;
pub const Name = naming_mod.Name;
pub const Unique = naming_mod.Unique;
pub const SourceSpan = span_mod.SourceSpan;

// ── ClassConstraint ───────────────────────────────────────────────────

/// A class constraint: `ClassName ty`.
///
/// During inference, constraints are emitted with `ty` containing fresh
/// metavariables.  The solver chases metavar chains before attempting
/// instance resolution.
pub const ClassConstraint = struct {
    class_name: Name,
    ty: HType,
    span: SourceSpan,
};

// ── ClassInfo ─────────────────────────────────────────────────────────

/// Information about a type class declaration.
///
/// Stored in the `ClassEnv` and used during instance resolution and
/// method type lookup.
pub const ClassInfo = struct {
    /// The class name (e.g. `Eq`, `Ord`).
    name: Name,
    /// The unique ID of the class's type variable.  For `class Eq a`,
    /// this is `a`'s unique.  Single-parameter classes only.
    tyvar: u64,
    /// Superclass names.  For `class Eq a => Ord a`, this is `[Eq]`.
    /// The solver uses this to emit entailed constraints.
    superclasses: []const Name,
    /// Method signatures declared in the class body.
    methods: []const MethodInfo,
};

/// A single method in a class declaration.
pub const MethodInfo = struct {
    /// Method name (e.g. `(==)`, `show`).
    name: Name,
    /// The method's type with the class tyvar as a rigid.
    /// For `(==) :: a -> a -> Bool` in `class Eq a`, this is
    /// `Rigid(a) -> Rigid(a) -> Con(Bool)`.  The class constraint
    /// itself is NOT included — it is added by the typechecker when
    /// building the qualified `TyScheme`.
    ty: HType,
    /// Whether a default implementation exists.
    has_default: bool,
};

// ── InstanceInfo ──────────────────────────────────────────────────────

/// Information about a type class instance declaration.
pub const InstanceInfo = struct {
    /// The class this is an instance of (e.g. `Eq`).
    class_name: Name,
    /// The instance head type.  For `instance Eq Int`, this is `Con(Int)`.
    /// For `instance Eq a => Eq [a]`, this is `Con([], [Rigid(a)])`.
    head: HType,
    /// Instance context constraints.  For `instance Eq a => Eq [a]`,
    /// this is `[ClassConstraint(Eq, Rigid(a))]`.  Empty for
    /// unconditional instances like `instance Eq Int`.
    context: []const ClassConstraint,
    /// Source location (for diagnostics).
    span: SourceSpan,
};

// ── ClassEnv ──────────────────────────────────────────────────────────

/// The class and instance environment.
///
/// Populated from parsed class/instance declarations (and built-in
/// registrations) before type inference begins.  Queried by the
/// constraint solver during class constraint resolution.
pub const ClassEnv = struct {
    /// Maps class unique ID → ClassInfo.
    classes: std.AutoHashMapUnmanaged(u64, ClassInfo),
    /// Maps class unique ID → list of known instances.
    instances: std.AutoHashMapUnmanaged(u64, std.ArrayListUnmanaged(InstanceInfo)),
    alloc: std.mem.Allocator,

    pub fn init(alloc: std.mem.Allocator) ClassEnv {
        return .{
            .classes = .empty,
            .instances = .empty,
            .alloc = alloc,
        };
    }

    pub fn deinit(self: *ClassEnv) void {
        self.classes.deinit(self.alloc);
        var it = self.instances.iterator();
        while (it.next()) |entry| {
            entry.value_ptr.deinit(self.alloc);
        }
        self.instances.deinit(self.alloc);
    }

    /// Register a class declaration.
    pub fn addClass(self: *ClassEnv, info: ClassInfo) !void {
        try self.classes.put(self.alloc, info.name.unique.value, info);
    }

    /// Register an instance declaration.
    pub fn addInstance(self: *ClassEnv, info: InstanceInfo) !void {
        const gop = try self.instances.getOrPut(self.alloc, info.class_name.unique.value);
        if (!gop.found_existing) {
            gop.value_ptr.* = .empty;
        }
        try gop.value_ptr.append(self.alloc, info);
    }

    /// Look up a class by its unique ID.
    pub fn lookupClass(self: *const ClassEnv, unique: u64) ?ClassInfo {
        return self.classes.get(unique);
    }

    /// Look up all instances for a class by its unique ID.
    pub fn lookupInstances(self: *const ClassEnv, class_unique: u64) []const InstanceInfo {
        if (self.instances.get(class_unique)) |list| {
            return list.items;
        }
        return &.{};
    }

    /// Return the superclass names for a given class, or empty if not found.
    pub fn superclasses(self: *const ClassEnv, class_unique: u64) []const Name {
        if (self.classes.get(class_unique)) |info| {
            return info.superclasses;
        }
        return &.{};
    }
};

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;
const Known = @import("../naming/known.zig");

fn testSpan() SourceSpan {
    return SourceSpan.init(
        span_mod.SourcePos.init(1, 1, 1),
        span_mod.SourcePos.init(1, 1, 1),
    );
}

test "ClassEnv: add and lookup class" {
    var env = ClassEnv.init(testing.allocator);
    defer env.deinit();

    const eq_method = MethodInfo{
        .name = Known.Fn.putStrLn, // placeholder name for (==)
        .ty = HType{ .Con = .{ .name = Known.Type.Bool, .args = &.{} } },
        .has_default = false,
    };

    try env.addClass(.{
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{eq_method},
    });

    const info = env.lookupClass(Known.Class.Eq.unique.value).?;
    try testing.expectEqualStrings("Eq", info.name.base);
    try testing.expectEqual(1, info.methods.len);
    try testing.expectEqual(0, info.superclasses.len);
}

test "ClassEnv: add and lookup instances" {
    var env = ClassEnv.init(testing.allocator);
    defer env.deinit();

    try env.addInstance(.{
        .class_name = Known.Class.Eq,
        .head = HType{ .Con = .{ .name = Known.Type.Int, .args = &.{} } },
        .context = &.{},
        .span = testSpan(),
    });
    try env.addInstance(.{
        .class_name = Known.Class.Eq,
        .head = HType{ .Con = .{ .name = Known.Type.Bool, .args = &.{} } },
        .context = &.{},
        .span = testSpan(),
    });

    const instances = env.lookupInstances(Known.Class.Eq.unique.value);
    try testing.expectEqual(2, instances.len);

    // No instances for Show
    const show_instances = env.lookupInstances(Known.Class.Show.unique.value);
    try testing.expectEqual(0, show_instances.len);
}

test "ClassEnv: superclass chain" {
    var env = ClassEnv.init(testing.allocator);
    defer env.deinit();

    // class Eq a
    try env.addClass(.{
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{},
    });

    // class Eq a => Ord a
    try env.addClass(.{
        .name = Known.Class.Ord,
        .tyvar = 5001,
        .superclasses = &.{Known.Class.Eq},
        .methods = &.{},
    });

    const ord_supers = env.superclasses(Known.Class.Ord.unique.value);
    try testing.expectEqual(1, ord_supers.len);
    try testing.expectEqualStrings("Eq", ord_supers[0].base);

    const eq_supers = env.superclasses(Known.Class.Eq.unique.value);
    try testing.expectEqual(0, eq_supers.len);
}

test "ClassEnv: lookup missing class returns null" {
    var env = ClassEnv.init(testing.allocator);
    defer env.deinit();

    try testing.expect(env.lookupClass(999) == null);
}

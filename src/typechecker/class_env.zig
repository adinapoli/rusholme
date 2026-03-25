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
    /// Pointer to the constrained type.  Must be a pointer (not a value
    /// copy) so that when the type is a fresh metavar, unifier solutions
    /// propagate through the shared mutable cell.  See env.zig
    /// `TyScheme.instantiate` where constraints are instantiated with
    /// fresh metas that must stay linked to the type tree.
    ty: *const HType,
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
    /// Dictionary constructor name (e.g. `MkDict$Eq`).
    /// Stored during desugaring so that instance declarations can reuse
    /// the same constructor unique instead of creating fresh ones (issue #569).
    dict_con_name: Name,
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

/// A binding from a type variable name to the Rigid HType node created
/// for it during Pass 0a instance registration.  Stored so that Pass 2
/// (instance method body inference) can reuse the *exact same* Rigid
/// nodes — matching by unique ID — that appear in the instance head and
/// context.
pub const RigidBinding = struct {
    tyvar: []const u8,
    rigid: *const HType,
};

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
    /// Rigid scope from Pass 0a.  Maps each instance type variable name
    /// to the Rigid HType node allocated during instance registration.
    /// Pass 2 uses this to set up the same type variable scope when
    /// inferring instance method bodies, ensuring Rigid unique IDs match
    /// those in `head` and `context`.
    rigid_scope: []const RigidBinding = &.{},
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

    /// Update the dictionary constructor name for an existing class.
    /// Called by the desugarer after creating the dictionary data type.
    /// Asserts that the class exists (should have been registered during type inference).
    pub fn setDictConName(self: *ClassEnv, class_unique: u64, dict_con_name: Name) void {
        const entry = self.classes.getPtr(class_unique) orelse {
            std.debug.panic("setDictConName: class {d} not found in ClassEnv", .{class_unique});
        };
        entry.dict_con_name = dict_con_name;
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

    /// Look up a class by its base name (e.g. "Eq").
    ///
    /// This is used by `skolemiseSignature` to resolve string class names
    /// from parsed `Assertion`s (in user-written type signatures) to the
    /// `Name` with the correct unique ID.  Returns `null` if no class
    /// with that base name has been registered.
    pub fn lookupClassByBaseName(self: *const ClassEnv, base_name: []const u8) ?ClassInfo {
        var it = self.classes.iterator();
        while (it.next()) |entry| {
            if (std.mem.eql(u8, entry.value_ptr.name.base, base_name)) {
                return entry.value_ptr.*;
            }
        }
        return null;
    }

    /// Return the superclass names for a given class, or empty if not found.
    pub fn superclasses(self: *const ClassEnv, class_unique: u64) []const Name {
        if (self.classes.get(class_unique)) |info| {
            return info.superclasses;
        }
        return &.{};
    }

    /// Merge all classes and instances from `other` into `self`.
    ///
    /// Classes are copied by unique ID (existing entries are overwritten).
    /// Instances are appended to the existing instance list for each class.
    ///
    /// Used by the REPL to seed a fresh `InferCtx.class_env` with
    /// classes/instances accumulated from prior inputs, and to merge
    /// newly-declared classes/instances back into the session state.
    pub fn mergeFrom(self: *ClassEnv, other: *const ClassEnv) !void {
        // Merge class declarations.
        var class_it = other.classes.iterator();
        while (class_it.next()) |entry| {
            try self.classes.put(self.alloc, entry.key_ptr.*, entry.value_ptr.*);
        }

        // Merge instance declarations.
        var inst_it = other.instances.iterator();
        while (inst_it.next()) |entry| {
            const gop = try self.instances.getOrPut(self.alloc, entry.key_ptr.*);
            if (!gop.found_existing) {
                gop.value_ptr.* = .empty;
            }
            for (entry.value_ptr.items) |inst| {
                try gop.value_ptr.append(self.alloc, inst);
            }
        }
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
        .dict_con_name = .{ .base = "", .unique = .{ .value = 0 } },
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
        .dict_con_name = .{ .base = "", .unique = .{ .value = 0 } },
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{},
    });

    // class Eq a => Ord a
    try env.addClass(.{
        .dict_con_name = .{ .base = "", .unique = .{ .value = 0 } },
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

test "ClassEnv: lookupClassByBaseName finds registered class" {
    var env = ClassEnv.init(testing.allocator);
    defer env.deinit();

    try env.addClass(.{
        .dict_con_name = .{ .base = "", .unique = .{ .value = 0 } },
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{},
    });

    const info = env.lookupClassByBaseName("Eq");
    try testing.expect(info != null);
    try testing.expectEqualStrings("Eq", info.?.name.base);
    try testing.expectEqual(Known.Class.Eq.unique.value, info.?.name.unique.value);
}

test "ClassEnv: lookupClassByBaseName returns null for unknown class" {
    var env = ClassEnv.init(testing.allocator);
    defer env.deinit();

    try testing.expect(env.lookupClassByBaseName("Eq") == null);
    try testing.expect(env.lookupClassByBaseName("") == null);
}

//! Tag Registry — Persistent Discriminant Assignment
//!
//! Owns all constructor/function/partial-application discriminant
//! assignments for GRIN → LLVM translation.  In the REPL, a single
//! `TagRegistry` lives in `JitEngine` and is shared across every
//! compilation.  In the batch compiler a local instance is created.
//!
//! ## Key invariant
//!
//! **Once a tag receives a discriminant, it never changes.**
//!
//! `register()` is idempotent: calling it again for an already-known
//! tag is a no-op.  New tags get the next sequential discriminant.
//! This append-only property prevents the discriminant-drift segfaults
//! that occur when a tag table is rebuilt from scratch and the
//! scanning order changes (#631, #637).
//!
//! See: https://github.com/adinapoli/rusholme/issues/636

const std = @import("std");

const grin = @import("../grin/ast.zig");
pub const FieldType = grin.FieldType;

// Well-known Prelude constructor unique IDs.
const known = struct {
    pub const nil_val = 207; // []
    pub const cons_val = 208; // (:)
};

/// Well-known constructor discriminants captured from the registry.
/// Used by the JIT engine to format results correctly.
pub const KnownTags = struct {
    true_disc: ?i64 = null,
    false_disc: ?i64 = null,
    nil_disc: ?i64 = null,
    cons_disc: ?i64 = null,
    nothing_disc: ?i64 = null,
    just_disc: ?i64 = null,
    unit_disc: ?i64 = null,
};

// ═══════════════════════════════════════════════════════════════════════
// TagRegistry
// ═══════════════════════════════════════════════════════════════════════

/// Persistent, append-only tag discriminant registry.
///
/// Built once before translation starts by scanning all `ConstTagNode`
/// values in the program.  A composite key (encoding tag type + name
/// unique + partial-application missing count) ensures that `C:Foo`,
/// `F:Foo`, `P(1):Foo`, and `P(2):Foo` all receive distinct
/// discriminants even when they share the same name unique.
///
/// See: https://github.com/adinapoli/rusholme/issues/449
pub const TagRegistry = struct {
    /// Discriminant assigned to each tag, keyed by composite `tagKey`.
    discriminants: std.AutoHashMapUnmanaged(u64, i64),
    /// Number of fields for each tag, keyed by composite `tagKey`.
    field_counts: std.AutoHashMapUnmanaged(u64, u32),
    /// Field types per tag, keyed by composite `tagKey`.
    /// Each slice contains FieldType for each field position.
    /// This is HPT-lite: a simplified type tracking that will be
    /// extended when implementing full HPT (M2.4).
    field_types: std.AutoHashMapUnmanaged(u64, []const FieldType),
    /// Set of composite keys that are F-tags (function thunks).
    /// Used by the inline eval loop to distinguish thunks from constructors.
    fun_tags: std.AutoHashMapUnmanaged(u64, void),
    /// Maps F-tag composite keys to their GRIN names for LLVM function lookup.
    fun_tag_names: std.AutoHashMapUnmanaged(u64, grin.Name),
    /// Set of composite keys that are P-tags (partial applications).
    /// Used by the apply function to dispatch on partial application nodes.
    partial_tags: std.AutoHashMapUnmanaged(u64, void),
    /// Maps P-tag composite keys to their tag info (name + missing count + field count).
    partial_tag_info: std.AutoHashMapUnmanaged(u64, PartialTagInfo),
    /// Maps constructor base name strings to their discriminants.
    /// Populated during register() for Con tags. Used by findByName()
    /// to look up well-known constructors (True, False, [], (:), etc.)
    /// regardless of which unique ID the renamer assigned.
    con_name_to_disc: std.StringHashMapUnmanaged(i64),
    /// Next discriminant to assign.
    next: i64,

    pub const PartialTagInfo = struct {
        name: grin.Name,
        missing: u32,
        n_fields: u32,
    };

    // Start discriminants at 0x1000 to avoid colliding with RTS special
    // tags (Unit=0, Int=1, Char=2, String=3, Thunk=0x100, Ind=0x101,
    // Closure=0x200). This matches rts/node.zig Tag.Data = 0x1000.
    pub const first_discriminant: i64 = 0x1000;

    pub fn init() TagRegistry {
        return .{
            .discriminants = .{},
            .field_counts = .{},
            .field_types = .{},
            .fun_tags = .{},
            .fun_tag_names = .{},
            .partial_tags = .{},
            .partial_tag_info = .{},
            .con_name_to_disc = .{},
            .next = first_discriminant,
        };
    }

    pub fn deinit(self: *TagRegistry, alloc: std.mem.Allocator) void {
        self.discriminants.deinit(alloc);
        self.field_counts.deinit(alloc);
        // Free each field_types slice.
        var iter = self.field_types.iterator();
        while (iter.next()) |entry| {
            alloc.free(entry.value_ptr.*);
        }
        self.field_types.deinit(alloc);
        self.fun_tags.deinit(alloc);
        self.fun_tag_names.deinit(alloc);
        self.partial_tags.deinit(alloc);
        self.partial_tag_info.deinit(alloc);
        self.con_name_to_disc.deinit(alloc);
    }

    // ── Registration ─────────────────────────────────────────────────

    /// Register a tag with the given field count.
    /// If already registered, this is a no-op (idempotent).
    /// F-tags (Fun) are recorded in the fun_tags set for eval dispatch.
    /// P-tags (Partial) are recorded in the partial_tags set for apply dispatch.
    pub fn register(self: *TagRegistry, alloc: std.mem.Allocator, tag: grin.Tag, n_fields: u32) !void {
        const key = tagKey(tag);
        if (self.discriminants.contains(key)) return;

        // For constructors, deduplicate by base name: if a constructor with
        // the same name but a different unique already exists (e.g., the
        // built-in True with unique 200 vs the Prelude-renamed True with
        // unique 1103), reuse its discriminant.
        const disc = if (tag.tag_type == .Con)
            if (self.con_name_to_disc.get(tag.name.base)) |existing_disc|
                existing_disc
            else
                self.next
        else
            self.next;

        const is_new = (disc == self.next);

        try self.discriminants.put(alloc, key, disc);
        try self.field_counts.put(alloc, key, n_fields);
        // Default: all fields are ptr (conservative for HPT-lite).
        const types = try alloc.alloc(FieldType, n_fields);
        for (types) |*t| t.* = .ptr;
        try self.field_types.put(alloc, key, types);
        // Track Con-tags by base name for reverse lookup (findByName).
        if (tag.tag_type == .Con) {
            try self.con_name_to_disc.put(alloc, tag.name.base, disc);
        }
        // Track F-tags for the inline eval loop in translateCase.
        if (tag.tag_type == .Fun) {
            try self.fun_tags.put(alloc, key, {});
            try self.fun_tag_names.put(alloc, key, tag.name);
        }
        // Track P-tags for the apply function dispatch.
        if (tag.tag_type == .Partial) {
            try self.partial_tags.put(alloc, key, {});
            try self.partial_tag_info.put(alloc, key, .{
                .name = tag.name,
                .missing = tag.tag_type.Partial,
                .n_fields = n_fields,
            });
        }
        if (is_new) self.next += 1;
    }

    /// Register all tags from a set of GRIN defs.  Idempotent — safe to
    /// call with overlapping or previously-registered def sets.
    ///
    /// This replaces the 4-phase scan logic that was previously
    /// spread across `translateProgramToModule` and
    /// `prepareGlobalTagTable`.  It:
    ///   1. Scans each def's body for C-tags and F-tags (Store, Case patterns).
    ///   2. Pre-registers every def with params > 0 as a potential F-tag.
    ///   3. Ensures list constructors ([] and (:)) are present.
    ///   4. Ensures intermediate partial tags (P(n-1) chains) are present.
    pub fn registerDefsAndBodies(self: *TagRegistry, alloc: std.mem.Allocator, defs: []const grin.Def) !void {
        // Phase 1: scan def bodies for tags.
        for (defs) |def| {
            try scanExprForTags(alloc, def.body, self);
        }
        // Phase 2: pre-register all defs as potential F-tags.
        for (defs) |def| {
            if (def.params.len > 0) {
                const fun_tag = grin.Tag{ .name = def.name, .tag_type = .Fun };
                try self.register(alloc, fun_tag, @intCast(def.params.len));
            }
        }
        // Phase 3: ensure list constructors.
        try self.ensureListConstructors(alloc);
        // Phase 4: ensure intermediate partial tags.
        {
            var prev_count = self.partial_tags.count();
            while (true) {
                try self.registerIntermediatePartialTags(alloc);
                const new_count = self.partial_tags.count();
                if (new_count == prev_count) break;
                prev_count = new_count;
            }
        }
    }

    /// Merge program-specific field types into the registry.
    /// Constructor field types from the GRIN program's field_types map
    /// override the default all-ptr types assigned during registration.
    ///
    /// Note: field type refinement is safe for code compiled *after* the
    /// call but not retroactively for already-JIT'd code.  In the REPL
    /// this is fine since each expression is freshly compiled.
    pub fn registerFieldTypes(self: *TagRegistry, alloc: std.mem.Allocator, program_field_types: std.AutoHashMapUnmanaged(u64, []const FieldType)) !void {
        var iter = program_field_types.iterator();
        while (iter.next()) |entry| {
            const unique = entry.key_ptr.*;
            const field_types = entry.value_ptr.*;
            const key = unique *% 4; // Con key encoding

            if (self.field_types.get(key)) |existing| {
                alloc.free(existing);
            }

            const types = try alloc.alloc(FieldType, field_types.len);
            @memcpy(types, field_types);
            try self.field_types.put(alloc, key, types);
        }
    }

    // ── Lookups ──────────────────────────────────────────────────────

    /// Return the discriminant for a tag, or null if unknown.
    pub fn discriminant(self: *const TagRegistry, tag: grin.Tag) ?i64 {
        return self.discriminants.get(tagKey(tag));
    }

    /// Return the field count for a tag, or null if unknown.
    pub fn fieldCount(self: *const TagRegistry, tag: grin.Tag) ?u32 {
        return self.field_counts.get(tagKey(tag));
    }

    /// Return field types for a tag, or null if unknown.
    pub fn fieldTypes(self: *const TagRegistry, tag: grin.Tag) ?[]const FieldType {
        return self.field_types.get(tagKey(tag));
    }

    /// Return true if the named variable is a known nullary constructor.
    pub fn isNullaryByName(self: *const TagRegistry, name: grin.Name) bool {
        const con_key = name.unique.value *% 4; // Con key encoding
        const fc = self.field_counts.get(con_key) orelse return false;
        return fc == 0;
    }

    /// Return the discriminant for a variable if it is a known nullary
    /// constructor, otherwise null.
    pub fn discriminantByName(self: *const TagRegistry, name: grin.Name) ?i64 {
        if (!self.isNullaryByName(name)) return null;
        const con_key = name.unique.value *% 4; // Con key encoding
        return self.discriminants.get(con_key);
    }

    /// Find a constructor discriminant by base name string.
    pub fn findByName(self: *const TagRegistry, name_base: []const u8) ?i64 {
        return self.con_name_to_disc.get(name_base);
    }

    /// Extract well-known constructor discriminants for result formatting.
    pub fn getKnownDiscriminants(self: *const TagRegistry) KnownTags {
        return .{
            .true_disc = self.findByName("True"),
            .false_disc = self.findByName("False"),
            .nil_disc = self.findByName("[]"),
            .cons_disc = self.findByName("(:)"),
            .nothing_disc = self.findByName("Nothing"),
            .just_disc = self.findByName("Just"),
            .unit_disc = self.findByName("()"),
        };
    }

    // ── Internal helpers ─────────────────────────────────────────────

    /// Ensure list constructors ([] and (:)) are registered.
    fn ensureListConstructors(self: *TagRegistry, alloc: std.mem.Allocator) !void {
        if (self.con_name_to_disc.get("[]") == null) {
            const nil_tag = grin.Tag{
                .tag_type = .Con,
                .name = .{ .base = "[]", .unique = .{ .value = known.nil_val } },
            };
            try self.register(alloc, nil_tag, 0);
        }
        if (self.con_name_to_disc.get("(:)") == null) {
            const cons_tag = grin.Tag{
                .tag_type = .Con,
                .name = .{ .base = "(:)", .unique = .{ .value = known.cons_val } },
            };
            try self.register(alloc, cons_tag, 2);
        }
    }

    /// Ensure intermediate partial tags exist for the apply function.
    fn registerIntermediatePartialTags(self: *TagRegistry, alloc: std.mem.Allocator) !void {
        var to_add = std.ArrayListUnmanaged(struct { tag: grin.Tag, n_fields: u32 }){};
        defer to_add.deinit(alloc);

        var iter = self.partial_tag_info.iterator();
        while (iter.next()) |entry| {
            const info = entry.value_ptr.*;
            if (info.missing > 1) {
                const new_tag = grin.Tag{
                    .tag_type = .{ .Partial = info.missing - 1 },
                    .name = info.name,
                };
                try to_add.append(alloc, .{ .tag = new_tag, .n_fields = info.n_fields + 1 });
            }
        }
        for (to_add.items) |item| {
            try self.register(alloc, item.tag, item.n_fields);
        }
    }

    // ── Key encoding ─────────────────────────────────────────────────

    /// Compute a composite key that distinguishes tag types sharing
    /// the same name unique.
    ///
    /// Encoding:
    ///   Con:        unique * 4
    ///   Fun:        unique * 4 + 1
    ///   Partial(n): (unique * 4 + 2) * 31 + n
    pub fn tagKey(tag: grin.Tag) u64 {
        const base = tag.name.unique.value;
        return switch (tag.tag_type) {
            .Con => base *% 4,
            .Fun => base *% 4 +% 1,
            .Partial => |n| (base *% 4 +% 2) *% 31 +% @as(u64, n),
        };
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Body Scanning
// ═══════════════════════════════════════════════════════════════════════

/// Recursively scan a GRIN expression for constructor/function tags
/// and register them in the registry.
pub fn scanExprForTags(alloc: std.mem.Allocator, expr: *const grin.Expr, registry: *TagRegistry) !void {
    switch (expr.*) {
        .Return => |v| try scanValForTags(alloc, v, registry),
        .Store => |v| try scanValForTags(alloc, v, registry),
        .App => |a| for (a.args) |arg| try scanValForTags(alloc, arg, registry),
        .Bind => |b| {
            try scanExprForTags(alloc, b.lhs, registry);
            try scanValForTags(alloc, b.pat, registry);
            try scanExprForTags(alloc, b.rhs, registry);
        },
        .Case => |k| {
            try scanValForTags(alloc, k.scrutinee, registry);
            for (k.alts) |alt| {
                switch (alt.pat) {
                    .NodePat => |np| try registry.register(alloc, np.tag, @intCast(np.fields.len)),
                    .TagPat => |t| try registry.register(alloc, t, 0),
                    else => {},
                }
                try scanExprForTags(alloc, alt.body, registry);
            }
        },
        .Update => |u| try scanValForTags(alloc, u.val, registry),
        .Fetch => {},
        .Block => |inner| try scanExprForTags(alloc, inner, registry),
    }
}

fn scanValForTags(alloc: std.mem.Allocator, val: grin.Val, registry: *TagRegistry) !void {
    switch (val) {
        .ConstTagNode => |ctn| {
            try registry.register(alloc, ctn.tag, @intCast(ctn.fields.len));
            for (ctn.fields) |f| try scanValForTags(alloc, f, registry);
        },
        .ValTag => |t| try registry.register(alloc, t, 0),
        .VarTagNode => |vtn| for (vtn.fields) |f| try scanValForTags(alloc, f, registry),
        .Var => {},
        .Lit => {},
        .Unit => {},
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Convenience: build a registry from a complete program
// ═══════════════════════════════════════════════════════════════════════

/// Create a fully-populated registry from a GRIN program.
/// Convenience for the batch compiler path.
pub fn buildRegistry(alloc: std.mem.Allocator, program: grin.Program) !TagRegistry {
    var registry = TagRegistry.init();
    errdefer registry.deinit(alloc);
    try registry.registerDefsAndBodies(alloc, program.defs);
    try registry.registerFieldTypes(alloc, program.field_types);
    return registry;
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

const testing = std.testing;

test "TagRegistry: register and discriminant" {
    var reg = TagRegistry.init();
    defer reg.deinit(testing.allocator);

    const tag_a = grin.Tag{
        .tag_type = .Con,
        .name = .{ .base = "A", .unique = .{ .value = 1 } },
    };
    try reg.register(testing.allocator, tag_a, 2);

    try testing.expectEqual(@as(i64, 0x1000), reg.discriminant(tag_a).?);
    try testing.expectEqual(@as(u32, 2), reg.fieldCount(tag_a).?);
}

test "TagRegistry: isNullaryByName" {
    var reg = TagRegistry.init();
    defer reg.deinit(testing.allocator);

    const tag_nil = grin.Tag{
        .tag_type = .Con,
        .name = .{ .base = "Nil", .unique = .{ .value = 10 } },
    };
    try reg.register(testing.allocator, tag_nil, 0);

    try testing.expect(reg.isNullaryByName(.{ .base = "Nil", .unique = .{ .value = 10 } }));
    try testing.expect(!reg.isNullaryByName(.{ .base = "Unknown", .unique = .{ .value = 99 } }));
}

test "TagRegistry: idempotent re-registration" {
    var reg = TagRegistry.init();
    defer reg.deinit(testing.allocator);

    const tag = grin.Tag{
        .tag_type = .Con,
        .name = .{ .base = "X", .unique = .{ .value = 5 } },
    };
    try reg.register(testing.allocator, tag, 1);
    const disc1 = reg.discriminant(tag).?;

    // Re-register — should be a no-op.
    try reg.register(testing.allocator, tag, 1);
    try testing.expectEqual(disc1, reg.discriminant(tag).?);
}

test "TagRegistry: composite keying distinguishes Con, Fun, and Partial tags" {
    var reg = TagRegistry.init();
    defer reg.deinit(testing.allocator);

    const name = grin.Name{ .base = "foo", .unique = .{ .value = 5 } };

    const con_tag = grin.Tag{ .tag_type = .Con, .name = name };
    const fun_tag = grin.Tag{ .tag_type = .Fun, .name = name };
    const par_tag = grin.Tag{ .tag_type = .{ .Partial = 2 }, .name = name };

    try reg.register(testing.allocator, con_tag, 0);
    try reg.register(testing.allocator, fun_tag, 1);
    try reg.register(testing.allocator, par_tag, 3);

    const disc_con = reg.discriminant(con_tag).?;
    const disc_fun = reg.discriminant(fun_tag).?;
    const disc_par = reg.discriminant(par_tag).?;

    // All three must have distinct discriminants.
    try testing.expect(disc_con != disc_fun);
    try testing.expect(disc_con != disc_par);
    try testing.expect(disc_fun != disc_par);

    // Verify composite keys are different.
    try testing.expect(TagRegistry.tagKey(con_tag) != TagRegistry.tagKey(fun_tag));
    try testing.expect(TagRegistry.tagKey(con_tag) != TagRegistry.tagKey(par_tag));
    try testing.expect(TagRegistry.tagKey(fun_tag) != TagRegistry.tagKey(par_tag));
}

test "TagRegistry: P(1) and P(2) get distinct discriminants" {
    var reg = TagRegistry.init();
    defer reg.deinit(testing.allocator);

    const name = grin.Name{ .base = "bar", .unique = .{ .value = 7 } };
    const p1 = grin.Tag{ .tag_type = .{ .Partial = 1 }, .name = name };
    const p2 = grin.Tag{ .tag_type = .{ .Partial = 2 }, .name = name };

    try reg.register(testing.allocator, p1, 2);
    try reg.register(testing.allocator, p2, 1);

    try testing.expect(reg.discriminant(p1).? != reg.discriminant(p2).?);
    try testing.expect(TagRegistry.tagKey(p1) != TagRegistry.tagKey(p2));
}

test "TagRegistry: registerIntermediatePartialTags creates P(n-1) from P(n)" {
    var reg = TagRegistry.init();
    defer reg.deinit(testing.allocator);

    const name = grin.Name{ .base = "baz", .unique = .{ .value = 9 } };
    const p3 = grin.Tag{ .tag_type = .{ .Partial = 3 }, .name = name };
    try reg.register(testing.allocator, p3, 1);
    try testing.expectEqual(@as(u32, 1), reg.partial_tags.count());

    // First round: P(3) → P(2) created.
    try reg.registerIntermediatePartialTags(testing.allocator);
    try testing.expectEqual(@as(u32, 2), reg.partial_tags.count());

    // Second round: P(2) → P(1) created.
    try reg.registerIntermediatePartialTags(testing.allocator);
    try testing.expectEqual(@as(u32, 3), reg.partial_tags.count());

    // Third round: P(1) — no more intermediates.
    try reg.registerIntermediatePartialTags(testing.allocator);
    try testing.expectEqual(@as(u32, 3), reg.partial_tags.count());
}

test "TagRegistry: getKnownDiscriminants" {
    var reg = TagRegistry.init();
    defer reg.deinit(testing.allocator);

    const true_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "True", .unique = .{ .value = 200 } } };
    const nil_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "[]", .unique = .{ .value = 207 } } };
    try reg.register(testing.allocator, true_tag, 0);
    try reg.register(testing.allocator, nil_tag, 0);

    const kt = reg.getKnownDiscriminants();
    try testing.expect(kt.true_disc != null);
    try testing.expect(kt.nil_disc != null);
    try testing.expect(kt.false_disc == null); // not registered
}

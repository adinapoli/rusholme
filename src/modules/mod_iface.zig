//! Module interface representation (`ModIface`) and `.rhi` serialisation.
//!
//! When module A imports module B, the compiler needs to know B's exported
//! names, their types, and their data constructors — without re-parsing or
//! re-typechecking B's source.  `ModIface` captures exactly this information
//! and can be persisted as a `.rhi` (Rusholme Interface) file.
//!
//! ## Pipeline position
//!
//! ```
//! Source → Parse → Rename → Typecheck → Desugar → Core
//!                                                     │
//!                                                     └─► buildModIface
//!                                                               │
//!                                                         writeRhi → <Module.rhi>
//! ```
//!
//! A downstream module calls `readRhi` to recover the `ModIface` and feeds it
//! into the renamer / typechecker as if the symbols were defined locally.
//!
//! ## Serialisation format
//!
//! The `.rhi` format is JSON (human-readable, debuggable).  Binary serialisation
//! is explicitly deferred to a follow-up issue once the format stabilises.
//!
//! ## Scope
//!
//! This is the M2 foundation for the module system (#365).  Known limitations
//! introduced here:
//!
//! - Re-exports (`module Foo (module Bar)`) are recorded in `ExportSpec` but not
//!   yet expanded; a downstream consumer must load Bar's interface separately.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/368
//!
//! - Type-class instances are not yet included in `ModIface`.  Adding them
//!   requires the full class/instance infrastructure (#60).
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/369
//!
//! ## References
//!
//! - Haskell 2010 Report §5.2 (Export Lists)
//! - GHC `GHC.Iface.Syntax.ModIface` (design inspiration, not format)

const std = @import("std");
const core = @import("../core/ast.zig");
const naming = @import("../naming/unique.zig");
const htype_mod = @import("../typechecker/htype.zig");
const infer_mod = @import("../typechecker/infer.zig");
const ast = @import("../frontend/ast.zig");

pub const Name = naming.Name;
pub const Unique = naming.Unique;
pub const CoreType = core.CoreType;
pub const TyScheme = htype_mod.TyScheme;
pub const ModuleTypes = infer_mod.ModuleTypes;
pub const CoreProgram = core.CoreProgram;
pub const ExportSpec = ast.ExportSpec;

// ── Serialisable CoreType ───────────────────────────────────────────────
//
// `core.ast.CoreType` uses pointer-based recursive types (FunTy, ForAllTy)
// and the `Name` struct (base + unique).  We flatten this into a set of
// JSON-friendly structs that `std.json` can round-trip without custom logic.
//
// Tag variants:
//   "TyVar"   → { "tag": "TyVar",    "name": "<base>", "unique": <u64> }
//   "TyCon"   → { "tag": "TyCon",    "name": "<base>", "unique": <u64>, "args": [...] }
//   "FunTy"   → { "tag": "FunTy",    "arg": <SerialisedCoreType>, "res": <SerialisedCoreType> }
//   "ForAllTy"→ { "tag": "ForAllTy", "binder_name": "<base>", "binder_unique": <u64>,
//                                     "body": <SerialisedCoreType> }
//
// We represent the tagged union as a `struct` with a `tag` discriminant
// and optional fields; this is the idiomatic approach for JSON unions in
// Zig without writing a custom serialiser.

/// A JSON-serialisable representation of `core.ast.CoreType`.
///
/// `alloc` must outlive any slice fields produced by `fromCoreType`.
pub const SerialisedCoreType = struct {
    tag: []const u8,

    // TyVar / TyCon: the constructor name.
    name: ?[]const u8 = null,
    unique: ?u64 = null,

    // TyCon: type arguments.
    args: ?[]const SerialisedCoreType = null,

    // FunTy: argument and result types.
    arg: ?*const SerialisedCoreType = null,
    res: ?*const SerialisedCoreType = null,

    // ForAllTy: binder name/unique and body.
    binder_name: ?[]const u8 = null,
    binder_unique: ?u64 = null,
    body: ?*const SerialisedCoreType = null,

    // ── Conversions ─────────────────────────────────────────────────────

    /// Convert a `CoreType` to its serialisable form.  All allocations go
    /// into `alloc` (expected to be an arena).
    pub fn fromCoreType(ty: CoreType, alloc: std.mem.Allocator) std.mem.Allocator.Error!SerialisedCoreType {
        switch (ty) {
            .TyVar => |n| return .{
                .tag = "TyVar",
                .name = n.base,
                .unique = n.unique.value,
            },

            .TyCon => |tc| {
                const s_args = try alloc.alloc(SerialisedCoreType, tc.args.len);
                for (tc.args, 0..) |a, i| {
                    s_args[i] = try fromCoreType(a, alloc);
                }
                return .{
                    .tag = "TyCon",
                    .name = tc.name.base,
                    .unique = tc.name.unique.value,
                    .args = s_args,
                };
            },

            .FunTy => |ft| {
                const s_arg = try alloc.create(SerialisedCoreType);
                s_arg.* = try fromCoreType(ft.arg.*, alloc);
                const s_res = try alloc.create(SerialisedCoreType);
                s_res.* = try fromCoreType(ft.res.*, alloc);
                return .{
                    .tag = "FunTy",
                    .arg = s_arg,
                    .res = s_res,
                };
            },

            .ForAllTy => |fa| {
                const s_body = try alloc.create(SerialisedCoreType);
                s_body.* = try fromCoreType(fa.body.*, alloc);
                return .{
                    .tag = "ForAllTy",
                    .binder_name = fa.binder.base,
                    .binder_unique = fa.binder.unique.value,
                    .body = s_body,
                };
            },
        }
    }

    /// Reconstruct a `CoreType` from its serialisable form.  All allocations
    /// go into `alloc`.
    pub fn toCoreType(self: SerialisedCoreType, alloc: std.mem.Allocator) std.mem.Allocator.Error!CoreType {
        if (std.mem.eql(u8, self.tag, "TyVar")) {
            return CoreType{ .TyVar = .{
                .base = self.name.?,
                .unique = .{ .value = self.unique.? },
            } };
        }
        if (std.mem.eql(u8, self.tag, "TyCon")) {
            const raw_args = self.args orelse &.{};
            const core_args = try alloc.alloc(CoreType, raw_args.len);
            for (raw_args, 0..) |a, i| {
                core_args[i] = try a.toCoreType(alloc);
            }
            return CoreType{ .TyCon = .{
                .name = .{
                    .base = self.name.?,
                    .unique = .{ .value = self.unique.? },
                },
                .args = core_args,
            } };
        }
        if (std.mem.eql(u8, self.tag, "FunTy")) {
            const arg_ct = try alloc.create(CoreType);
            arg_ct.* = try self.arg.?.toCoreType(alloc);
            const res_ct = try alloc.create(CoreType);
            res_ct.* = try self.res.?.toCoreType(alloc);
            return CoreType{ .FunTy = .{ .arg = arg_ct, .res = res_ct } };
        }
        if (std.mem.eql(u8, self.tag, "ForAllTy")) {
            const body_ct = try alloc.create(CoreType);
            body_ct.* = try self.body.?.toCoreType(alloc);
            return CoreType{ .ForAllTy = .{
                .binder = .{
                    .base = self.binder_name.?,
                    .unique = .{ .value = self.binder_unique.? },
                },
                .body = body_ct,
            } };
        }
        @panic("SerialisedCoreType.toCoreType: unknown tag");
    }
};

// ── SerialisedScheme ────────────────────────────────────────────────────

/// A JSON-serialisable type scheme: `forall b0 b1 … . body`.
///
/// `binder_uniques` holds the unique IDs of the universally-quantified
/// rigid variables (matching `TyScheme.binders`).
pub const SerialisedScheme = struct {
    /// Unique IDs of the `forall`-bound rigid variables.
    binder_uniques: []const u64,
    /// Base names of the `forall`-bound rigid variables (parallel to binder_uniques).
    binder_names: []const []const u8,
    /// The body type.
    body: SerialisedCoreType,
};

// ── ExportedValue ────────────────────────────────────────────────────────

/// A top-level value exported by a module: its source name, unique ID,
/// and generalised type scheme.
pub const ExportedValue = struct {
    /// Source-level name (e.g. `"map"`, `"foldr"`).
    name: []const u8,
    /// Unique ID assigned by the renamer.
    unique: u64,
    /// Type scheme (serialised form of `TyScheme`).
    scheme: SerialisedScheme,
};

// ── DataCon ──────────────────────────────────────────────────────────────

/// A data constructor exported by a module.
pub const DataCon = struct {
    /// Source-level constructor name (e.g. `"Just"`, `"Nothing"`).
    name: []const u8,
    /// Unique ID assigned by the renamer.
    unique: u64,
    /// The constructor's monomorphic type (under the data declaration's foralls).
    ty: SerialisedCoreType,
};

// ── ExportedDataDecl ─────────────────────────────────────────────────────

/// A data type declaration exported by a module.
pub const ExportedDataDecl = struct {
    /// Type constructor name (e.g. `"Maybe"`, `"List"`).
    name: []const u8,
    /// Unique ID of the type constructor.
    unique: u64,
    /// Type variable binder names (e.g. `["a"]` for `data Maybe a = …`).
    tyvar_names: []const []const u8,
    /// Unique IDs of the type variables (parallel to `tyvar_names`).
    tyvar_uniques: []const u64,
    /// Exported data constructors.
    constructors: []const DataCon,
};

// ── ModIface ─────────────────────────────────────────────────────────────

/// The complete interface for a compiled Rusholme module.
///
/// This is the data structure written to `.rhi` files and loaded when a
/// downstream module imports this one.  It is intentionally a pure
/// data struct (no allocator field, no vtable) — all memory is arena-owned
/// and the struct can be freely copied.
pub const ModIface = struct {
    /// The module's fully-qualified name (e.g. `"Data.Map"`, `"Main"`).
    module_name: []const u8,
    /// Exported value bindings (functions, constants).
    values: []const ExportedValue,
    /// Exported data type declarations.
    data_decls: []const ExportedDataDecl,
    // ── Not yet implemented ─────────────────────────────────────────────
    //
    // Exported type class instances are not yet included.
    // Tracked in: https://github.com/adinapoli/rusholme/issues/369
    //
    // Re-export expansion (module Foo (module Bar)) is not yet performed.
    // Tracked in: https://github.com/adinapoli/rusholme/issues/368
};

// ── buildModIface ────────────────────────────────────────────────────────

/// Build a `ModIface` from the compiler's post-Core outputs.
///
/// `alloc` must outlive the returned `ModIface` (use an arena).
///
/// `module_name` is the fully-qualified module name (e.g. `"Main"`).
///
/// `export_list` is the parsed export spec from the module header, or `null`
/// if the module exports everything (the default).  When non-null, only names
/// appearing in `export_list` are included.
///
/// `core_prog` is the desugared Core program for this module.
///
/// `module_types` is the typechecker's output: a map from name unique to
/// `TyScheme` (still as `HType`; we call `toCore` to resolve metavars).
pub fn buildModIface(
    alloc: std.mem.Allocator,
    module_name: []const u8,
    export_list: ?[]const ExportSpec,
    core_prog: CoreProgram,
    module_types: *const ModuleTypes,
) std.mem.Allocator.Error!ModIface {
    // ── Collect exported value bindings ─────────────────────────────────
    var values: std.ArrayListUnmanaged(ExportedValue) = .{};

    for (core_prog.binds) |bind| {
        switch (bind) {
            .NonRec => |bp| {
                if (!isValueExported(bp.binder.name, export_list)) continue;
                const ev = try buildExportedValue(alloc, bp.binder.name, module_types) orelse continue;
                try values.append(alloc, ev);
            },
            .Rec => |pairs| {
                for (pairs) |bp| {
                    if (!isValueExported(bp.binder.name, export_list)) continue;
                    const ev = try buildExportedValue(alloc, bp.binder.name, module_types) orelse continue;
                    try values.append(alloc, ev);
                }
            },
        }
    }

    // ── Collect exported data declarations ──────────────────────────────
    var data_decls: std.ArrayListUnmanaged(ExportedDataDecl) = .{};

    for (core_prog.data_decls) |dd| {
        if (!isTypeExported(dd.name, export_list)) continue;

        // Collect data constructors.
        var cons: std.ArrayListUnmanaged(DataCon) = .{};
        for (dd.constructors) |con| {
            // Only include constructors that are also exported.
            // When the export spec lists `T(..)`, all constructors are
            // included; when it lists `T` alone, none are.  We conservatively
            // include all constructors when the type is exported and the export
            // spec either exports everything or uses `T(..)`.
            if (!isConExported(con.name, dd.name, export_list)) continue;
            const s_ty = try SerialisedCoreType.fromCoreType(con.ty, alloc);
            try cons.append(alloc, .{
                .name = con.name.base,
                .unique = con.name.unique.value,
                .ty = s_ty,
            });
        }

        // Collect type variable binders.
        const tyvar_names = try alloc.alloc([]const u8, dd.tyvars.len);
        const tyvar_uniques = try alloc.alloc(u64, dd.tyvars.len);
        for (dd.tyvars, 0..) |tv, i| {
            tyvar_names[i] = tv.base;
            tyvar_uniques[i] = tv.unique.value;
        }

        try data_decls.append(alloc, .{
            .name = dd.name.base,
            .unique = dd.name.unique.value,
            .tyvar_names = tyvar_names,
            .tyvar_uniques = tyvar_uniques,
            .constructors = try cons.toOwnedSlice(alloc),
        });
    }

    return ModIface{
        .module_name = module_name,
        .values = try values.toOwnedSlice(alloc),
        .data_decls = try data_decls.toOwnedSlice(alloc),
    };
}

/// Build an `ExportedValue` for a single binder, looking up its scheme
/// in `module_types`.  Returns `null` if the scheme is not found (e.g. a
/// generated binder that the typechecker did not assign a scheme to).
fn buildExportedValue(
    alloc: std.mem.Allocator,
    name: Name,
    module_types: *const ModuleTypes,
) std.mem.Allocator.Error!?ExportedValue {
    const scheme = module_types.get(name.unique) orelse return null;

    // Convert HType binders → unique ID array.
    const binder_uniques = try alloc.dupe(u64, scheme.binders);

    // Build parallel names array.  Binders in TyScheme are stored as
    // `u64` unique IDs; to get the base name we look into the body for
    // the first `Rigid` with that ID.  For now we synthesise a name
    // `_tv<id>` as a placeholder — the base name is advisory only.
    const binder_names = try alloc.alloc([]const u8, scheme.binders.len);
    for (scheme.binders, 0..) |uid, i| {
        binder_names[i] = try rigidNameFromBody(scheme.body, uid, alloc);
    }

    // Convert the HType body to CoreType.
    const core_ty = try scheme.body.toCore(alloc);
    const s_body = try SerialisedCoreType.fromCoreType(core_ty, alloc);

    return ExportedValue{
        .name = name.base,
        .unique = name.unique.value,
        .scheme = .{
            .binder_uniques = binder_uniques,
            .binder_names = binder_names,
            .body = s_body,
        },
    };
}

/// Search `ty` for a `Rigid` node with unique `id` and return its base name.
/// Falls back to `_tv<id>` if not found.
fn rigidNameFromBody(ty: htype_mod.HType, id: u64, alloc: std.mem.Allocator) std.mem.Allocator.Error![]const u8 {
    switch (ty) {
        .Rigid => |n| if (n.unique.value == id) return n.base,
        .Con => |c| {
            for (c.args) |a| {
                const found = try rigidNameFromBody(a, id, alloc);
                if (!std.mem.startsWith(u8, found, "_tv")) return found;
            }
        },
        .Fun => |f| {
            const in_arg = try rigidNameFromBody(f.arg.*, id, alloc);
            if (!std.mem.startsWith(u8, in_arg, "_tv")) return in_arg;
            return rigidNameFromBody(f.res.*, id, alloc);
        },
        .ForAll => |fa| return rigidNameFromBody(fa.body.*, id, alloc),
        .AppTy => |at| {
            const in_head = try rigidNameFromBody(at.head.*, id, alloc);
            if (!std.mem.startsWith(u8, in_head, "_tv")) return in_head;
            return rigidNameFromBody(at.arg.*, id, alloc);
        },
        .Meta => |mv| if (mv.ref) |next| return rigidNameFromBody(next.*, id, alloc),
    }
    // Not found — synthesise a placeholder.
    return std.fmt.allocPrint(alloc, "_tv{d}", .{id});
}

// ── Export list filtering ────────────────────────────────────────────────

/// Returns `true` if the value `name` should be included in the interface.
///
/// - When `export_list` is `null`, all names are exported (default).
/// - Otherwise, only names listed in an `ExportSpec.Var` or `ExportSpec.Con`
///   entry are included.
fn isValueExported(name: Name, export_list: ?[]const ExportSpec) bool {
    const list = export_list orelse return true; // export everything
    for (list) |spec| {
        switch (spec) {
            .Var => |v| if (std.mem.eql(u8, v, name.base)) return true,
            .Con => |c| if (std.mem.eql(u8, c, name.base)) return true,
            else => {},
        }
    }
    return false;
}

/// Returns `true` if the type constructor `name` should appear in the interface.
fn isTypeExported(name: Name, export_list: ?[]const ExportSpec) bool {
    const list = export_list orelse return true;
    for (list) |spec| {
        switch (spec) {
            .Type => |ts| if (std.mem.eql(u8, ts.name, name.base)) return true,
            // Modules re-exported via `module Foo` are resolved separately.
            // Tracked in: https://github.com/adinapoli/rusholme/issues/368
            .Module => {},
            else => {},
        }
    }
    return false;
}

/// Returns `true` if the data constructor `con_name` belonging to type
/// `type_name` should be included in the interface.
///
/// Rules (Haskell 2010 §5.2):
/// - `export_list == null` → export all constructors.
/// - `T(..)` in the export list → export all constructors of T.
/// - `T` in the export list → export the type but NO constructors.
fn isConExported(con_name: Name, type_name: Name, export_list: ?[]const ExportSpec) bool {
    const list = export_list orelse return true;
    for (list) |spec| {
        switch (spec) {
            .Type => |ts| {
                if (std.mem.eql(u8, ts.name, type_name.base)) {
                    return ts.with_constructors;
                }
            },
            .Con => |c| if (std.mem.eql(u8, c, con_name.base)) return true,
            else => {},
        }
    }
    return false;
}

// ── Serialisation (.rhi write) ──────────────────────────────────────────

/// Serialise a `ModIface` to its JSON `.rhi` representation.
///
/// Returns a heap-allocated string (caller owns, must free with `alloc`).
pub fn writeRhi(alloc: std.mem.Allocator, iface: ModIface) std.mem.Allocator.Error![]u8 {
    return std.json.Stringify.valueAlloc(alloc, iface, .{ .whitespace = .indent_2 });
}

// ── Deserialisation (.rhi read) ──────────────────────────────────────────

/// The error set for `.rhi` reading.
pub const ReadRhiError = std.mem.Allocator.Error || std.json.ParseError(std.json.Scanner);

/// Deserialise a `ModIface` from its JSON `.rhi` representation.
///
/// All memory for the returned `ModIface` is allocated via `alloc`; the
/// caller is responsible for freeing it (or using an arena that outlives
/// the `ModIface`).
///
/// `data` is the raw UTF-8 JSON content of the `.rhi` file.
pub fn readRhi(alloc: std.mem.Allocator, data: []const u8) ReadRhiError!ModIface {
    const parsed = try std.json.parseFromSlice(ModIface, alloc, data, .{
        .allocate = .alloc_always,
    });
    defer parsed.deinit();

    // Deep-copy the parsed value into `alloc` so that it survives after we
    // call `parsed.deinit()`.  `std.json.parseFromSlice` owns its arena; we
    // must not return pointers into it.
    return try deepCopyModIface(alloc, parsed.value);
}

/// Deep-copy a `ModIface` into `alloc`.  Needed because `std.json`'s parsed
/// value lives in an internal arena that is freed with the `Parsed` handle.
fn deepCopyModIface(alloc: std.mem.Allocator, src: ModIface) std.mem.Allocator.Error!ModIface {
    const module_name = try alloc.dupe(u8, src.module_name);

    const values = try alloc.alloc(ExportedValue, src.values.len);
    for (src.values, 0..) |v, i| {
        values[i] = try deepCopyExportedValue(alloc, v);
    }

    const data_decls = try alloc.alloc(ExportedDataDecl, src.data_decls.len);
    for (src.data_decls, 0..) |dd, i| {
        data_decls[i] = try deepCopyExportedDataDecl(alloc, dd);
    }

    return ModIface{
        .module_name = module_name,
        .values = values,
        .data_decls = data_decls,
    };
}

fn deepCopyExportedValue(alloc: std.mem.Allocator, src: ExportedValue) std.mem.Allocator.Error!ExportedValue {
    const binder_uniques = try alloc.dupe(u64, src.scheme.binder_uniques);
    const binder_names = try alloc.alloc([]const u8, src.scheme.binder_names.len);
    for (src.scheme.binder_names, 0..) |n, i| {
        binder_names[i] = try alloc.dupe(u8, n);
    }
    const body = try deepCopySerialisedCoreType(alloc, src.scheme.body);
    return ExportedValue{
        .name = try alloc.dupe(u8, src.name),
        .unique = src.unique,
        .scheme = .{
            .binder_uniques = binder_uniques,
            .binder_names = binder_names,
            .body = body,
        },
    };
}

fn deepCopyExportedDataDecl(alloc: std.mem.Allocator, src: ExportedDataDecl) std.mem.Allocator.Error!ExportedDataDecl {
    const tyvar_names = try alloc.alloc([]const u8, src.tyvar_names.len);
    for (src.tyvar_names, 0..) |n, i| {
        tyvar_names[i] = try alloc.dupe(u8, n);
    }
    const tyvar_uniques = try alloc.dupe(u64, src.tyvar_uniques);

    const cons = try alloc.alloc(DataCon, src.constructors.len);
    for (src.constructors, 0..) |c, i| {
        cons[i] = .{
            .name = try alloc.dupe(u8, c.name),
            .unique = c.unique,
            .ty = try deepCopySerialisedCoreType(alloc, c.ty),
        };
    }

    return ExportedDataDecl{
        .name = try alloc.dupe(u8, src.name),
        .unique = src.unique,
        .tyvar_names = tyvar_names,
        .tyvar_uniques = tyvar_uniques,
        .constructors = cons,
    };
}

fn deepCopySerialisedCoreType(alloc: std.mem.Allocator, src: SerialisedCoreType) std.mem.Allocator.Error!SerialisedCoreType {
    var result = SerialisedCoreType{
        .tag = try alloc.dupe(u8, src.tag),
    };
    if (src.name) |n| result.name = try alloc.dupe(u8, n);
    result.unique = src.unique;

    if (src.args) |arr| {
        const copied = try alloc.alloc(SerialisedCoreType, arr.len);
        for (arr, 0..) |a, i| {
            copied[i] = try deepCopySerialisedCoreType(alloc, a);
        }
        result.args = copied;
    }

    if (src.arg) |p| {
        const copied = try alloc.create(SerialisedCoreType);
        copied.* = try deepCopySerialisedCoreType(alloc, p.*);
        result.arg = copied;
    }
    if (src.res) |p| {
        const copied = try alloc.create(SerialisedCoreType);
        copied.* = try deepCopySerialisedCoreType(alloc, p.*);
        result.res = copied;
    }
    if (src.binder_name) |n| result.binder_name = try alloc.dupe(u8, n);
    result.binder_unique = src.binder_unique;
    if (src.body) |p| {
        const copied = try alloc.create(SerialisedCoreType);
        copied.* = try deepCopySerialisedCoreType(alloc, p.*);
        result.body = copied;
    }

    return result;
}

// ── Tests ─────────────────────────────────────────────────────────────────

const testing = std.testing;

// ── Test helpers ─────────────────────────────────────────────────────────

fn testName(base: []const u8, id: u64) Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

fn intCoreTy() CoreType {
    return .{ .TyCon = .{ .name = testName("Int", 1), .args = &.{} } };
}

fn funCoreTy(arg: CoreType, res: CoreType, alloc: std.mem.Allocator) !CoreType {
    const a = try alloc.create(CoreType);
    a.* = arg;
    const r = try alloc.create(CoreType);
    r.* = res;
    return CoreType{ .FunTy = .{ .arg = a, .res = r } };
}

// ── SerialisedCoreType round-trip ─────────────────────────────────────────

test "SerialisedCoreType: TyCon round-trip" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const original = intCoreTy();
    const serialised = try SerialisedCoreType.fromCoreType(original, alloc);
    const recovered = try serialised.toCoreType(alloc);

    try testing.expectEqualStrings("Int", recovered.TyCon.name.base);
    try testing.expectEqual(@as(u64, 1), recovered.TyCon.name.unique.value);
    try testing.expectEqual(@as(usize, 0), recovered.TyCon.args.len);
}

test "SerialisedCoreType: TyVar round-trip" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const original = CoreType{ .TyVar = testName("a", 42) };
    const serialised = try SerialisedCoreType.fromCoreType(original, alloc);
    const recovered = try serialised.toCoreType(alloc);

    try testing.expectEqualStrings("a", recovered.TyVar.base);
    try testing.expectEqual(@as(u64, 42), recovered.TyVar.unique.value);
}

test "SerialisedCoreType: FunTy round-trip" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const original = try funCoreTy(intCoreTy(), intCoreTy(), alloc);
    const serialised = try SerialisedCoreType.fromCoreType(original, alloc);
    const recovered = try serialised.toCoreType(alloc);

    try testing.expectEqualStrings("FunTy", serialised.tag);
    try testing.expectEqualStrings("Int", recovered.FunTy.arg.TyCon.name.base);
    try testing.expectEqualStrings("Int", recovered.FunTy.res.TyCon.name.base);
}

test "SerialisedCoreType: ForAllTy round-trip" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const body = CoreType{ .TyVar = testName("a", 5) };
    const body_ptr = try alloc.create(CoreType);
    body_ptr.* = body;
    const original = CoreType{ .ForAllTy = .{ .binder = testName("a", 5), .body = body_ptr } };
    const serialised = try SerialisedCoreType.fromCoreType(original, alloc);
    const recovered = try serialised.toCoreType(alloc);

    try testing.expectEqualStrings("a", recovered.ForAllTy.binder.base);
    try testing.expectEqualStrings("a", recovered.ForAllTy.body.TyVar.base);
}

// ── Export list filtering ─────────────────────────────────────────────────

test "isValueExported: null export list exports everything" {
    const n = testName("foo", 10);
    try testing.expect(isValueExported(n, null));
}

test "isValueExported: named export list" {
    const specs = [_]ExportSpec{
        .{ .Var = "foo" },
        .{ .Var = "bar" },
    };
    try testing.expect(isValueExported(testName("foo", 10), &specs));
    try testing.expect(isValueExported(testName("bar", 11), &specs));
    try testing.expect(!isValueExported(testName("baz", 12), &specs));
}

test "isTypeExported: type with constructors" {
    const specs = [_]ExportSpec{
        .{ .Type = .{ .name = "Maybe", .with_constructors = true } },
    };
    try testing.expect(isTypeExported(testName("Maybe", 20), &specs));
    try testing.expect(!isTypeExported(testName("Either", 21), &specs));
}

test "isConExported: T(..) exports constructors" {
    const specs = [_]ExportSpec{
        .{ .Type = .{ .name = "Maybe", .with_constructors = true } },
    };
    try testing.expect(isConExported(testName("Just", 30), testName("Maybe", 20), &specs));
    try testing.expect(isConExported(testName("Nothing", 31), testName("Maybe", 20), &specs));
}

test "isConExported: T without (..) does not export constructors" {
    const specs = [_]ExportSpec{
        .{ .Type = .{ .name = "Maybe", .with_constructors = false } },
    };
    try testing.expect(!isConExported(testName("Just", 30), testName("Maybe", 20), &specs));
    try testing.expect(!isConExported(testName("Nothing", 31), testName("Maybe", 20), &specs));
}

// ── ModIface JSON round-trip ───────────────────────────────────────────────

test "ModIface: writeRhi / readRhi round-trip (empty module)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const original = ModIface{
        .module_name = "Main",
        .values = &.{},
        .data_decls = &.{},
    };

    const json = try writeRhi(alloc, original);
    const recovered = try readRhi(alloc, json);

    try testing.expectEqualStrings("Main", recovered.module_name);
    try testing.expectEqual(@as(usize, 0), recovered.values.len);
    try testing.expectEqual(@as(usize, 0), recovered.data_decls.len);
}

test "ModIface: writeRhi / readRhi round-trip (value binding)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Represent `id :: forall a. a -> a`.
    const body_ty = CoreType{ .TyVar = testName("a", 5) };
    const body_ptr = try alloc.create(CoreType);
    body_ptr.* = body_ty;
    const forall_ty = CoreType{ .ForAllTy = .{ .binder = testName("a", 5), .body = body_ptr } };
    const s_body = try SerialisedCoreType.fromCoreType(forall_ty, alloc);

    const original = ModIface{
        .module_name = "Prelude",
        .values = &.{.{
            .name = "id",
            .unique = 42,
            .scheme = .{
                .binder_uniques = &.{5},
                .binder_names = &.{"a"},
                .body = s_body,
            },
        }},
        .data_decls = &.{},
    };

    const json = try writeRhi(alloc, original);
    const recovered = try readRhi(alloc, json);

    try testing.expectEqualStrings("Prelude", recovered.module_name);
    try testing.expectEqual(@as(usize, 1), recovered.values.len);
    try testing.expectEqualStrings("id", recovered.values[0].name);
    try testing.expectEqual(@as(u64, 42), recovered.values[0].unique);
    try testing.expectEqual(@as(usize, 1), recovered.values[0].scheme.binder_uniques.len);
    try testing.expectEqual(@as(u64, 5), recovered.values[0].scheme.binder_uniques[0]);
    try testing.expectEqualStrings("a", recovered.values[0].scheme.binder_names[0]);
    try testing.expectEqualStrings("ForAllTy", recovered.values[0].scheme.body.tag);
}

test "ModIface: writeRhi / readRhi round-trip (data declaration)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Represent `data Maybe a = Nothing | Just a`.
    //   Nothing :: Maybe a  (simplified as TyCon "Maybe" [TyVar "a"])
    //   Just :: a -> Maybe a
    const maybe_ty = CoreType{ .TyCon = .{
        .name = testName("Maybe", 20),
        .args = &.{CoreType{ .TyVar = testName("a", 5) }},
    } };
    const s_maybe = try SerialisedCoreType.fromCoreType(maybe_ty, alloc);

    const just_inner = try funCoreTy(CoreType{ .TyVar = testName("a", 5) }, maybe_ty, alloc);
    const s_just = try SerialisedCoreType.fromCoreType(just_inner, alloc);

    const original = ModIface{
        .module_name = "Data.Maybe",
        .values = &.{},
        .data_decls = &.{.{
            .name = "Maybe",
            .unique = 20,
            .tyvar_names = &.{"a"},
            .tyvar_uniques = &.{5},
            .constructors = &.{
                .{ .name = "Nothing", .unique = 30, .ty = s_maybe },
                .{ .name = "Just", .unique = 31, .ty = s_just },
            },
        }},
    };

    const json = try writeRhi(alloc, original);
    const recovered = try readRhi(alloc, json);

    try testing.expectEqualStrings("Data.Maybe", recovered.module_name);
    try testing.expectEqual(@as(usize, 1), recovered.data_decls.len);
    const dd = recovered.data_decls[0];
    try testing.expectEqualStrings("Maybe", dd.name);
    try testing.expectEqual(@as(u64, 20), dd.unique);
    try testing.expectEqual(@as(usize, 1), dd.tyvar_names.len);
    try testing.expectEqualStrings("a", dd.tyvar_names[0]);
    try testing.expectEqual(@as(usize, 2), dd.constructors.len);
    try testing.expectEqualStrings("Nothing", dd.constructors[0].name);
    try testing.expectEqualStrings("Just", dd.constructors[1].name);
}

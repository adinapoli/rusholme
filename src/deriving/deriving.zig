//! Deriving pass: synthesise `InstanceDecl` nodes for every `deriving`
//! clause on data/newtype declarations (and for every standalone
//! `DerivingDecl`) and append them to the module's declaration list.
//!
//! Runs between the parser and the renamer, so synthesised instances pass
//! through renaming and typechecking exactly as if the user had written
//! them by hand.
//!
//! Issue: https://github.com/adinapoli/rusholme/issues/679

const std = @import("std");
const ast = @import("../frontend/ast.zig");
const span_mod = @import("../diagnostics/span.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");

const shape_mod = @import("shape.zig");
const builder = @import("builder.zig");
const eq_mod = @import("eq.zig");
const ord_mod = @import("ord.zig");
const show_mod = @import("show.zig");
const bounded_mod = @import("bounded.zig");
const enum_mod = @import("enum_class.zig");

pub const SourceSpan = span_mod.SourceSpan;
pub const Allocator = std.mem.Allocator;
pub const DeriveError = error{OutOfMemory};

const StockClass = enum { eq, ord, show, bounded, enum_ };

const stock_classes = std.StaticStringMap(StockClass).initComptime(.{
    .{ "Eq", .eq },
    .{ "Ord", .ord },
    .{ "Show", .show },
    .{ "Bounded", .bounded },
    .{ "Enum", .enum_ },
});

/// Walk `module.declarations`, synthesise `InstanceDecl` nodes for every
/// `deriving` clause, and append them.  The pass mutates the module by
/// replacing the `declarations` slice with a freshly allocated one.
///
/// Synthesis errors are reported through `diags` but do not halt the pass —
/// every clause is processed so the user sees all problems in one compile.
pub fn derive(
    arena: Allocator,
    module: *ast.Module,
    diags: *diag_mod.DiagnosticCollector,
) DeriveError!void {
    var out: std.ArrayListUnmanaged(ast.Decl) = .empty;

    // Reset the occurrence-span counter so each synthesised class-method call
    // site gets a distinct span (required for correct dictionary-evidence
    // keying in the desugarer — see builder.occ_seq / #851).
    builder.resetOccurrenceSpans();

    // Synthesise instances inline, placing the helpers + instance
    // immediately after the data/newtype declaration that triggered them.
    // This keeps each type with its derived machinery together and matches
    // the declaration order a user would write by hand.
    for (module.declarations) |decl| {
        try out.append(arena, decl);
        switch (decl) {
            .Data => |d| {
                if (d.deriving.len == 0) continue;
                const norm = shape_mod.NormalizedDecl.fromData(d);
                try processDeriveList(arena, norm, d.deriving, d.span, diags, &out);
            },
            .Newtype => |n| {
                if (n.deriving.len == 0) continue;
                const norm = try shape_mod.NormalizedDecl.fromNewtype(arena, n);
                try processDeriveList(arena, norm, n.deriving, n.span, diags, &out);
            },
            .Deriving => |sd| {
                try processStandalone(arena, sd, module.*, diags, &out);
            },
            else => {},
        }
    }

    module.declarations = try out.toOwnedSlice(arena);
}

fn processDeriveList(
    arena: Allocator,
    decl: shape_mod.NormalizedDecl,
    classes: []const []const u8,
    span: SourceSpan,
    diags: *diag_mod.DiagnosticCollector,
    out: *std.ArrayListUnmanaged(ast.Decl),
) DeriveError!void {
    for (classes) |class_name| {
        const r = synthOne(arena, decl, class_name, span, diags) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.NotDerivable => continue,
        };
        for (r.helpers) |h| try out.append(arena, h);
        try out.append(arena, .{ .Instance = r.instance });
    }
}

fn processStandalone(
    arena: Allocator,
    sd: ast.DerivingDecl,
    module: ast.Module,
    diags: *diag_mod.DiagnosticCollector,
    out: *std.ArrayListUnmanaged(ast.Decl),
) DeriveError!void {
    // Find the data/newtype decl that `sd.type` refers to so that we can
    // walk its constructors.  `sd.type` may be a `Con T` or `App [Con T, ...]`.
    const type_name = extractTypeName(sd.type) orelse {
        try diags.emit(arena, .{
            .severity = .@"error",
            .code = .deriving_shape_mismatch,
            .span = sd.span,
            .message = "Cannot derive standalone instance: target type is not a simple data/newtype constructor",
        });
        return;
    };

    var norm: ?shape_mod.NormalizedDecl = null;
    for (module.declarations) |d| {
        switch (d) {
            .Data => |dd| if (std.mem.eql(u8, dd.name, type_name)) {
                norm = shape_mod.NormalizedDecl.fromData(dd);
                break;
            },
            .Newtype => |nn| if (std.mem.eql(u8, nn.name, type_name)) {
                norm = try shape_mod.NormalizedDecl.fromNewtype(arena, nn);
                break;
            },
            else => {},
        }
    }
    const ndecl = norm orelse {
        try diags.emit(arena, .{
            .severity = .@"error",
            .code = .deriving_shape_mismatch,
            .span = sd.span,
            .message = "Cannot derive standalone instance: target type not found in module",
        });
        return;
    };

    for (sd.classes) |class_name| {
        const r = synthOne(arena, ndecl, class_name, sd.span, diags) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.NotDerivable => continue,
        };
        for (r.helpers) |h| try out.append(arena, h);
        try out.append(arena, .{ .Instance = r.instance });
    }
}

fn extractTypeName(t: ast.Type) ?[]const u8 {
    return switch (t) {
        .Con => |q| q.name,
        .App => |parts| if (parts.len >= 1) extractTypeName(parts[0].*) else null,
        .Paren => |p| extractTypeName(p.*),
        else => null,
    };
}

const SynthError = error{ OutOfMemory, NotDerivable };

const Synthesised = struct {
    helpers: []const ast.Decl,
    instance: ast.InstanceDecl,
};

fn synthOne(
    arena: Allocator,
    decl: shape_mod.NormalizedDecl,
    class_name: []const u8,
    span: SourceSpan,
    diags: *diag_mod.DiagnosticCollector,
) SynthError!Synthesised {
    const kind = stock_classes.get(class_name) orelse {
        try diags.emit(arena, .{
            .severity = .@"error",
            .code = .deriving_unsupported_class,
            .span = span,
            .message = std.fmt.allocPrint(
                arena,
                "Cannot derive `{s}`: only Eq, Ord, Show, Bounded, Enum are supported",
                .{class_name},
            ) catch "Cannot derive: unsupported class",
        });
        return error.NotDerivable;
    };
    return switch (kind) {
        .eq => blk: {
            const r = try eq_mod.synth(arena, decl, span);
            break :blk .{ .helpers = r.helpers, .instance = r.instance };
        },
        .ord => blk: {
            const r = try ord_mod.synth(arena, decl, span);
            break :blk .{ .helpers = r.helpers, .instance = r.instance };
        },
        .show => blk: {
            const r = try show_mod.synth(arena, decl, span);
            break :blk .{ .helpers = r.helpers, .instance = r.instance };
        },
        .bounded => blk: {
            const r = try bounded_mod.synth(arena, decl, span, diags);
            break :blk .{ .helpers = r.helpers, .instance = r.instance };
        },
        .enum_ => blk: {
            const r = try enum_mod.synth(arena, decl, span, diags);
            break :blk .{ .helpers = r.helpers, .instance = r.instance };
        },
    };
}

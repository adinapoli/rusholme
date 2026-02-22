//! Rusholme - A toy Haskell compiler in Zig.
//!
//! This is the root module that exports all public APIs.

// Diagnostics
pub const diagnostics = struct {
    pub const span = @import("diagnostics/span.zig");
    pub const diagnostic = @import("diagnostics/diagnostic.zig");
    pub const terminal = @import("diagnostics/terminal.zig");
    pub const json = @import("diagnostics/json.zig");
};

// Frontend
pub const frontend = struct {
    pub const lexer = @import("frontend/lexer.zig");
    pub const parser = @import("frontend/parser.zig");
    pub const layout = @import("frontend/layout.zig");
    pub const unicode = @import("frontend/unicode.zig");
    pub const ast = @import("frontend/ast.zig");
    pub const pretty = @import("frontend/pretty.zig");
};

// Naming
pub const naming = struct {
    pub const unique = @import("naming/unique.zig");
};

// Renamer
pub const renamer = struct {
    pub const renamer = @import("renamer/renamer.zig");
};

// Type checking
pub const typechecker = @import("typechecker.zig");

pub const tc = struct {
    pub const htype = @import("typechecker/htype.zig");
    pub const unify = @import("typechecker/unify.zig");
    pub const env = @import("typechecker/env.zig");
    pub const solver = @import("typechecker/solver.zig");
    pub const infer = @import("typechecker/infer.zig");
    pub const class_env = @import("typechecker/class_env.zig");
};

// IR representations
pub const core = struct {
    pub const ast = @import("core/ast.zig");
    pub const pretty = @import("core/pretty.zig");
    pub const desugar = @import("core/desugar.zig");
    pub const lint = @import("core/lint.zig");
};

pub const grin = struct {
    pub const ir = @import("grin/ir.zig");
    pub const pretty = @import("grin/pretty.zig");
};

// Backend
pub const backend = struct {
    pub const llvm = @import("backend/llvm.zig");
};

// Runtime
pub const runtime = @import("runtime.zig");

// Re-export commonly used types
pub const SourceSpan = diagnostics.span.SourceSpan;
pub const SourcePos = diagnostics.span.SourcePos;
pub const FileId = diagnostics.span.FileId;
pub const Diagnostic = diagnostics.diagnostic.Diagnostic;
pub const DiagnosticCode = diagnostics.diagnostic.DiagnosticCode;
pub const Severity = diagnostics.diagnostic.Severity;
pub const Name = naming.unique.Name;
pub const Unique = naming.unique.Unique;
pub const UniqueSupply = naming.unique.UniqueSupply;

// ── Test discovery ─────────────────────────────────────────────────────
// Zig's test runner only discovers test blocks in transitively-referenced
// files. Imports inside struct wrappers above are not automatically
// traversed for tests. This block ensures all submodule tests are found.
test {
    const testing = @import("std").testing;
    // Top-level re-exports and direct imports
    testing.refAllDecls(@This());
    // Nested struct modules need explicit referencing
    testing.refAllDecls(diagnostics);
    testing.refAllDecls(frontend);
    testing.refAllDecls(naming);
    testing.refAllDecls(renamer);
    testing.refAllDecls(core);
    testing.refAllDecls(grin);
    testing.refAllDecls(backend);
    testing.refAllDecls(tc);
}

//! Rusholme - A toy Haskell compiler in Zig.
//!
//! This is the root module that exports all public APIs.

// Diagnostics
pub const diagnostics = struct {
    pub const span = @import("diagnostics/span.zig");
    pub const diagnostic = @import("diagnostics/diagnostic.zig");
};

// Frontend
pub const frontend = struct {
    pub const lexer = @import("frontend/lexer.zig");
    pub const parser = @import("frontend/parser.zig");
    pub const layout = @import("frontend/layout.zig");
    pub const unicode = @import("frontend/unicode.zig");
    pub const ast = @import("frontend/ast.zig");
};

// Type checking
pub const typechecker = @import("typechecker.zig");

// IR representations
pub const core = struct {
    pub const ir = @import("core/ir.zig");
};

pub const grin = struct {
    pub const ir = @import("grin/ir.zig");
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
pub const Severity = diagnostics.diagnostic.Severity;

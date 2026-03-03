//! Minimal REPL evaluation
//!
//! For MVP, echoes back the input expression with a formatted response.
//!
//! Compilation pipeline integration (future):
//!   1. Parse expression via rusholme.frontend.parser.Parser
//!   2. Typecheck via rusholme.tc.infer
//!   3. Desugar to Core via rusholme.core.desugar
//!   4. Translate to GRIN via rusholme.grin.grin_to
//!   5. Compile to WASM via rusholme.backend.grin_to_llvm

const std = @import("std");
const eval = @import("eval.zig");
const buffer = @import("buffer.zig");

/// Evaluate expression and write JSON response to output buffer
/// Returns the length of the response written
pub fn evaluate(input: []const u8) usize {
    const output_slice = buffer.getOutputBuffer()[0..16384];
    @memset(output_slice, 0); // Clear output buffer

    // Strip multi-line delimiters if present
    const expr = eval.stripMultilineDelimiters(input);

    // For MVP, echo back with type information
    // Future: compile and evaluate

    if (isIdentifier(expr)) {
        writeResponse(output_slice, expr, "identifier");
    } else if (isNumber(expr)) {
        writeResponse(output_slice, expr, "literal");
    } else {
        writeResponse(output_slice, expr, "expression");
    }

    // Return the length written (find first null terminator)
    var len: usize = 0;
    for (0..16384) |i| {
        if (output_slice[i] == 0 and i > 0) {
            len = i;
            break;
        }
    }
    return len;
}

fn isIdentifier(s: []const u8) bool {
    if (s.len == 0) return false;
    for (s) |c| {
        if (!((c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or c == '_')) {
            return false;
        }
    }
    return true;
}

fn isNumber(s: []const u8) bool {
    if (s.len == 0) return false;
    var has_digit = false;
    for (s) |c| {
        if (c >= '0' and c <= '9') {
            has_digit = true;
        } else {
            return false;
        }
    }
    return has_digit;
}

fn writeResponse(output: []u8, expr: []const u8, expr_type: []const u8) void {
    const template = "{{\"status\":\"success\",\"value\":\"{s}: \\\"{s}\\\"\"}}";
    _ = std.fmt.bufPrintZ(output, template, .{ expr_type, expr }) catch void;
}

//! IO primitives for LLVM-based runtime (issue #56).
//!
//! These functions are called from LLVM-generated code via the PrimOpMapping
//! in `grin_to_llvm.zig`.  The same source compiles correctly for every
//! supported target:
//!   - Native (Linux/macOS): `std.posix.system.write` → OS write() syscall
//!   - wasm32-wasi:          `std.os.wasi.fd_write`   → WASI fd_write import
//!
//! No backend-specific adaptations are needed.  (Issue #477.)

const std = @import("std");
const builtin = @import("builtin");
const node_mod = @import("node.zig");

// ═══════════════════════════════════════════════════════════════════════
// Internal helpers
// ═══════════════════════════════════════════════════════════════════════

/// Write `bytes` to the given file descriptor.
///
/// Branches at comptime on the OS so only the relevant syscall path is
/// emitted for each target.
fn writeBytesToFd(fd: u32, bytes: []const u8) void {
    switch (builtin.target.os.tag) {
        .wasi => {
            const iov = [1]std.os.wasi.ciovec_t{
                .{ .base = bytes.ptr, .len = bytes.len },
            };
            var nwritten: usize = 0;
            _ = std.os.wasi.fd_write(@intCast(fd), &iov, 1, &nwritten);
        },
        else => {
            _ = std.posix.system.write(@intCast(fd), bytes.ptr, bytes.len);
        },
    }
}

fn writeBytes(bytes: []const u8) void {
    writeBytesToFd(1, bytes);
}

fn writeBytesErr(bytes: []const u8) void {
    writeBytesToFd(2, bytes);
}

// ═══════════════════════════════════════════════════════════════════════
// IO Primitives
// ═══════════════════════════════════════════════════════════════════════

/// Print a null-terminated string followed by a newline to stdout.
///
/// Called `rts_putStrLn` from LLVM-generated code (PrimOp for `putStrLn`).
/// Returns 0 on success (return value matches the `puts()` convention used
/// by the LLVM codegen's LibcFunction descriptor).
pub export fn rts_putStrLn(str: [*:0]const u8) i32 {
    writeBytes(std.mem.span(str));
    writeBytes("\n");
    return 0;
}

/// Print a null-terminated string without a trailing newline to stdout.
///
/// Called `rts_putStr` from LLVM-generated code (PrimOp for `putStr`).
/// Returns 0 on success.
pub export fn rts_putStr(str: [*:0]const u8) i32 {
    writeBytes(std.mem.span(str));
    return 0;
}

/// Print a single character to stdout.
///
/// Called `rts_putChar` from LLVM-generated code (PrimOp for `putChar`).
/// The character is passed as an i64 (the Char's codepoint, zero-extended).
/// Returns 0 on success.
pub export fn rts_putChar(ch: i64) i32 {
    const byte: u8 = @intCast(ch & 0xFF);
    writeBytes(&[1]u8{byte});
    return 0;
}

/// Convert a [Char] heap list (Cons/Nil linked list of character nodes) to a
/// null-terminated C string allocated on the RTS heap.
///
/// Called `rts_charlist_to_cstring` from LLVM-generated code when a [Char]
/// value is passed to a primop that expects a C string (e.g., putStrLn).
///
/// Parameters:
///   - list_ptr: pointer to the head node of the [Char] list
///   - cons_disc: the tag discriminant for the (:) constructor
///   - nil_disc: the tag discriminant for the [] constructor
///
/// Returns a pointer to a null-terminated C string. The string is allocated
/// from the RTS heap and need not be freed (arena-managed).
pub export fn rts_charlist_to_cstring(list_ptr: *const node_mod.Node, cons_disc: u64, nil_disc: u64) [*:0]const u8 {
    // First pass: count the length
    var len: usize = 0;
    var cur: *const node_mod.Node = list_ptr;
    while (true) {
        const tag_int: u64 = @intFromEnum(cur.tag);
        if (tag_int == nil_disc) break;
        if (tag_int != cons_disc) break; // unexpected tag, stop
        if (cur.n_fields < 2) break;
        len += 1;
        // field[1] is the tail pointer — may be stored as PtrToInt (i64)
        const tail_raw = node_mod.fieldsConst(cur)[1];
        if (tail_raw == 0) break;
        // The tail is a pointer to the next node stored as u64
        cur = @ptrFromInt(@as(usize, @intCast(tail_raw)));
    }

    // Allocate buffer (len + 1 for null terminator)
    const heap_alloc = @import("heap.zig").allocator();
    const buf = heap_alloc.alloc(u8, len + 1) catch @panic("OOM in rts_charlist_to_cstring");

    // Second pass: extract characters
    cur = list_ptr;
    for (0..len) |i| {
        const tag_int: u64 = @intFromEnum(cur.tag);
        if (tag_int != cons_disc or cur.n_fields < 2) break;
        // field[0] is the character value (either raw i64 or pointer to Char node)
        const char_field = node_mod.fieldsConst(cur)[0];
        // Check if the field is a pointer to a Char node
        const align_val: u64 = @alignOf(*anyopaque);
        if (char_field > 0x1000 and char_field % align_val == 0) {
            const char_node: *const node_mod.Node = @ptrFromInt(@as(usize, @intCast(char_field)));
            if (char_node.tag == .Char and char_node.n_fields >= 1) {
                buf[i] = @intCast(node_mod.fieldsConst(char_node)[0] & 0xFF);
            } else {
                buf[i] = @intCast(char_field & 0xFF);
            }
        } else {
            buf[i] = @intCast(char_field & 0xFF);
        }
        const tail_uptr: usize = @intCast(node_mod.fieldsConst(cur)[1]);
        cur = @ptrFromInt(tail_uptr);
    }
    buf[len] = 0;

    return @ptrCast(buf.ptr);
}

/// Convert a null-terminated C string to a [Char] heap list (Cons/Nil linked
/// list of character values).
///
/// Called `rts_cstring_to_charlist` from LLVM-generated code when a string
/// literal needs to be treated as a [Char] list (e.g., for pattern matching
/// by `++`, `head`, `tail`, etc.).
///
/// Parameters:
///   - str: pointer to a null-terminated C string
///   - cons_disc: the tag discriminant for the (:) constructor
///   - nil_disc: the tag discriminant for the [] constructor
///
/// Returns a pointer to the head node of the [Char] list. Each Cons node
/// has 2 fields: field[0] = character value (as u64), field[1] = tail pointer.
pub export fn rts_cstring_to_charlist(str: [*:0]const u8, cons_disc: u64, nil_disc: u64) *node_mod.Node {
    // Build the list from right to left: start with Nil, then prepend each character.
    var tail: *node_mod.Node = node_mod.rts_alloc(nil_disc, 0);
    const span = std.mem.span(str);

    var i = span.len;
    while (i > 0) {
        i -= 1;
        const cons = node_mod.rts_alloc(cons_disc, 2);
        // field[0] = character value (raw i64)
        node_mod.rts_store_field(cons, 0, @as(u64, span[i]));
        // field[1] = tail pointer (as u64)
        node_mod.rts_store_field(cons, 1, @intFromPtr(tail));
        tail = cons;
    }
    return tail;
}

/// Print an error message to stderr and terminate the program with exit code 1.
///
/// Implements the `error :: String -> a` Haskell primitive.  Called
/// `rts_error` from LLVM-generated code (PrimOp for `error`).
/// Never returns — `std.process.exit` calls `proc_exit` on WASI and the
/// `exit` syscall on native targets.
pub export fn rts_error(str: [*:0]const u8) i32 {
    writeBytesErr("error: ");
    writeBytesErr(std.mem.span(str));
    writeBytesErr("\n");
    std.process.exit(1);
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "rts_putStrLn is callable" {
    // Compile-time verification that the export exists and has the right type.
    _ = &rts_putStrLn;
}

test "rts_putStr is callable" {
    _ = &rts_putStr;
}

test "rts_putChar is callable" {
    _ = &rts_putChar;
}

test "rts_cstring_to_charlist is callable" {
    _ = &rts_cstring_to_charlist;
}

test "rts_error is callable" {
    _ = &rts_error;
}

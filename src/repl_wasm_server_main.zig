//! WASM REPL Server entry point (command mode).
//!
//! Unlike `repl_wasm_main.zig` which builds a **reactor** module for
//! the browser (long-lived, exported functions, no `proc_exit`), this
//! file builds a **command** module intended for headless use via
//! `wasmtime run repl-server.wasm`.
//!
//! It initialises a JSON-RPC server and runs the stdin/stdout loop
//! until the client sends a `shutdown` request or stdin closes.

const std = @import("std");
const ReplServer = @import("repl/server.zig").ReplServer;

pub fn main() !void {
    var io_backend: std.Io.Threaded = std.Io.Threaded.init_single_threaded;
    const io = io_backend.io();

    var server = try ReplServer.init(std.heap.page_allocator, io);
    defer server.deinit();

    try server.run();
}

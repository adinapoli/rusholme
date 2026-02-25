//! Linker abstraction for producing native executables.
//!
//! Drives the system linker (via `cc`) to combine compiled object files
//! into a native executable. Designed to evolve as the runtime grows:
//!
//! - **M1**: single object + libc (`cc hello.o -o hello`)
//! - **Future**: `runtime_objects` will include Zig RTS `.o` files
//!   (heap, thunk evaluator, GC)
//!
//! The `system_libs` / `runtime_objects` separation is deliberate:
//! runtime objects are RTS code we compile ourselves; system libs are
//! OS/distro-provided. This distinction matters for cross-compilation.

const std = @import("std");
const Io = std.Io;
const process = std.process;

pub const Linker = struct {
    /// Object files to link (compiled GRIN modules).
    objects: []const []const u8,
    /// System libraries to link against (e.g. "c").
    system_libs: []const []const u8,
    /// Extra object files from the runtime (future: Zig RTS).
    runtime_objects: []const []const u8,
    /// Output path for the executable.
    output_path: []const u8,

    pub const LinkError = error{
        LinkerFailed,
        LinkerNotFound,
        OutOfMemory,
    } || process.SpawnError || process.Child.WaitError;

    /// Invoke the system linker to produce a native executable.
    ///
    /// Uses `cc` as the linker driver, which is available in the Nix
    /// devshell as part of `stdenv`. Structured so swapping to `zig cc`
    /// or a custom link step is a single-point change.
    pub fn link(self: Linker, allocator: std.mem.Allocator, io: Io) LinkError!void {
        // Build argv: cc <objects> <runtime_objects> -l<lib>... -o <output>
        var argv: std.ArrayList([]const u8) = .empty;
        defer argv.deinit(allocator);

        try argv.append(allocator, "cc");

        for (self.objects) |obj| {
            try argv.append(allocator, obj);
        }

        for (self.runtime_objects) |obj| {
            try argv.append(allocator, obj);
        }

        for (self.system_libs) |lib| {
            // Build "-l<lib>" flag.
            const flag = try std.fmt.allocPrint(allocator, "-l{s}", .{lib});
            try argv.append(allocator, flag);
        }

        try argv.append(allocator, "-o");
        try argv.append(allocator, self.output_path);

        var child = try process.spawn(io, .{
            .argv = argv.items,
        });

        const term = try child.wait(io);

        // Free the allocated -l flags after the child has terminated.
        for (argv.items) |arg| {
            if (arg.len >= 2 and arg[0] == '-' and arg[1] == 'l') {
                allocator.free(arg);
            }
        }

        switch (term) {
            .exited => |code| {
                if (code != 0) return error.LinkerFailed;
            },
            else => return error.LinkerFailed,
        }
    }
};

test "Linker: struct fields are accessible" {
    const linker = Linker{
        .objects = &.{"hello.o"},
        .system_libs = &.{"c"},
        .runtime_objects = &.{},
        .output_path = "hello",
    };
    try std.testing.expectEqual(@as(usize, 1), linker.objects.len);
    try std.testing.expectEqualStrings("hello.o", linker.objects[0]);
    try std.testing.expectEqual(@as(usize, 1), linker.system_libs.len);
    try std.testing.expectEqualStrings("c", linker.system_libs[0]);
    try std.testing.expectEqual(@as(usize, 0), linker.runtime_objects.len);
    try std.testing.expectEqualStrings("hello", linker.output_path);
}

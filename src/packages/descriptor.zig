//! Package descriptor format for Rusholme packages.
//!
//! A `.rhc-pkg` file describes a Rusholme package: its name, version,
//! exposed modules, and dependencies.
//!
//! ## Format
//!
//! The format is a minimal line-oriented key-value format:
//!
//! ```
//! # rhc-internal package descriptor
//! name    = "rhc-internal"
//! version = "0.1.0"
//!
//! exposed-modules = ["RHC.Base", "RHC.IO"]
//! depends         = ["rhc-prim-0.1.0"]
//! ```
//!
//! Rules:
//! - Comments begin with `#` and extend to end-of-line.
//! - Blank lines are ignored.
//! - Each non-blank, non-comment line has the form `key = value`.
//! - String values are double-quoted, with `\n`, `\t`, `\r`, `\"`, `\\` escapes.
//! - List values are `["elem1", "elem2"]` on a single line; multi-line lists
//!   are not supported.
//! - Unknown keys are silently ignored (forward-compatibility).
//!
//! Required fields: `name`, `version`.
//! Optional fields: `exposed-modules` (default `[]`), `depends` (default `[]`).
//!
//! ## References
//!
//! - `docs/decisions/0008-rhc-internal-package-ecosystem.md` (Phase 1)
//! - GitHub issue: https://github.com/adinapoli/rusholme/issues/649

const std = @import("std");

// ── Public types ─────────────────────────────────────────────────────────────

/// A parsed `.rhc-pkg` package descriptor.
///
/// All string memory is owned by this struct; call `deinit` to free it.
pub const PackageDescriptor = struct {
    /// Package name, e.g. `"rhc-internal"`.
    name: []const u8,
    /// Semantic version string, e.g. `"0.1.0"`.
    version: []const u8,
    /// Module names exposed to importers, e.g. `["RHC.Base", "RHC.IO"]`.
    exposed_modules: []const []const u8,
    /// Dependencies in `name-version` form, e.g. `["rhc-prim-0.1.0"]`.
    depends: []const []const u8,

    pub fn deinit(self: PackageDescriptor, alloc: std.mem.Allocator) void {
        alloc.free(self.name);
        alloc.free(self.version);
        for (self.exposed_modules) |m| alloc.free(m);
        alloc.free(self.exposed_modules);
        for (self.depends) |d| alloc.free(d);
        alloc.free(self.depends);
    }
};

/// Errors that can arise during descriptor parsing.
pub const Error = error{
    /// A required field (`name` or `version`) is absent.
    MissingRequiredField,
    /// A field appears more than once in the descriptor.
    DuplicateField,
    /// The descriptor syntax is malformed.
    InvalidSyntax,
    /// Memory allocation failed.
    OutOfMemory,
};

// ── Serialisation ─────────────────────────────────────────────────────────────

/// Serialise `desc` back to `.rhc-pkg` format, returning a heap-allocated
/// string.  The output is accepted by `parse` without loss.
///
/// The caller owns the returned slice and must free it with `alloc.free`.
pub fn format(desc: PackageDescriptor, alloc: std.mem.Allocator) ![]u8 {
    var buf: std.ArrayListUnmanaged(u8) = .{};
    errdefer buf.deinit(alloc);

    try buf.appendSlice(alloc, "name    = ");
    try appendQuotedString(&buf, alloc, desc.name);
    try buf.append(alloc, '\n');

    try buf.appendSlice(alloc, "version = ");
    try appendQuotedString(&buf, alloc, desc.version);
    try buf.append(alloc, '\n');

    try buf.appendSlice(alloc, "\nexposed-modules = [");
    for (desc.exposed_modules, 0..) |m, i| {
        if (i > 0) try buf.appendSlice(alloc, ", ");
        try appendQuotedString(&buf, alloc, m);
    }
    try buf.appendSlice(alloc, "]\n");

    try buf.appendSlice(alloc, "depends = [");
    for (desc.depends, 0..) |d, i| {
        if (i > 0) try buf.appendSlice(alloc, ", ");
        try appendQuotedString(&buf, alloc, d);
    }
    try buf.appendSlice(alloc, "]\n");

    return buf.toOwnedSlice(alloc);
}

fn appendQuotedString(
    buf: *std.ArrayListUnmanaged(u8),
    alloc: std.mem.Allocator,
    s: []const u8,
) !void {
    try buf.append(alloc, '"');
    for (s) |ch| {
        switch (ch) {
            '"' => try buf.appendSlice(alloc, "\\\""),
            '\\' => try buf.appendSlice(alloc, "\\\\"),
            '\n' => try buf.appendSlice(alloc, "\\n"),
            '\t' => try buf.appendSlice(alloc, "\\t"),
            '\r' => try buf.appendSlice(alloc, "\\r"),
            else => try buf.append(alloc, ch),
        }
    }
    try buf.append(alloc, '"');
}

// ── Parser ────────────────────────────────────────────────────────────────────

const Parser = struct {
    alloc: std.mem.Allocator,
    source: []const u8,
    pos: usize,

    fn init(alloc: std.mem.Allocator, source: []const u8) Parser {
        return .{ .alloc = alloc, .source = source, .pos = 0 };
    }

    fn atEnd(self: *const Parser) bool {
        return self.pos >= self.source.len;
    }

    fn peek(self: *const Parser) ?u8 {
        return if (self.atEnd()) null else self.source[self.pos];
    }

    fn advance(self: *Parser) void {
        if (!self.atEnd()) self.pos += 1;
    }

    /// Skip horizontal whitespace (spaces and tabs, but not newlines).
    fn skipHorizontalWs(self: *Parser) void {
        while (self.peek()) |ch| {
            if (ch == ' ' or ch == '\t') self.advance() else break;
        }
    }

    /// Consume exactly `expected` (after skipping horizontal whitespace).
    /// Returns `InvalidSyntax` if the next non-whitespace byte is not `expected`.
    fn consumeChar(self: *Parser, expected: u8) Error!void {
        self.skipHorizontalWs();
        if (self.peek() != expected) return Error.InvalidSyntax;
        self.advance();
    }

    /// Skip to the start of the next line (consuming the newline).
    fn skipToNextLine(self: *Parser) void {
        while (self.peek()) |ch| {
            self.advance();
            if (ch == '\n') return;
        }
    }

    /// Return true if everything remaining on this line is whitespace or a
    /// `#`-comment.  Does not advance `pos`.
    fn isRestOfLineEmpty(self: *const Parser) bool {
        var i = self.pos;
        while (i < self.source.len) {
            switch (self.source[i]) {
                ' ', '\t' => i += 1,
                '#', '\n', '\r' => return true,
                else => return false,
            }
        }
        return true; // end of file
    }

    /// Parse a quoted string starting with the opening `"`.
    /// On return `pos` is just after the closing `"`.
    fn parseQuotedString(self: *Parser) Error![]const u8 {
        try self.consumeChar('"');

        var buf: std.ArrayListUnmanaged(u8) = .{};
        errdefer buf.deinit(self.alloc);

        while (true) {
            const ch = self.peek() orelse return Error.InvalidSyntax;
            self.advance();
            switch (ch) {
                '"' => break,
                '\\' => {
                    const esc = self.peek() orelse return Error.InvalidSyntax;
                    self.advance();
                    switch (esc) {
                        'n' => try buf.append(self.alloc, '\n'),
                        't' => try buf.append(self.alloc, '\t'),
                        'r' => try buf.append(self.alloc, '\r'),
                        '"' => try buf.append(self.alloc, '"'),
                        '\\' => try buf.append(self.alloc, '\\'),
                        else => return Error.InvalidSyntax,
                    }
                },
                else => try buf.append(self.alloc, ch),
            }
        }

        return buf.toOwnedSlice(self.alloc);
    }

    /// Parse a list of quoted strings: `["a", "b"]` (single-line only).
    /// On return `pos` is just after the `]`.
    fn parseStringList(self: *Parser) Error![]const []const u8 {
        try self.consumeChar('[');

        var list: std.ArrayListUnmanaged([]const u8) = .{};
        errdefer {
            for (list.items) |s| self.alloc.free(s);
            list.deinit(self.alloc);
        }

        self.skipHorizontalWs();
        if (self.peek() == @as(?u8, ']')) {
            self.advance();
            return list.toOwnedSlice(self.alloc);
        }

        while (true) {
            const s = try self.parseQuotedString();
            errdefer self.alloc.free(s);
            try list.append(self.alloc, s);

            self.skipHorizontalWs();
            const ch = self.peek() orelse return Error.InvalidSyntax;
            if (ch == ']') {
                self.advance();
                break;
            } else if (ch == ',') {
                self.advance();
                self.skipHorizontalWs();
                // Allow a trailing comma immediately before `]`.
                if (self.peek() == @as(?u8, ']')) {
                    self.advance();
                    break;
                }
            } else {
                return Error.InvalidSyntax;
            }
        }

        return list.toOwnedSlice(self.alloc);
    }

    /// Parse an identifier key: `[A-Za-z0-9_-]+`.
    /// Returns a slice into `source` (no allocation).
    fn parseKey(self: *Parser) Error![]const u8 {
        self.skipHorizontalWs();
        const start = self.pos;
        while (self.peek()) |ch| {
            if (std.ascii.isAlphanumeric(ch) or ch == '-' or ch == '_') {
                self.advance();
            } else break;
        }
        if (self.pos == start) return Error.InvalidSyntax;
        return self.source[start..self.pos];
    }
};

/// Parse a `.rhc-pkg` descriptor from `source`.
///
/// All strings in the returned `PackageDescriptor` are heap-allocated using
/// `alloc`; the caller must call `desc.deinit(alloc)` when done.
pub fn parse(alloc: std.mem.Allocator, source: []const u8) Error!PackageDescriptor {
    var p = Parser.init(alloc, source);

    // Parsed field values — null until seen.
    var name: ?[]const u8 = null;
    var version: ?[]const u8 = null;
    var exposed_modules: ?[]const []const u8 = null;
    var depends: ?[]const []const u8 = null;

    errdefer {
        if (name) |s| alloc.free(s);
        if (version) |s| alloc.free(s);
        if (exposed_modules) |ms| {
            for (ms) |m| alloc.free(m);
            alloc.free(ms);
        }
        if (depends) |ds| {
            for (ds) |d| alloc.free(d);
            alloc.free(ds);
        }
    }

    while (!p.atEnd()) {
        p.skipHorizontalWs();

        // Blank line or comment — skip entire line.
        switch (p.peek() orelse break) {
            '\n', '\r', '#' => {
                p.skipToNextLine();
                continue;
            },
            else => {},
        }

        const key = try p.parseKey();
        try p.consumeChar('=');
        p.skipHorizontalWs();

        if (std.mem.eql(u8, key, "name")) {
            if (name != null) return Error.DuplicateField;
            name = try p.parseQuotedString();
        } else if (std.mem.eql(u8, key, "version")) {
            if (version != null) return Error.DuplicateField;
            version = try p.parseQuotedString();
        } else if (std.mem.eql(u8, key, "exposed-modules")) {
            if (exposed_modules != null) return Error.DuplicateField;
            exposed_modules = try p.parseStringList();
        } else if (std.mem.eql(u8, key, "depends")) {
            if (depends != null) return Error.DuplicateField;
            depends = try p.parseStringList();
        } else {
            // Unknown key — skip to next line (forward-compatible).
            p.skipToNextLine();
            continue;
        }

        if (!p.isRestOfLineEmpty()) return Error.InvalidSyntax;
        p.skipToNextLine();
    }

    // Validate required fields.
    if (name == null or version == null) return Error.MissingRequiredField;

    // Fill in optional fields with empty defaults (may allocate).
    if (exposed_modules == null) {
        exposed_modules = try alloc.dupe([]const u8, &.{});
    }
    if (depends == null) {
        depends = try alloc.dupe([]const u8, &.{});
    }

    return PackageDescriptor{
        .name = name.?,
        .version = version.?,
        .exposed_modules = exposed_modules.?,
        .depends = depends.?,
    };
}

// ── Tests ─────────────────────────────────────────────────────────────────────

test "parse minimal descriptor" {
    const source =
        \\name    = "rhc-internal"
        \\version = "0.1.0"
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings("rhc-internal", desc.name);
    try std.testing.expectEqualStrings("0.1.0", desc.version);
    try std.testing.expectEqual(@as(usize, 0), desc.exposed_modules.len);
    try std.testing.expectEqual(@as(usize, 0), desc.depends.len);
}

test "parse full descriptor" {
    const source =
        \\# rhc-internal package descriptor
        \\name    = "rhc-internal"
        \\version = "0.1.0"
        \\
        \\exposed-modules = ["RHC.Base", "RHC.IO"]
        \\depends         = ["rhc-prim-0.1.0"]
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings("rhc-internal", desc.name);
    try std.testing.expectEqualStrings("0.1.0", desc.version);

    try std.testing.expectEqual(@as(usize, 2), desc.exposed_modules.len);
    try std.testing.expectEqualStrings("RHC.Base", desc.exposed_modules[0]);
    try std.testing.expectEqualStrings("RHC.IO", desc.exposed_modules[1]);

    try std.testing.expectEqual(@as(usize, 1), desc.depends.len);
    try std.testing.expectEqualStrings("rhc-prim-0.1.0", desc.depends[0]);
}

test "parse descriptor with comment after value" {
    const source =
        \\name    = "foo" # package name
        \\version = "1.2.3" # semver
        \\depends = ["bar-0.1.0"] # dependencies
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings("foo", desc.name);
    try std.testing.expectEqualStrings("1.2.3", desc.version);
    try std.testing.expectEqual(@as(usize, 1), desc.depends.len);
    try std.testing.expectEqualStrings("bar-0.1.0", desc.depends[0]);
}

test "parse: unknown fields are silently ignored" {
    const source =
        \\name    = "foo"
        \\version = "0.1.0"
        \\author  = "someone"
        \\license = "BSD-3"
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings("foo", desc.name);
    try std.testing.expectEqualStrings("0.1.0", desc.version);
}

test "parse: trailing comma in list" {
    const source =
        \\name    = "foo"
        \\version = "0.1.0"
        \\exposed-modules = ["A", "B",]
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(usize, 2), desc.exposed_modules.len);
    try std.testing.expectEqualStrings("A", desc.exposed_modules[0]);
    try std.testing.expectEqualStrings("B", desc.exposed_modules[1]);
}

test "parse: empty lists" {
    const source =
        \\name    = "foo"
        \\version = "0.1.0"
        \\exposed-modules = []
        \\depends         = []
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(usize, 0), desc.exposed_modules.len);
    try std.testing.expectEqual(@as(usize, 0), desc.depends.len);
}

test "parse error: missing required field name" {
    const result = parse(std.testing.allocator, "version = \"0.1.0\"\n");
    try std.testing.expectError(Error.MissingRequiredField, result);
}

test "parse error: missing required field version" {
    const result = parse(std.testing.allocator, "name = \"foo\"\n");
    try std.testing.expectError(Error.MissingRequiredField, result);
}

test "parse error: duplicate field" {
    const source =
        \\name    = "foo"
        \\name    = "bar"
        \\version = "0.1.0"
    ;
    const result = parse(std.testing.allocator, source);
    try std.testing.expectError(Error.DuplicateField, result);
}

test "format and parse roundtrip" {
    const source =
        \\name    = "base"
        \\version = "0.1.0"
        \\exposed-modules = ["Prelude", "Data.Maybe", "Data.List"]
        \\depends         = ["rhc-internal-0.1.0"]
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    const serialised = try format(desc, std.testing.allocator);
    defer std.testing.allocator.free(serialised);

    const desc2 = try parse(std.testing.allocator, serialised);
    defer desc2.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(desc.name, desc2.name);
    try std.testing.expectEqualStrings(desc.version, desc2.version);
    try std.testing.expectEqual(desc.exposed_modules.len, desc2.exposed_modules.len);
    for (desc.exposed_modules, desc2.exposed_modules) |m1, m2| {
        try std.testing.expectEqualStrings(m1, m2);
    }
    try std.testing.expectEqual(desc.depends.len, desc2.depends.len);
    for (desc.depends, desc2.depends) |d1, d2| {
        try std.testing.expectEqualStrings(d1, d2);
    }
}

test "parse: string escape sequences" {
    const source =
        \\name    = "foo\"bar"
        \\version = "0\\1"
    ;
    const desc = try parse(std.testing.allocator, source);
    defer desc.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings("foo\"bar", desc.name);
    try std.testing.expectEqualStrings("0\\1", desc.version);
}

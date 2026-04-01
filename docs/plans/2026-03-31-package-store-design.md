# Package Store Design

**Date:** 2026-03-31
**Issue:** #650 — Implement package store layout at `~/.rhc/store/`
**Status:** Approved

---

## Overview

Implement `src/packages/store.zig` — a package registry at `~/.rhc/store/<arch>-<os>-<version>/` with JSON conf entries for package lookup and registration.

---

## Architecture

```
Store (src/packages/store.zig)
├── Store.init(allocator, root_path?)      → create/open store
├── Store.defaultPath(allocator)           → ~/.rhc/store/<arch>-<os>-<version>
├── Store.register(pkg_key, descriptor)    → write .conf + create package dir
├── Store.lookup(name, version)            → ?Store.Entry
├── Store.lookupByKey(key)                 → ?Store.Entry
└── Store.list()                           → []const Store.Entry
```

---

## On-Disk Layout

```
~/.rhc/store/<arch>-<os>-<version>/
  package.conf.d/               # one .conf (JSON) per installed package
    abc123...-rhc-prim-0.1.0.conf
    def456...-rhc-internal-0.1.0.conf
  rhc-prim-0.1.0/              # package artifacts
    RHC/Prim.rhi
    grin/RHC.Prim.grin
    llvm/x86_64-linux/rhc-prim.bc
  rhc-internal-0.1.0/
    RHC/Base.rhi
    RHC/IO.rhi
    grin/...
```

**Note:** This implements Phase 1 of `docs/decisions/0008-rhc-internal-package-ecosystem.md`. Package artifact directories (`rhc-prim-0.1.0/`) are created by `Store.register()` as empty stubs; contents are populated later during package installation.

---

## Package Keys

**Design decision:** Use descriptor SHA256 hash as key.

**Key format:** `{sha256}-{name}-{version}`

Example: `abc123def456...-rhc-prim-0.1.0`

**Rationale:**
- Simple, deterministic based on `.rhc-pkg` file content
- Matches existing descriptor parsing format (`depends = ["rhc-prim-0.1.0"]`)
- Boot packages (shipped with rhc) are immutable by definition
- Future upgrade path to closure hashing can add `closure_hash` field to conf files

---

## Conf File Format

Path: `package.conf.d/{hash}-{name}-{version}.conf`

```json
{
  "key": "abc123...-rhc-prim-0.1.0",
  "name": "rhc-prim",
  "version": "0.1.0",
  "hash": "abc123...",
  "exposed_modules": ["RHC.Prim"],
  "depends": [],
  "install_path": "/home/user/.rhc/store/x86_64-linux-0.1.0/rhc-prim-0.1.0"
}
```

**Fields:**
- `key`: Full package key for direct lookup
- `name`, `version`: Semantic package identifier
- `hash`: SHA256 of descriptor (for verification)
- `install_path`: Absolute path to package artifact directory
- `exposed_modules`, `depends`: Copied from descriptor

---

## API Design

### Types

```zig
pub const Store = struct {
    allocator: std.mem.Allocator,
    root_path: []const u8,
    conf_dir_path: []const u8,

    pub fn deinit(self: *Store) void { }

    pub fn init(alloc: std.mem.Allocator, root_path: ?[]const u8) Error!Store { }
    pub fn defaultPath(alloc: std.mem.Allocator) []const u8 { }
    pub fn register(self: *Store, pkg_key: []const u8, desc: descriptor.PackageDescriptor) Error!void { }
    pub fn lookup(self: *const Store, name: []const u8, version: []const u8) Error!?Entry { }
    pub fn lookupByKey(self: *const Store, key: []const u8) Error!?Entry { }
    pub fn list(self: *const Store) Error![]const Entry { }

    // Internal helpers
    fn computeKey(name: []const u8, version: []const u8, descriptor_content: []const u8) [64]u8 { }
    fn computeConfPath(self: Store, key: []const u8) []const u8 { }
    fn computePkgPath(self: Store, name: []const u8, version: []const u8) []const u8 { }
};

pub const Entry = struct {
    key: []const u8,              // "{hash}-{name}-{version}"
    name: []const u8,
    version: []const u8,
    hash: []const u8,             // descriptor SHA256
    exposed_modules: []const []const u8,
    depends: []const []const u8,
    install_path: []const u8,

    pub fn deinit(entry: Entry, alloc: std.mem.Allocator) void { }
};

pub const Error = error {
    DuplicatePackage,
    InvalidConf,
    OutOfMemory,
} || std.fs.File.OpenError || std.json.Error;
```

### Methods

#### Store.init(allocator, root_path?)
- If `root_path` null → compute default path via `defaultPath()`
- Create root directory and `package.conf.d/` if missing
- Return `Error` on IO failure

#### Store.defaultPath(allocator)
- Returns `~/.rhc/store/{arch}-{os}-{version}/`
- e.g., `/home/user/.rhc/store/x86_64-linux-0.1.0/`
- Uses `builtin.cpu.arch`, `builtin.os.tag`, and `RUSHOLME_VERSION` constant
- Caller owns the returned string

#### Store.computeKey(name, version, descriptor_content)
- Internal: compute SHA256 hash of descriptor bytes
- Return hex string (64 chars, no null terminator)

#### Store.register(pkg_key, descriptor)
- `pkg_key` is `{hash}-{name}-{version}` (pre-computed by caller)
- Write JSON conf to `package.conf.d/{key}.conf`
- Create empty package directory `{root}/{name}-{version}/`
- Return `DuplicatePackage` if conf file already exists
- Conf file contains `descriptor` fields + `key`, `hash`, `install_path`

#### Store.lookup(name, version) / lookupByKey(key)
- Scan `package.conf.d/` for matching conf file (by name+version or exact key)
- Parse JSON, return `Entry` with owned strings
- Return null if not found
- `Entry` strings allocated with Store's allocator; caller must call `deinit()`

#### Store.list()
- Scan `package.conf.d/`, parse all `.conf` files
- Return slice of `Entry` entries
- Caller must deinit each entry and free the slice

---

## Error Handling

Hybrid approach: specific Store errors for semantic issues, raw errors for IO/JSON.

| Operation | Errors |
|-----------|--------|
| `init()` | `std.fs.File.OpenError`, `OutOfMemory` |
| `register()` | `DuplicatePackage`, `std.fs.File.WriteError`, `OutOfMemory` |
| `lookup()` | `InvalidConf`, `std.json.Error`, `OutOfMemory` |
| `list()` | `InvalidConf`, `std.json.Error`, `OutOfMemory` |

---

## Testing Requirements

Unit tests in `src/packages/store.zig`:

1. `Store.init()` creates directory structure correctly
2. `Store.defaultPath()` generates correct format
3. `Store.register()` writes conf file and creates package dir
4. `Store.register()` returns `DuplicatePackage` on re-registration
5. `Store.lookup(name, version)` finds registered package
6. `Store.lookupByKey(key)` finds by full key
7. `Store.lookup()` returns null for non-existent package
8. `Store.list()` returns all registered packages
9. `Entry.deinit()` properly frees all memory

Tests should use `std.testing.allocator` and `std.fs.tmpDir` for isolation.

---

## Future Considerations

### Upgrade Path to Closure Hashing

Current implementation uses descriptor hash (`hash` field). Future versions may add:

```json
{
  "hash": "abc123...",           // descriptor hash (current)
  "closure_hash": "def456...",   // closure hash (future upgrade)
  ...
}
```

The `key` filename format remains `{hash}-{name}-{version}` for backward compatibility; `closure_hash` can be added transparently.

### Multi-Store Support

`Store.init(root_path)` already accepts custom root paths, enabling per-project package databases in the future (similar to Cabal's `--package-db` flag).

### Package Removal

Not in scope for Phase 1. Future `Store.unregister(key)` would:
- Remove conf file
- Optionally remove package directory (with safety checks for dependencies)

---

## References

- Issue: #650 — Implement package store layout at `~/.rhc/store/`
- Design: `docs/decisions/0008-rhc-internal-package-ecosystem.md` (Phase 1)
- Code: `src/packages/descriptor.zig` — descriptor format

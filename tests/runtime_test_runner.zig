//! Runtime test runner for issue #56 tests.
//!
//! This module runs tests for the LLVM-based runtime (src/rts/).
//! These tests require C headers/libc and should be run via `nix develop`.

const std = @import("std");
const runtime = @import("runtime");
const heap = runtime.heap;
const io = runtime.io_module;
const eval = runtime.eval;
const node = runtime.node;

test "runtime: init/deinit heap" {
    heap.init();
    defer heap.deinit();

    _ = heap.allocator();
}

test "runtime: alloc integer node" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    try std.testing.expectEqual(.Int, n.tag);
}

test "runtime: alloc character node" {
    heap.init();
    defer heap.deinit();

    const n = node.createChar('A');
    try std.testing.expectEqual(.Char, n.tag);
}

test "runtime: alloc unit node" {
    heap.init();
    defer heap.deinit();

    const n = node.createUnit();
    try std.testing.expectEqual(.Unit, n.tag);
}

test "runtime: alloc string node" {
    heap.init();
    defer heap.deinit();

    const hello: [*]const u8 = "Hello";
    const n = node.createString(hello);
    try std.testing.expectEqual(.String, n.tag);
}

test "runtime: evaluate non-thunk returns as-is" {
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    const result = eval.rts_eval(n);

    try std.testing.expectEqual(n, result);
}

test "runtime: rts_putStrLn exports C function" {
    _ = io.rts_putStrLn;
}

test "runtime: rts_putStr exports C function" {
    _ = io.rts_putStr;
}

// ── Thunk evaluation tests (#384) ────────────────────────────────────────────

test "runtime: createThunk stores fn_ptr and env" {
    heap.init();
    defer heap.deinit();

    const env = node.createInt(99);
    const ThunkHelper = struct {
        fn call(e: *node.Node) callconv(.auto) *node.Node {
            return e;
        }
    };
    const t = node.createThunk(ThunkHelper.call, env);
    try std.testing.expectEqual(node.Tag.Thunk, t.tag);
    try std.testing.expectEqual(env, node.thunkEnv(t));
}

test "runtime: evaluate indirection follows chain" {
    heap.init();
    defer heap.deinit();

    const target = node.createInt(7);
    const ind = node.createInd(target);

    const result = eval.rts_eval(ind);
    try std.testing.expectEqual(target, result);
    try std.testing.expectEqual(node.Tag.Int, result.tag);
}

test "runtime: evaluate double indirection follows chain" {
    heap.init();
    defer heap.deinit();

    const target = node.createInt(5);
    const ind2 = node.createInd(target);
    const ind1 = node.createInd(ind2);

    const result = eval.rts_eval(ind1);
    try std.testing.expectEqual(target, result);
}

test "runtime: evaluate thunk forces and memoizes" {
    heap.init();
    defer heap.deinit();

    const ThunkHelper = struct {
        fn evalFn(env: *node.Node) callconv(.auto) *node.Node {
            _ = env;
            return node.createInt(42);
        }
    };

    const env = node.createUnit();
    const thunk = node.createThunk(ThunkHelper.evalFn, env);
    try std.testing.expectEqual(node.Tag.Thunk, thunk.tag);

    const result = eval.rts_eval(thunk);
    try std.testing.expectEqual(node.Tag.Int, result.tag);

    // The thunk node should now be an Ind to the result.
    try std.testing.expectEqual(node.Tag.Ind, thunk.tag);
    try std.testing.expectEqual(result, node.indTarget(thunk));

    // A second call should follow the Ind without re-evaluating.
    const result2 = eval.rts_eval(thunk);
    try std.testing.expectEqual(result, result2);
}

test "runtime: evaluate thunk chain (thunk returns thunk)" {
    heap.init();
    defer heap.deinit();

    // Thunk that returns another thunk that returns an Int.
    const ThunkHelper = struct {
        fn inner(env: *node.Node) callconv(.auto) *node.Node {
            _ = env;
            return node.createInt(77);
        }
        fn outer(env: *node.Node) callconv(.auto) *node.Node {
            return node.createThunk(inner, env);
        }
    };

    const env = node.createUnit();
    const thunk = node.createThunk(ThunkHelper.outer, env);
    const result = eval.rts_eval(thunk);
    try std.testing.expectEqual(node.Tag.Int, result.tag);
}

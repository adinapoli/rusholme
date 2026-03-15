//! REPL TDD Tests
//!
//! Test-driven development for REPL behavior.
//! Tests are written first, then implementation is fixed to make them pass.

const std = @import("std");
const testing = std.testing;
const rusholme = @import("rusholme");

// Use proper module imports via rusholme
const Session = rusholme.repl.session.Session;
const protocol = rusholme.repl.protocol;
const Status = protocol.Status;
const evaluate = protocol.evaluate;

const engine_mod = rusholme.repl.engine;
const GrinEngine = engine_mod.GrinEngine;
const grin_ast = rusholme.grin.ast;

const testing_io = testing.io;

// ── Test: literal expressions ─────────────────────────────────────────────

test "repl: evaluate integer literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "42") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("42", result.value);
}

test "repl: evaluate string literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "\"hello\"") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("\"hello\"", result.value);
}

test "repl: evaluate boolean literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "True") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("True", result.value);
}

// ── Test: simple declarations ────────────────────────────────────────────

test "repl: define function silently" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    // Declaration should succeed silently
    try testing.expectEqual(Status.silent, result.status);
    try testing.expectEqualStrings("", result.value);
}

test "repl: define then use function" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define id
    const decl_result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use id
    const use_result = evaluate(alloc, &session, "id 42") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, use_result.status);
    try testing.expectEqualStrings("42", use_result.value);
}

// ── Test: IO expressions ─────────────────────────────────────────────────

test "repl: putStrLn \"hello\" returns unit" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Execute putStrLn "hello"
    const result = evaluate(alloc, &session, "putStrLn \"hello\"") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    // IO actions return Unit, which maps to empty value / silent status
    try testing.expectEqual(Status.silent, result.status);
    try testing.expectEqualStrings("", result.value);
}

// ── Integration tests for let-defined functions with IO ───────────────

test "repl: define function then use with putStrLn" {
    // This tests the issue reported: putStrLn (f "hello") where f was defined earlier
    // Previously caused ModuleAddFailed error due to premature context disposal
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define a simple function
    const decl_result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use it with putStrLn — IO actions return Unit (silent)
    const use_result = evaluate(alloc, &session, "putStrLn (id \"hello\")") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, use_result.status);
    try testing.expectEqualStrings("", use_result.value);
}

test "repl: multiple function definitions" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define multiple functions
    const decl1 = evaluate(alloc, &session, "f x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl1.status);

    const decl2 = evaluate(alloc, &session, "g y = y") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl2.status);

    // Use both
    const use = evaluate(alloc, &session, "f (g 42)") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, use.status);
    try testing.expectEqualStrings("42", use.value);
}

test "repl: function call after declaration accumulates correctly" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define identity function
    const decl_result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use it multiple times - each should work without failing
    for ([_]u8{0}**3) |_| {
        const use_result = evaluate(alloc, &session, "id 99") catch |err| {
            std.debug.panic("evaluate failed: {}", .{err});
        };
        try testing.expectEqual(Status.success, use_result.status);
        try testing.expectEqualStrings("99", use_result.value);
    }
}

// ── Test: error recovery ─────────────────────────────────────────────────

test "repl: error recovery — bad then good" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Evaluate an undefined identifier — should fail
    const bad_result = evaluate(alloc, &session, "not_defined_xyz") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.failed, bad_result.status);

    // Evaluate a valid expression — session should not be corrupted
    const good_result = evaluate(alloc, &session, "42") catch |err| {
        std.debug.panic("evaluate failed after error: {}", .{err});
    };
    try testing.expectEqual(Status.success, good_result.status);
    try testing.expectEqualStrings("42", good_result.value);
}

// ── Test: chained declarations ───────────────────────────────────────────

test "repl: chained declarations" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define wrap — wraps a value in identity
    // (Avoids arithmetic operators which require Num typeclass support)
    const decl1 = evaluate(alloc, &session, "wrap x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl1.status);

    // Define apply in terms of wrap
    const decl2 = evaluate(alloc, &session, "apply x = wrap (wrap x)") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl2.status);

    // Use apply — should chain through wrap twice and return the value
    const result = evaluate(alloc, &session, "apply 3") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("3", result.value);
}

// ── Test: multiline block via joined content ─────────────────────────────

test "repl: multiline block via joined content" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Send two declarations joined by a newline, simulating a :{ ... :} block
    const decl_result = evaluate(alloc, &session, "f x = x\ng y = f y") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    // We expect the declaration(s) to be accepted silently
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use the second function, which depends on the first
    const use_result = evaluate(alloc, &session, "g 42") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, use_result.status);
    try testing.expectEqualStrings("42", use_result.value);
}

// ── Test: empty input ────────────────────────────────────────────────────

test "repl: empty input" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Empty input should not crash the session
    _ = evaluate(alloc, &session, "") catch {};

    // Verify session still works
    const result = evaluate(alloc, &session, "42") catch |err| {
        std.debug.panic("evaluate failed after empty input: {}", .{err});
    };
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("42", result.value);
}

// ── Test: whitespace-only input ──────────────────────────────────────────

test "repl: whitespace-only input" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Whitespace-only input should not crash the session
    _ = evaluate(alloc, &session, "   ") catch {};

    // Verify session still works
    const result = evaluate(alloc, &session, "42") catch |err| {
        std.debug.panic("evaluate failed after whitespace input: {}", .{err});
    };
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("42", result.value);
}

// ── Test: let syntax ─────────────────────────────────────────────────────

// ── Test: GrinEngine path (simulates WASM REPL) ─────────────────────

test "repl: GrinEngine — define then use function (WASM path)" {
    // This test exercises the exact code path the WASM REPL takes:
    // 1. Compile a declaration, accumulate its GRIN defs
    // 2. Compile an expression that references the declaration
    // 3. Merge accumulated_defs + expression def into one program
    // 4. Execute via GrinEngine (tree-walking evaluator)
    //
    // On native, session.eval() uses JitEngine which resolves symbols
    // via the ORC linker. On WASM, it uses GrinEngine which needs all
    // defs in a single program. This test catches WASM-specific failures.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Step 1: Define identity function
    const decl = session.processInput("let identity x = x") catch |err| {
        std.debug.panic("Declaration compilation failed: {}", .{err});
    };
    try testing.expect(decl.compile.kind == .declaration_let_stripped);

    // Step 2: Compile expression that uses identity
    const expr = session.processInput("identity 42") catch |err| {
        std.debug.panic("Expression compilation failed: {}", .{err});
    };
    try testing.expect(expr.compile.kind == .expression);

    // Step 3: Merge accumulated_defs + expression def (exactly as Session.eval does for WASM)
    const total_defs = session.accumulated_defs.items.len + expr.compile.program.defs.len;
    const all_defs = try alloc.alloc(grin_ast.Def, total_defs);

    for (session.accumulated_defs.items, 0..) |def, i| {
        all_defs[i] = def;
    }
    for (expr.compile.program.defs, 0..) |def, i| {
        all_defs[session.accumulated_defs.items.len + i] = def;
    }

    const merged_program = grin_ast.Program{ .defs = all_defs };

    // Step 4: Execute via GrinEngine (the WASM path)
    var engine = GrinEngine.init(alloc, testing_io);
    const result = engine.execute(&merged_program) catch |err| {
        std.debug.panic("GrinEngine execution failed: {s}", .{@errorName(err)});
    };

    try testing.expectEqualStrings("42", result.value);
}

test "repl: GrinEngine — define then use with putStrLn (WASM path)" {
    // Tests the specific failure case: putStrLn (identity "hello")
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define identity
    _ = session.processInput("let identity x = x") catch |err| {
        std.debug.panic("Declaration failed: {}", .{err});
    };

    // Compile putStrLn (identity "hello")
    const expr = session.processInput("putStrLn (identity \"hello\")") catch |err| {
        std.debug.panic("Expression compilation failed: {}", .{err});
    };

    // Merge and execute via GrinEngine
    const total_defs = session.accumulated_defs.items.len + expr.compile.program.defs.len;
    const all_defs = try alloc.alloc(grin_ast.Def, total_defs);

    for (session.accumulated_defs.items, 0..) |def, i| {
        all_defs[i] = def;
    }
    for (expr.compile.program.defs, 0..) |def, i| {
        all_defs[session.accumulated_defs.items.len + i] = def;
    }

    const merged_program = grin_ast.Program{ .defs = all_defs };

    var engine = GrinEngine.init(alloc, testing_io);
    const result = engine.execute(&merged_program) catch |err| {
        std.debug.panic("GrinEngine execution failed: {s}", .{@errorName(err)});
    };

    // IO actions return Unit, which formats as empty string
    try testing.expectEqualStrings("", result.value);
}

test "repl: let syntax" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // GHCi-style let binding
    const decl_result = evaluate(alloc, &session, "let f x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use the let-bound function
    const use_result = evaluate(alloc, &session, "f 99") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, use_result.status);
    try testing.expectEqualStrings("99", use_result.value);
}

// ── Test: issue #494 — :load then evaluate main ─────────────────────────

test "repl: GrinEngine — load then evaluate main (WASM :load path, issue #494)" {
    // This test reproduces the exact WASM REPL :load flow:
    // 1. Compile "main = putStrLn \"hello\"" as a declaration
    // 2. Compile "main" as an expression
    // 3. Merge accumulated_defs + expression def
    // 4. Execute via GrinEngine (tree-walking evaluator)
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Step 1: Load file body (declaration)
    _ = session.processInput("main = putStrLn \"hello\"") catch |err| {
        std.debug.panic("Declaration compilation failed: {}", .{err});
    };

    // Step 2: Compile expression "main"
    const expr = session.processInput("main") catch |err| {
        std.debug.panic("Expression compilation failed: {s}", .{@errorName(err)});
    };
    try testing.expect(expr.compile.kind == .expression);

    // Step 3: Merge accumulated_defs + expression def
    const total_defs = session.accumulated_defs.items.len + expr.compile.program.defs.len;
    const all_defs = try alloc.alloc(grin_ast.Def, total_defs);

    for (session.accumulated_defs.items, 0..) |def, i| {
        all_defs[i] = def;
    }
    for (expr.compile.program.defs, 0..) |def, i| {
        all_defs[session.accumulated_defs.items.len + i] = def;
    }

    const merged_program = grin_ast.Program{ .defs = all_defs };

    // Step 4: Execute via GrinEngine (the WASM path)
    var engine = GrinEngine.init(alloc, testing_io);
    const result = engine.execute(&merged_program) catch |err| {
        std.debug.panic("GrinEngine execution failed: {s}", .{@errorName(err)});
    };

    // putStrLn returns IO Unit, which formats as empty string
    try testing.expectEqualStrings("", result.value);
}

test "repl: load file body then evaluate main (issue #494)" {
    // Simulates the browser REPL :load flow:
    // 1. User loads a file, JS strips "module Main where\n" header
    // 2. File body is sent as a single evaluate() call
    // 3. User types "main" to run the loaded program
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Step 1: Simulate :load by sending stripped file body
    const load_result = evaluate(alloc, &session, "main = putStrLn \"hello\"") catch |err| {
        std.debug.panic("load evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, load_result.status);

    // Step 2: Type "main" — should execute the loaded main
    const main_result = evaluate(alloc, &session, "main") catch |err| {
        std.debug.panic("main evaluate failed: {}", .{err});
    };
    // putStrLn returns IO (), which should be silent (empty value)
    try testing.expectEqual(Status.silent, main_result.status);
}

test "repl: multi-declaration load then evaluate main (issue #494 reproducer)" {
    // Reproduces the browser REPL scenario where a multi-declaration
    // .hs file is loaded, then "main" is evaluated. The file body
    // (with module header stripped) is sent as a single evaluate() call.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Simulate loading a file with multiple declarations (like a 25-line hello.hs)
    const file_body =
        \\greet name = putStrLn name
        \\
        \\main = greet "hello"
    ;

    const load_result = evaluate(alloc, &session, file_body) catch |err| {
        std.debug.panic("load evaluate failed: {s}", .{@errorName(err)});
    };
    try testing.expectEqual(Status.silent, load_result.status);

    // Now evaluate "main" — should find it from the loaded definitions
    const main_result = evaluate(alloc, &session, "main") catch |err| {
        std.debug.panic("main evaluate failed: {s}", .{@errorName(err)});
    };
    try testing.expectEqual(Status.silent, main_result.status);
}

// ── Test: ClassEnv persistence across REPL inputs (#557, #571) ────────

test "repl: class declaration persists for instance in next input (#557)" {
    // Regression test for #557: ClassEnv was not persisted across REPL
    // inputs, so a class declared in one input was invisible to instance
    // declarations in subsequent inputs. The fix seeds each new InferCtx
    // from the session's accumulated ClassEnv.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Input 1: Define a custom class
    const class_result = session.processInput("class Describe a where\n  describe :: a -> String");
    if (class_result) |r| {
        try testing.expect(r.compile.kind == .declaration);
    } else |err| {
        std.debug.panic("Class declaration failed: {}", .{err});
    }

    // Input 2: Define an instance of that class — this requires the
    // class to be in the ClassEnv from the prior input.
    const instance_result = session.processInput("instance Describe Bool where\n  describe True = \"yes\"\n  describe False = \"no\"");
    if (instance_result) |r| {
        try testing.expect(r.compile.kind == .declaration);
    } else |err| {
        std.debug.panic("Instance declaration failed (ClassEnv not persisted?): {}", .{err});
    }
}

test "repl: class and instance in same input, used in next input (#557)" {
    // Define a class and instance together, then use the class method
    // in a subsequent expression. Tests that both the class and its
    // instances are available for constraint solving in later inputs.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Input 1: Define class + instance together
    const decl_result = session.processInput(
        "class Describe a where\n  describe :: a -> String\n\ninstance Describe Bool where\n  describe True = \"yes\"\n  describe False = \"no\"",
    );
    if (decl_result) |r| {
        try testing.expect(r.compile.kind == .declaration);
    } else |err| {
        std.debug.panic("Class+instance declaration failed: {}", .{err});
    }

    // Input 2: Use the class method — requires ClassEnv persistence
    // so that the constraint solver can find the Describe Bool instance.
    const expr_result = session.processInput("describe True");
    if (expr_result) |r| {
        try testing.expect(r.compile.kind == .expression);
    } else |err| {
        std.debug.panic("Expression using class method failed (ClassEnv not persisted?): {}", .{err});
    }
}

test "repl: multiple classes accumulate across inputs (#557)" {
    // Ensure that multiple class declarations across separate inputs
    // all persist and don't overwrite each other.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Input 1: Define first class
    const class1 = session.processInput("class Foo a where\n  foo :: a -> Int");
    if (class1) |r| {
        try testing.expect(r.compile.kind == .declaration);
    } else |err| {
        std.debug.panic("First class declaration failed: {}", .{err});
    }

    // Input 2: Define second class
    const class2 = session.processInput("class Bar a where\n  bar :: a -> String");
    if (class2) |r| {
        try testing.expect(r.compile.kind == .declaration);
    } else |err| {
        std.debug.panic("Second class declaration failed: {}", .{err});
    }

    // Input 3: Instance for first class — must still be in ClassEnv
    const inst1 = session.processInput("instance Foo Bool where\n  foo True = 1\n  foo False = 0");
    if (inst1) |r| {
        try testing.expect(r.compile.kind == .declaration);
    } else |err| {
        std.debug.panic("Instance for Foo failed (first class lost?): {}", .{err});
    }

    // Input 4: Instance for second class — must also still be in ClassEnv
    const inst2 = session.processInput("instance Bar Bool where\n  bar True = \"true\"\n  bar False = \"false\"");
    if (inst2) |r| {
        try testing.expect(r.compile.kind == .declaration);
    } else |err| {
        std.debug.panic("Instance for Bar failed (second class lost?): {}", .{err});
    }
}

test "repl: load file with comments then evaluate main (issue #494)" {
    // Reproduces the browser REPL scenario with a file containing
    // comments and blank lines — typical of a real .hs file.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Simulate a file body after stripping "module Main where\n"
    // This is what a typical hello.hs might look like.
    const file_body =
        \\-- A simple greeting program
        \\
        \\greet name = putStrLn name
        \\
        \\-- Main entry point
        \\main = greet "hello"
    ;

    const load_result = evaluate(alloc, &session, file_body) catch |err| {
        std.debug.panic("load evaluate failed: {s}", .{@errorName(err)});
    };
    try testing.expectEqual(Status.silent, load_result.status);

    // Now evaluate "main"
    const main_result = evaluate(alloc, &session, "main") catch |err| {
        std.debug.panic("main evaluate failed: {s}", .{@errorName(err)});
    };
    try testing.expectEqual(Status.silent, main_result.status);
}

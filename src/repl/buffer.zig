//! Shared buffer management for WASM/JavaScript bridge
//! 
//! Manages linear memory buffers for passing data between
//! JavaScript and WebAssembly.

const std = @import("std");

// Shared buffers for input/output
var input_buffer: [4096]u8 = undefined;
var output_buffer: [16384]u8 = undefined;

pub fn writeToBuffer(buffer: []u8, data: []const u8) !void {
    if (data.len > buffer.len) return error.BufferOverflow;
    @memcpy(buffer[0..data.len], data);
}

pub fn jsonString(data: []const u8) []const u8 {
    // Write to output_buffer and return pointer
    const len = @min(data.len, output_buffer.len);
    @memcpy(&output_buffer, data[0..len]);
    return output_buffer[0..len];
}

pub fn getInputBuffer() [*]u8 {
    return &input_buffer;
}

pub fn getOutputBuffer() [*]u8 {
    return &output_buffer;
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "buffer write" {
    var buffer: [64]u8 = undefined;
    const data = "hello";
    try writeToBuffer(&buffer, data);
    try testing.expectEqualStrings("hello", buffer[0..data.len]);
}

test "buffer write overflow" {
    var buffer: [4]u8 = undefined;
    const data = "hello";
    try testing.expectError(error.BufferOverflow, writeToBuffer(&buffer, data));
}

test "jsonString" {
    const data = "test output";
    const result = jsonString(data);
    try testing.expectEqualStrings("test output", result);
}

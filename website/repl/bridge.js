// Rusholme REPL — WASM bridge
//
// Initialises the wasm32-wasi REPL module, providing a minimal WASI
// shim so that Zig's std library functions (fd_write, proc_exit, etc.)
// work in the browser. IO output is routed to the xterm.js terminal.
//
// See docs/decisions/0006-repl-architecture.md for the full design.

// ── Minimal WASI shim ────────────────────────────────────────────────
//
// The WASM binary imports wasi_snapshot_preview1 functions. We provide
// stub implementations for the ones Zig's standard library emits. Only
// fd_write (for stdout/stderr) does real work — everything else is a
// no-op or returns ENOSYS (52).

function createWasiShim(wasmInstance) {
    return {
        // fd_write(fd, iovs_ptr, iovs_len, nwritten_ptr) -> errno
        // Implements stdout/stderr output by reading iovec structs from
        // linear memory and routing the text to the terminal.
        fd_write(fd, iovs_ptr, iovs_len, nwritten_ptr) {
            const mem = new DataView(wasmInstance.exports.memory.buffer);
            let totalWritten = 0;

            for (let i = 0; i < iovs_len; i++) {
                const bufPtr = mem.getUint32(iovs_ptr + i * 8, true);
                const bufLen = mem.getUint32(iovs_ptr + i * 8 + 4, true);
                const bytes = new Uint8Array(wasmInstance.exports.memory.buffer, bufPtr, bufLen);
                const text = new TextDecoder().decode(bytes);

                if (fd === 1 || fd === 2) {
                    // stdout or stderr → terminal
                    if (typeof terminal !== 'undefined' && terminal.writeLine) {
                        terminal.writeLine(text);
                    } else {
                        console.log(text);
                    }
                }
                totalWritten += bufLen;
            }

            mem.setUint32(nwritten_ptr, totalWritten, true);
            return 0; // ESUCCESS
        },

        // fd_read(fd, iovs_ptr, iovs_len, nread_ptr) -> errno
        fd_read() { return 52; }, // ENOSYS

        // fd_close(fd) -> errno
        fd_close() { return 0; },

        // fd_seek(fd, offset, whence, newoffset_ptr) -> errno
        fd_seek() { return 52; },

        // fd_fdstat_get(fd, buf) -> errno
        fd_fdstat_get(fd, buf) {
            const mem = new DataView(wasmInstance.exports.memory.buffer);
            // filetype = REGULAR_FILE (4), flags = 0
            mem.setUint8(buf, 4);
            mem.setUint16(buf + 2, 0, true);
            // rights_base and rights_inheriting = all bits set
            mem.setBigUint64(buf + 8, 0n, true);
            mem.setBigUint64(buf + 16, 0n, true);
            return 0;
        },

        // fd_prestat_get(fd, buf) -> errno
        fd_prestat_get() { return 8; }, // EBADF — no preopens

        // fd_prestat_dir_name(fd, path, path_len) -> errno
        fd_prestat_dir_name() { return 8; }, // EBADF

        // fd_pwrite(fd, iovs, iovs_len, offset, nwritten) -> errno
        fd_pwrite() { return 52; },

        // fd_pread(fd, iovs, iovs_len, offset, nread) -> errno
        fd_pread() { return 52; },

        // fd_sync(fd) -> errno
        fd_sync() { return 52; },

        // fd_filestat_get(fd, buf) -> errno
        fd_filestat_get() { return 8; }, // EBADF

        // fd_filestat_set_size(fd, size) -> errno
        fd_filestat_set_size() { return 52; },

        // fd_filestat_set_times(fd, atim, mtim, fst_flags) -> errno
        fd_filestat_set_times() { return 52; },

        // fd_readdir(fd, buf, buf_len, cookie, bufused) -> errno
        fd_readdir() { return 52; },

        // path_open(...) -> errno
        path_open() { return 52; },

        // path_link(...) -> errno
        path_link() { return 52; },

        // path_create_directory(fd, path, path_len) -> errno
        path_create_directory() { return 52; },

        // path_filestat_get(fd, flags, path, path_len, buf) -> errno
        path_filestat_get() { return 52; },

        // path_unlink_file(fd, path, path_len) -> errno
        path_unlink_file() { return 52; },

        // path_remove_directory(fd, path, path_len) -> errno
        path_remove_directory() { return 52; },

        // path_rename(fd, old_path, old_path_len, new_fd, new_path, new_path_len) -> errno
        path_rename() { return 52; },

        // path_symlink(old_path, old_path_len, fd, new_path, new_path_len) -> errno
        path_symlink() { return 52; },

        // path_readlink(fd, path, path_len, buf, buf_len, bufused) -> errno
        path_readlink() { return 52; },

        // proc_exit(code)
        proc_exit(code) {
            console.log(`WASM proc_exit(${code})`);
        },

        // environ_sizes_get(count_ptr, buf_size_ptr) -> errno
        environ_sizes_get(count_ptr, buf_size_ptr) {
            const mem = new DataView(wasmInstance.exports.memory.buffer);
            mem.setUint32(count_ptr, 0, true);
            mem.setUint32(buf_size_ptr, 0, true);
            return 0;
        },

        // environ_get(environ_ptr, environ_buf_ptr) -> errno
        environ_get() { return 0; },

        // clock_time_get(clock_id, precision, time_ptr) -> errno
        clock_time_get(clock_id, precision, time_ptr) {
            const mem = new DataView(wasmInstance.exports.memory.buffer);
            const now = BigInt(Date.now()) * 1000000n; // ms → ns
            mem.setBigUint64(time_ptr, now, true);
            return 0;
        },

        // clock_res_get(clock_id, resolution_ptr) -> errno
        clock_res_get(clock_id, resolution_ptr) {
            const mem = new DataView(wasmInstance.exports.memory.buffer);
            mem.setBigUint64(resolution_ptr, 1000000n, true); // 1ms
            return 0;
        },

        // poll_oneoff(in, out, nsubscriptions, nevents) -> errno
        poll_oneoff() { return 52; },

        // args_sizes_get(argc_ptr, argv_buf_size_ptr) -> errno
        args_sizes_get(argc_ptr, argv_buf_size_ptr) {
            const mem = new DataView(wasmInstance.exports.memory.buffer);
            mem.setUint32(argc_ptr, 0, true);
            mem.setUint32(argv_buf_size_ptr, 0, true);
            return 0;
        },

        // args_get(argv_ptr, argv_buf_ptr) -> errno
        args_get() { return 0; },

        // random_get(buf, buf_len) -> errno
        random_get(buf, buf_len) {
            const bytes = new Uint8Array(wasmInstance.exports.memory.buffer, buf, buf_len);
            crypto.getRandomValues(bytes);
            return 0;
        },
    };
}

// ── REPL bridge ──────────────────────────────────────────────────────

window.replBridge = {
    wasmInstance: null,
    inputBuffer: null,
    outputBuffer: null,

    decodeString(ptr, len) {
        const bytes = new Uint8Array(this.wasmInstance.exports.memory.buffer, ptr, len);
        return new TextDecoder().decode(bytes);
    },

    encodeString(str) {
        const encoder = new TextEncoder();
        const bytes = encoder.encode(str);
        const inputPtr = this.wasmInstance.exports.repl_get_input_buffer();
        const inputView = new Uint8Array(this.wasmInstance.exports.memory.buffer, inputPtr);
        for (let i = 0; i < bytes.length && i < inputView.length; i++) {
            inputView[i] = bytes[i];
        }
        return bytes.length;
    },

    async init() {
        try {
            const response = await fetch('repl.wasm');
            const bytes = await response.arrayBuffer();
            const module = await WebAssembly.compile(bytes);

            // Two-phase instantiation: first create the instance with
            // a proxy shim, then patch in the real shim that can read
            // the instance's memory.
            const wasiStub = {};
            const handler = {
                get(_target, prop) {
                    return (...args) => {
                        if (wasiStub.impl && wasiStub.impl[prop]) {
                            return wasiStub.impl[prop](...args);
                        }
                        console.warn(`WASI stub: ${prop} not implemented`);
                        return 52; // ENOSYS
                    };
                },
            };
            const wasiProxy = new Proxy(wasiStub, handler);

            this.wasmInstance = await WebAssembly.instantiate(module, {
                wasi_snapshot_preview1: wasiProxy,
            });

            // Now wire the real shim that can access memory.
            wasiStub.impl = createWasiShim(this.wasmInstance);

            // Run _start if present (WASI convention), then init the REPL.
            if (this.wasmInstance.exports._start) {
                this.wasmInstance.exports._start();
            }
            this.wasmInstance.exports.repl_init();

            this.inputBuffer = this.wasmInstance.exports.repl_get_input_buffer();
            this.outputBuffer = this.wasmInstance.exports.repl_get_output_buffer();

            terminal.showPrompt();
        } catch (error) {
            console.error('Failed to load WASM module:', error);
            terminal.writeLine('Failed to initialize Rusholme REPL: ' + error.message);
        }
    },

    evaluate(expr) {
        if (!this.wasmInstance) {
            terminal.writeLine('Error: REPL not initialized');
            terminal.showPrompt();
            return;
        }

        try {
            const len = this.encodeString(expr);
            const resultLen = this.wasmInstance.exports.repl_evaluate(len);
            const jsonString = this.decodeString(this.outputBuffer, resultLen);
            const data = JSON.parse(jsonString);

            if (data.status === 'error') {
                terminal.writeLine('Error: ' + data.message);
            } else {
                terminal.writeLine(data.value || '<no value>');
            }
            terminal.showPrompt();
        } catch (error) {
            terminal.writeLine('Error: ' + error.message);
            terminal.showPrompt();
        }
    },
};

replBridge.init().catch(console.error);

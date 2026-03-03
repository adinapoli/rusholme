// Step 1 of task 10: WASM bridge implementation
window.replBridge = {
    wasmInstance: null,
    inputBuffer: null,
    outputBuffer: null,

    // Decode UTF-8 string from WASM memory
    decodeString: function(ptr, len) {
        const bytes = new Uint8Array(this.wasmInstance.exports.memory.buffer, ptr, len);
        return new TextDecoder().decode(bytes);
    },

    // Encode UTF-8 string to WASM memory
    encodeString: function(str) {
        const encoder = new TextEncoder();
        const bytes = encoder.encode(str);

        // Copy bytes to input buffer
        const inputPtr = this.wasmInstance.exports.repl_get_input_buffer();
        const inputView = new Uint8Array(this.wasmInstance.exports.memory.buffer, inputPtr);

        for (let i = 0; i < bytes.length && i < inputView.length; i++) {
            inputView[i] = bytes[i];
        }

        return bytes.length;
    },

    // Initialize WASM module
    init: async function() {
        try {
            const response = await fetch('repl.wasm');
            const bytes = await response.arrayBuffer();
            const module = await WebAssembly.compile(bytes);

            // Create imports (empty for now - callbacks not supported in wasm exports)
            const imports = {
                env: {},
            };

            this.wasmInstance = await WebAssembly.instantiate(module, imports);

            // Initialize REPL
            this.wasmInstance.exports.repl_init();

            // Get buffer pointers
            this.inputBuffer = this.wasmInstance.exports.repl_get_input_buffer();
            this.outputBuffer = this.wasmInstance.exports.repl_get_output_buffer();

            terminal.showPrompt();
        } catch (error) {
            console.error('Failed to load WASM module:', error);
            terminal.writeLine('Failed to initialize Rusholme REPL (WASM module not found)');
        }
    },

    // Evaluate Haskell expression
    evaluate: function(expr) {
        if (!this.wasmInstance) {
            terminal.writeLine('Error: REPL not initialized');
            terminal.showPrompt();
            return;
        }

        try {
            // Write expression to input buffer
            const len = this.encodeString(expr);

            // Call evaluation and get result length
            const resultLen = this.wasmInstance.exports.repl_evaluate(len);

            // Read JSON response from output buffer (always at offset 0)
            const jsonString = this.decodeString(this.outputBuffer, resultLen);
            const data = JSON.parse(jsonString);

            if (data.status === 'error') {
                terminal.writeLine(`Error: ${data.type} - ${data.message}`);
            } else {
                terminal.writeLine(data.value || '<no value>');
            }

            terminal.showPrompt();
        } catch (error) {
            terminal.writeLine(`Error: ${error.message}`);
            terminal.showPrompt();
        }
    },
};

// Initialize bridge and REPL
replBridge.init().catch(console.error);

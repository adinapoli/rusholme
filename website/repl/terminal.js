// xterm.js terminal setup - Step 1 of task 8
const term = new Terminal({
    fontSize: 14,
    fontFamily: "'Menlo', 'Monaco', 'Courier New', monospace",
    theme: {
        background: '#0a0a0f',
        foreground: '#f0f0f0',
        cursor: '#f0f0f0',
        selection: 'rgba(255, 255, 255, 0.3)',
    },
});

const fitAddon = new FitAddon.FitAddon();
term.loadAddon(fitAddon);

// Mount terminal to DOM
term.open(document.getElementById('terminal'));
fitAddon.fit();

// Welcome message
term.writeln('Rusholme WASM REPL');
term.writeln('Type Haskell expressions and definitions, then press Enter to evaluate.');
term.writeln('For multi-line blocks, surround with :{ and :}');
term.writeln('');

// Expose writeLine function for bridge to use
window.terminal = {
    term: term,
    writeLine: function(text) {
        term.writeln(text);
    },
    showPrompt: function() {
        term.write('> ');
    },
    onData: function(callback) {
        term.onData(callback);
    },
    fit: function() {
        fitAddon.fit();
    },
};

window.addEventListener('resize', () => fitAddon.fit());

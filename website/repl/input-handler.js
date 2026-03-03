// Enter key handling - Step 1 of task 9
let currentLine = '';

terminal.onData((data) => {
    const code = data.charCodeAt(0);

    if (code === 13) { // Enter
        // Submit the line for evaluation
        if (currentLine.trim()) {
            window.replBridge.evaluate(currentLine);
            currentLine = '';
        }
        terminal.showPrompt();
    } else if (code === 3) { // Ctrl+C
        // Clear current line and show prompt
        terminal.writeln('^C');
        currentLine = '';
        terminal.showPrompt();
    } else if (code >= 32 && code <= 126) { // Printable characters
        currentLine += data;
        terminal.write(data);
    } else if (code === 127) { // Backspace
        if (currentLine.length > 0) {
            currentLine = currentLine.slice(0, -1);
            terminal.write('\x1b[D \x1b[D'); // Move cursor back, clear space, move back again
        }
    }
    // Other control codes (arrows, etc.) can be handled as extensions
});

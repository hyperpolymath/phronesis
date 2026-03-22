# Phronesis VSCode Extension

VSCode extension for Phronesis policy language with LSP support.

## Features

- **Syntax Highlighting** - Full language support
- **Auto-Completion** - Keywords, stdlib functions, variables
- **Hover Documentation** - Inline docs for functions and keywords
- **Go to Definition** - Jump to policy/constant definitions
- **Real-time Diagnostics** - Syntax errors and warnings
- **Code Formatting** - Auto-format on save

## Installation

### From Source

1. **Build the extension:**
   ```bash
   cd editors/vscode
   npm install
   npm run compile
   ```

2. **Install phronesis CLI:**
   ```bash
   mix escript.build
   # Add to PATH or configure extension
   ```

3. **Install extension:**
   ```bash
   code --install-extension phronesis-0.2.0.vsix
   ```

   Or copy to extensions directory:
   ```bash
   cp -r . ~/.vscode/extensions/phronesis-0.2.0/
   ```

### Configuration

Open VSCode settings and configure:

```json
{
  "phronesis.serverPath": "/path/to/phronesis",
  "phronesis.trace.server": "off"
}
```

## Usage

1. Open a `.phr` file
2. LSP server starts automatically
3. Auto-completion: Type `Std.` to see stdlib modules
4. Hover over keywords/functions for documentation
5. F12 / Cmd+Click for go-to-definition

## Features in Detail

### Auto-Completion

- **Keywords**: `POLICY`, `CONST`, `IMPORT`, `ACCEPT`, `REJECT`, etc.
- **Standard Library**: `Std.RPKI.*`, `Std.BGP.*`, `Std.Consensus.*`, `Std.Temporal.*`
- **Functions**: All stdlib functions with signatures

Example:
```phronesis
Std.R  # Auto-complete shows: Std.RPKI
Std.RPKI.  # Shows: validate, check_origin, validation_status
```

### Hover Documentation

Hover over any keyword or function to see:
- Syntax
- Parameters
- Return type
- Examples

### Diagnostics

Real-time error checking:
- Syntax errors (lexer/parser)
- Linter warnings
- Type issues

### Formatting

Format document: `Shift+Alt+F` or save with format-on-save enabled.

## Troubleshooting

### LSP server not starting

1. Check phronesis is installed:
   ```bash
   which phronesis
   phronesis --version
   ```

2. Check server path in settings
3. View LSP logs: `Output` → `Phronesis Language Server`

### No auto-completion

1. Ensure `.phr` file is recognized as Phronesis language
2. Restart LSP: `Cmd+Shift+P` → "Restart Language Server"

## Development

### Build

```bash
npm install
npm run compile
```

### Watch Mode

```bash
npm run watch
```

### Package

```bash
npm install -g vsce
vsce package
```

## License

PMPL-1.0-or-later

## Links

- [Phronesis Repository](https://github.com/hyperpolymath/phronesis)
- [Language Specification](../../docs/draft-phronesis-policy-language.txt)
- [LSP Specification](https://microsoft.github.io/language-server-protocol/)

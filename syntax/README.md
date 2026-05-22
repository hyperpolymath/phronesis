# Phronesis Syntax Highlighting

This directory contains syntax highlighting definitions for various editors.

## Installation

### VSCode / VSCodium

1. Create extension directory:
   ```bash
   mkdir -p ~/.vscode/extensions/phronesis-lang
   ```

2. Copy files:
   ```bash
   cp phronesis.tmLanguage.json ~/.vscode/extensions/phronesis-lang/
   ```

3. Create `package.json`:
   ```json
   {
     "name": "phronesis",
     "displayName": "Phronesis Policy Language",
     "description": "Syntax highlighting for Phronesis (.phr files)",
     "version": "0.2.0",
     "engines": { "vscode": "^1.60.0" },
     "categories": ["Programming Languages"],
     "contributes": {
       "languages": [{
         "id": "phronesis",
         "aliases": ["Phronesis", "phronesis"],
         "extensions": [".phr"],
         "configuration": "./language-configuration.json"
       }],
       "grammars": [{
         "language": "phronesis",
         "scopeName": "source.phronesis",
         "path": "./phronesis.tmLanguage.json"
       }]
     }
   }
   ```

4. Reload VSCode

### Vim / Neovim

1. Copy to syntax directory:
   ```bash
   mkdir -p ~/.vim/syntax
   cp phronesis.vim ~/.vim/syntax/
   ```

2. Add to `~/.vim/ftdetect/phronesis.vim`:
   ```vim
   autocmd BufNewFile,BufRead *.phr set filetype=phronesis
   ```

3. (Optional) Add to `~/.vim/ftplugin/phronesis.vim`:
   ```vim
   setlocal commentstring=#\ %s
   setlocal tabstop=2
   setlocal shiftwidth=2
   setlocal expandtab
   ```

### Emacs

1. Copy to Emacs config:
   ```bash
   cp phronesis-mode.el ~/.emacs.d/lisp/
   ```

2. Add to `~/.emacs` or `~/.emacs.d/init.el`:
   ```elisp
   (add-to-list 'load-path "~/.emacs.d/lisp")
   (require 'phronesis-mode)
   ```

3. Reload Emacs or evaluate: `M-x eval-buffer`

### Sublime Text

TextMate grammars (`.tmLanguage.json`) work in Sublime Text:

1. Open Sublime Text
2. `Preferences` → `Browse Packages`
3. Create directory: `Phronesis/`
4. Copy `phronesis.tmLanguage.json` to `Phronesis/Phronesis.tmLanguage.json`
5. Restart Sublime Text

### Kate / KWrite

TODO: Create `phronesis.xml` syntax file for KDE editors.

### GitHub / GitLab

For syntax highlighting on GitHub:
1. Submit `linguist.yml` definition to [github/linguist](https://github.com/github/linguist)
2. Or add `.gitattributes` to your repo:
   ```
   *.phr linguist-language=Phronesis
   ```

## Features

All syntax definitions support:

- **Keywords**: `POLICY`, `CONST`, `IMPORT`, `IF`, `THEN`, `ELSE`, `AND`, `OR`, `NOT`, `IN`
- **Actions**: `ACCEPT`, `REJECT`, `REPORT`, `EXECUTE`, `BLOCK`
- **Metadata**: `PRIORITY`, `EXPIRES`, `CREATED_BY`
- **Test keywords**: `TEST`, `SCENARIO`, `GIVEN`, `EXPECT`
- **Types**: `Integer`, `String`, `Boolean`, `Float`, `List`, `Map`, `Route`
- **Constants**: `true`, `false`, `nil`, `null`, `never`, `always`
- **Standard library**: `Std.RPKI.*`, `Std.BGP.*`, `Std.Consensus.*`, `Std.Temporal.*`
- **Comments**: `# line comments`, `## block comments ##`
- **Strings**: `"double quoted"`, `'single quoted'`, `"${interpolation}"`
- **Numbers**: Integers, floats, hex (`0xFF`)
- **Operators**: `==`, `!=`, `>=`, `<=`, `>`, `<`, `+`, `-`, `*`, `/`, `%`, `&&`, `||`, `!`, `.`, `?.`

## Editor-Specific Features

### VSCode
- Bracket matching
- Auto-indentation
- Code folding

### Vim
- Syntax highlighting
- `commentstring` for comment toggling
- Indentation settings

### Emacs
- Major mode with keybindings:
  - `C-c C-c` - Run file
  - `C-c C-k` - Check syntax
  - `C-c C-p` - Parse and show AST
  - `C-c C-r` - Start REPL
- Auto-indentation
- Comment support

## Example

```phronesis
# BGP Security Policy
IMPORT Std.RPKI
IMPORT Std.BGP

CONST my_asn = 64512

POLICY rpki_validation:
  Std.RPKI.validate(route) == :invalid
  THEN REJECT("RPKI validation failed")
  PRIORITY: 200
  EXPIRES: never
  CREATED_BY: security_team

POLICY as_path_loop:
  my_asn IN Std.BGP.extract_as_path(route)
  THEN REJECT("AS path loop detected")
  PRIORITY: 300
```

## Contributing

To add support for a new editor:

1. Create syntax definition file
2. Test with sample `.phr` files
3. Document installation in this README
4. Submit PR

## License

MPL-2.0

## Maintainer

Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

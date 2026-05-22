# Phronesis Toolchain Wishlist
## Missing Components for Production-Grade Language

**Current Status:** Basic toolchain complete (45% overall)

**Existing Tools:** ✅
- Lexer, Parser, AST
- Compiler (bytecode + optimizer)
- Interpreter (basic + tracing)
- REPL (interactive mode)
- CLI (`phronesis run/parse/check/repl`)
- Formatter (code formatting)
- Linter (policy validation)
- Standard library (Consensus, BGP, RPKI, Temporal)
- Demo/Examples

---

## High Priority (Production Essentials)

### 1. Language Server Protocol (LSP) 📡
**Impact:** IDE integration, developer experience
**Effort:** 2-3 weeks

**Features:**
- Go to definition
- Find references
- Hover documentation
- Auto-completion
- Inline diagnostics (errors/warnings)
- Code actions (quick fixes)
- Rename symbol
- Signature help

**Implementation:**
```elixir
# lib/phronesis/lsp/server.ex
defmodule Phronesis.LSP.Server do
  # JSON-RPC server
  # textDocument/didOpen, didChange, didSave
  # textDocument/completion
  # textDocument/hover
  # textDocument/definition
  # textDocument/references
  # textDocument/formatting
end
```

**Why Critical:**
- VSCode/Neovim/Emacs integration
- Real-time error checking
- Autocomplete for Std.BGP.*, Std.RPKI.*, etc.
- Standard for modern languages

**Deliverable:** `phronesis lsp` command

---

### 2. Debugger 🐛
**Impact:** Policy development, troubleshooting
**Effort:** 1-2 weeks

**Features:**
- Breakpoints in policies
- Step-through execution
- Variable inspection
- Watch expressions
- Call stack
- Trace history navigation

**Implementation:**
```elixir
# lib/phronesis/debugger.ex
defmodule Phronesis.Debugger do
  # Instrument AST with breakpoints
  # Step-by-step evaluation
  # State inspection at each step
  # Integration with existing Trace module
end
```

**Why Critical:**
- Complex policies hard to debug
- Consensus failures need investigation
- Decision traces help but not interactive

**Deliverable:** `phronesis debug policy.phr`

---

### 3. Testing Framework 🧪
**Impact:** Policy reliability, CI/CD
**Effort:** 1 week

**Features:**
- Unit tests for policies
- Property-based testing
- Consensus simulation
- Network scenario testing
- Coverage reporting

**Implementation:**
```elixir
# lib/phronesis/test_framework.ex
defmodule Phronesis.Test do
  defmacro describe_policy(name, do: block)
  defmacro it(description, do: block)
  defmacro assert_accept(policy, situation)
  defmacro assert_reject(policy, situation, reason)
  defmacro assert_consensus(policy, agents, threshold)
end
```

**Test File Example:**
```phronesis
# test/bgp_security_test.phr
TEST "BGP Security Policy" {
  SCENARIO "RPKI invalid route" {
    GIVEN route = {prefix: "192.0.2.0/24", origin: 99999}
    EXPECT REJECT("RPKI validation failed")
  }

  SCENARIO "Valid route" {
    GIVEN route = {prefix: "192.0.2.0/24", origin: 64512}
    EXPECT ACCEPT()
  }
}
```

**Why Critical:**
- Network policies are safety-critical
- Regression testing essential
- CI/CD integration

**Deliverable:** `phronesis test` command

---

### 4. Documentation Generator 📚
**Impact:** API docs, onboarding
**Effort:** 1 week

**Features:**
- Auto-generate API docs from modules
- Policy documentation extraction
- Stdlib reference
- Examples/tutorials
- HTML/PDF output

**Implementation:**
```elixir
# lib/phronesis/doc.ex
defmodule Phronesis.Doc do
  # Extract doc comments from policies
  # Generate stdlib reference
  # Cross-reference policies
  # Export to HTML/Markdown
end
```

**Doc Comment Syntax:**
```phronesis
##
# Validates BGP routes against RPKI ROAs.
#
# @param route - BGP route with prefix and origin
# @returns :valid | :invalid | :not_found
# @example
#   route = {prefix: "192.0.2.0/24", origin: 64512}
#   Std.RPKI.validate(route)  // => :valid
##
```

**Why Critical:**
- Stdlib docs needed
- Policy sharing requires documentation
- Onboarding new users

**Deliverable:** `phronesis doc` command

---

### 5. Profiler & Benchmarking ⚡
**Impact:** Performance optimization
**Effort:** 1 week

**Features:**
- Policy execution time
- Module call profiling
- Consensus latency
- Memory usage
- Hotspot detection
- Flame graphs

**Implementation:**
```elixir
# lib/phronesis/profiler.ex
defmodule Phronesis.Profiler do
  # Instrument evaluation
  # Measure time per policy
  # Track module call counts
  # Memory allocation tracking
  # Export flamegraph.svg
end
```

**Why Critical:**
- Goal: 10k policies/sec
- Need to identify bottlenecks
- Consensus overhead measurement

**Deliverable:** `phronesis profile policy.phr`

---

## Medium Priority (Quality of Life)

### 6. Static Analyzer 🔍
**Impact:** Code quality, bug prevention
**Effort:** 1-2 weeks

**Features Beyond Linter:**
- Dead code detection
- Unreachable policy branches
- Unused imports
- Constant propagation analysis
- Consensus threshold validation
- Security vulnerability scanning

**Example Checks:**
```phronesis
# Warning: Policy 'never_matches' has unreachable condition
POLICY never_matches:
  false AND risk > 50
  THEN REJECT()

# Warning: Unused import
IMPORT Std.Temporal

# Error: Consensus threshold must be 0.0 to 1.0
CONST threshold = 1.5
```

**Deliverable:** `phronesis analyze policy.phr`

---

### 7. Package Manager 📦
**Impact:** Code reuse, ecosystem
**Effort:** 2-3 weeks

**Features:**
- Policy library publishing
- Dependency resolution
- Version management
- Standard library versioning
- Local/remote package registry

**Package Manifest:**
```nickel
# phronesis.ncl
{
  name = "acme-network-policies",
  version = "1.0.0",
  dependencies = {
    std = "^0.2.0",
    acme-common = "^2.1.0"
  },
  policies = [
    "bgp_security.phr",
    "rpki_validation.phr"
  ]
}
```

**Commands:**
```bash
phronesis pkg init
phronesis pkg install acme-common
phronesis pkg publish
phronesis pkg search rpki
```

**Deliverable:** `phronesis pkg` subcommand

---

### 8. Syntax Highlighting Definitions 🎨
**Impact:** Editor support
**Effort:** 2-3 days

**Targets:**
- VSCode/VSCodium (TextMate grammar)
- Vim/Neovim (vim syntax file)
- Emacs (major mode)
- Sublime Text
- Kate/KWrite
- GitHub/GitLab (linguist)

**Files to Create:**
```
syntax/
├── phronesis.tmLanguage.json  # VSCode/Sublime
├── phronesis.vim              # Vim/Neovim
├── phronesis-mode.el          # Emacs
└── phronesis.xml              # Kate
```

**Deliverable:** Editor plugin packages

---

### 9. Error Reporter & Diagnostics 🚨
**Impact:** Developer experience
**Effort:** 1 week

**Features:**
- Colorized error messages
- Source context (line + context)
- Suggestions for fixes
- Error codes (E0001, E0002, etc.)
- Related information
- Help text

**Example:**
```
error[E0042]: undefined variable 'risk_levle'
  --> bgp_security.phr:12:3
   |
12 |   risk_levle > 50
   |   ^^^^^^^^^^ not found in this scope
   |
help: a variable with a similar name exists
   |
12 |   risk_level > 50
   |   ~~~~~~~~~~
```

**Deliverable:** Enhanced error messages throughout

---

### 10. Code Completion Engine 🔮
**Impact:** IDE productivity
**Effort:** 1 week

**Features:**
- Module/function suggestions
- Variable name completion
- Snippet expansion
- Context-aware suggestions
- Policy template insertion

**Completions:**
```
Std.RPKI.v|  →  validate(route)
           |     validation_status(status)

POLICY |    →  POLICY name:
       |        condition
       |        THEN action
       |        PRIORITY: 100
```

**Deliverable:** LSP `textDocument/completion` impl

---

## Low Priority (Advanced Features)

### 11. Refactoring Tools ♻️
**Impact:** Code maintenance
**Effort:** 2 weeks

**Features:**
- Extract policy (from condition)
- Inline constant
- Rename variable/policy (safe)
- Move to module
- Extract module function
- Change signature

**Deliverable:** LSP code actions

---

### 12. Type Checker (Gradual Typing) 🔢
**Impact:** Type safety beyond runtime
**Effort:** 2-3 weeks

**Current:** Dynamic typing with runtime checks
**Proposed:** Optional type annotations

```phronesis
# Type annotations (optional)
CONST my_asn: Integer = 64512

POLICY typed_example:
  (route: Route) => route.origin == my_asn
  THEN ACCEPT("Owned AS")

TYPE Route = {
  prefix: String,
  origin: Integer,
  as_path: List<Integer>
}
```

**Deliverable:** `phronesis typecheck` command

---

### 13. Module Registry / Package Repository 🏛️
**Impact:** Ecosystem growth
**Effort:** 4-6 weeks (infrastructure + UI)

**Features:**
- Web UI (search, browse)
- REST API
- Authentication
- Package versioning
- Download statistics
- Documentation hosting

**Stack:**
- Phoenix web framework
- PostgreSQL database
- S3/Spaces for storage
- CloudFlare CDN

**URL:** `https://policies.phronesis.dev`

**Deliverable:** Full package registry service

---

### 14. WASM Target 🌐
**Impact:** Browser execution
**Effort:** 3-4 weeks

**Goal:** Compile phronesis → WebAssembly

**Use Cases:**
- Policy playground in browser
- Client-side policy evaluation
- Embedded in web apps
- Edge computing (Cloudflare Workers)

**Implementation:**
```bash
phronesis compile --target wasm policy.phr -o policy.wasm
```

**Deliverable:** WASM backend for compiler

---

### 15. Foreign Function Interface (FFI) 🔌
**Impact:** External integration
**Effort:** 2 weeks

**Goal:** Call Erlang/Elixir from policies

```phronesis
# Call Elixir function
EXTERN erlang:crypto.hash(Algorithm, Data) -> Hash

POLICY hash_check:
  erlang:crypto.hash(:sha256, data) == expected_hash
  THEN ACCEPT()
```

**Why Deferred:**
- Security concerns (sandbox isolation)
- Capability enforcement needed
- BEAM integration complex

**Deliverable:** `EXTERN` keyword support

---

## Implementation Priority Matrix

| Tool | Impact | Effort | Priority | When |
|------|--------|--------|----------|------|
| LSP | Very High | High | 1 | Phase 4 |
| Debugger | High | Medium | 2 | Phase 4 |
| Testing Framework | Very High | Low | 3 | Phase 3 |
| Profiler | Medium | Low | 4 | Phase 4 |
| Doc Generator | Medium | Low | 5 | Phase 4 |
| Static Analyzer | Medium | Medium | 6 | Phase 5 |
| Syntax Highlighting | High | Very Low | 7 | Phase 3 |
| Error Reporter | Medium | Low | 8 | Phase 4 |
| Package Manager | High | High | 9 | Phase 5 |
| Code Completion | Medium | Low | 10 | Phase 4 (via LSP) |
| Refactoring | Low | Medium | 11 | Phase 6 |
| Type Checker | Medium | High | 12 | Phase 6 |
| Module Registry | Low | Very High | 13 | Phase 7 |
| WASM Target | Low | High | 14 | Phase 7 |
| FFI | Medium | Medium | 15 | Phase 6 |

---

## Recommended Next Steps

**Phase 3 (Current):** Consensus Integration
- Add Raft library
- Multi-node cluster

**Phase 4 (Next):** Developer Tools
1. **Syntax highlighting** (2-3 days) ← Quick win
2. **Testing framework** (1 week) ← Essential
3. **LSP server** (2-3 weeks) ← Game changer
4. **Debugger** (1-2 weeks)
5. **Profiler** (1 week)
6. **Doc generator** (1 week)

**Phase 5:** Quality & Ecosystem
- Static analyzer
- Package manager
- Error reporter enhancements

**Phase 6:** Advanced Features
- Gradual type checker
- Refactoring tools
- FFI (if needed)

**Phase 7:** Infrastructure
- Module registry (web service)
- WASM target

---

## Estimated Timeline

**Complete Toolchain (Production-Grade):** 12-16 weeks

- Phase 3: Consensus (1 week) ✅ In progress
- Phase 4: Dev Tools (6-8 weeks)
- Phase 5: Quality (3-4 weeks)
- Phase 6: Advanced (2-3 weeks)
- Phase 7: Infrastructure (when needed)

**MVP Toolchain:** 8 weeks (Phases 3-4 only)

---

## Community Contributions Welcome

Lower priority items ideal for contributors:
- Syntax highlighting definitions
- Editor plugins
- Documentation examples
- Policy libraries
- Testing policies

High-skill contributions:
- LSP implementation
- Debugger
- WASM backend
- Type checker

---

**Current Status:** 45% complete
**With full toolchain:** 100% complete (production-ready language)

**Maintainer:** Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
**Date:** 2026-01-30
**License:** MPL-2.0

# Phronesis Wiki

> **Phronesis** - A consensus-gated policy language for network configuration

Welcome to the Phronesis documentation wiki. This comprehensive resource covers everything from getting started to advanced deployment scenarios.

---

## Quick Navigation

### Getting Started
- [Installation](Installation.md) - Install Phronesis on your system
- [Quick Start](Quick-Start.md) - Your first policy in 5 minutes
- [Hello World](Hello-World.md) - Basic examples explained
- [Project Structure](Project-Structure.md) - Organizing policy projects

### Language Guide
- [Language Overview](Language-Overview.md) - Core concepts
- [Syntax Reference](Syntax-Reference.md) - Complete syntax guide
- [Types](Types.md) - Type system documentation
- [Operators](Operators.md) - All operators explained
- [Expressions](Expressions.md) - Expression evaluation
- [Policies](Policies.md) - Policy declarations
- [Actions](Actions.md) - ACCEPT, REJECT, REPORT, EXECUTE
- [Modules](Modules.md) - Module system and imports

### Standard Library
- [Std.RPKI](Stdlib-RPKI.md) - RPKI validation
- [Std.BGP](Stdlib-BGP.md) - BGP operations
- [Std.Consensus](Stdlib-Consensus.md) - Distributed consensus
- [Std.Temporal](Stdlib-Temporal.md) - Temporal constraints
- [Std.IP](Stdlib-IP.md) - IP address utilities
- [Std.ASN](Stdlib-ASN.md) - AS number utilities

### Tooling
- [CLI Reference](CLI-Reference.md) - Command-line interface
- [REPL Guide](REPL-Guide.md) - Interactive mode
- [Formatter](Formatter.md) - Code formatting
- [Linter](Linter.md) - Static analysis
- [Testing](Testing.md) - Test framework
- [Debugging](Debugging.md) - Debug tools

### Architecture
- [System Overview](Architecture-Overview.md) - High-level design
- [Lexer](Architecture-Lexer.md) - Tokenization
- [Parser](Architecture-Parser.md) - Parsing & AST
- [Interpreter](Architecture-Interpreter.md) - Execution model
- [Compiler](Architecture-Compiler.md) - Compilation pipeline
- [Consensus](Architecture-Consensus.md) - Raft implementation
- [State Model](Architecture-State.md) - State management

### Tutorials
- [Tutorial: BGP Security](Tutorial-BGP-Security.md) - Secure BGP policies
- [Tutorial: RPKI Validation](Tutorial-RPKI.md) - ROA validation
- [Tutorial: Consensus Routing](Tutorial-Consensus.md) - Multi-party approval
- [Tutorial: Traffic Engineering](Tutorial-Traffic-Engineering.md) - TE policies
- [Tutorial: Testing Policies](Tutorial-Testing.md) - Test your policies

### Advanced Topics
- [Formal Semantics](Formal-Semantics.md) - Operational semantics
- [Type System](Advanced-Types.md) - Type theory
- [Security Model](Security-Model.md) - Security guarantees
- [Performance Tuning](Performance.md) - Optimization guide
- [Production Deployment](Production.md) - Deployment guide
- [High Availability](High-Availability.md) - HA configuration

### Integration
- [RPKI Validators](Integration-RPKI.md) - Routinator, rpki-client
- [Router Integration](Integration-Routers.md) - Cisco, Juniper, Arista
- [Kubernetes](Integration-Kubernetes.md) - K8s NetworkPolicy
- [Terraform](Integration-Terraform.md) - IaC integration
- [Prometheus](Integration-Prometheus.md) - Metrics & monitoring

### Developer Guide
- [Contributing](Contributing.md) - How to contribute
- [Development Setup](Development-Setup.md) - Dev environment
- [Code Style](Code-Style.md) - Style guidelines
- [Testing Guide](Testing-Guide.md) - Writing tests
- [Release Process](Release-Process.md) - Release workflow
- [RFC Process](RFC-Process.md) - Feature proposals

### Reference
- [Grammar (EBNF)](Reference-Grammar.md) - Formal grammar
- [AST Reference](Reference-AST.md) - AST node types
- [Error Codes](Reference-Errors.md) - Error reference
- [Glossary](Glossary.md) - Terms & definitions
- [FAQ](FAQ.md) - Frequently asked questions
- [Changelog](Changelog.md) - Version history

---

## Feature Status

| Feature | Status | Version |
|---------|--------|---------|
| Core Language | ✅ Stable | 0.1.x |
| Lexer | ✅ Stable | 0.1.x |
| Parser | ✅ Stable | 0.1.x |
| Interpreter | ✅ Stable | 0.1.x |
| CLI | ✅ Stable | 0.1.x |
| REPL | ✅ Stable | 0.1.x |
| Std.RPKI | ✅ Stable | 0.1.x |
| Std.BGP | ✅ Stable | 0.1.x |
| Std.Consensus | ✅ Stable | 0.1.x |
| Std.Temporal | ✅ Stable | 0.1.x |
| Raft Consensus | ✅ Stable | 0.1.x |
| TLA+ Spec | ✅ Complete | 0.1.x |
| Formatter | 🔄 In Progress | 0.2.x |
| LSP Server | 📋 Planned | 0.3.x |
| Bytecode Compiler | 📋 Planned | 0.4.x |

---

## Quick Example

```phronesis
# BGP Security Policy
IMPORT Std.RPKI
IMPORT Std.BGP

CONST bogon_prefixes = ["0.0.0.0/8", "10.0.0.0/8", "127.0.0.0/8"]

POLICY rpki_validation:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI validation failed")
  PRIORITY: 200

POLICY bogon_filter:
  route.prefix IN bogon_prefixes
  THEN REJECT("Bogon prefix not allowed")
  PRIORITY: 190

POLICY default_accept:
  true
  THEN ACCEPT(route)
  PRIORITY: 1
```

---

## Getting Help

- **Documentation**: You're here!
- **GitHub Issues**: [Report bugs](https://github.com/hyperpolymath/phronesis/issues)
- **Discussions**: [Ask questions](https://github.com/hyperpolymath/phronesis/discussions)
- **Discord**: [Community chat](#)

---

## License

Phronesis is licensed under [AGPL-3.0-or-later](../LICENSE).

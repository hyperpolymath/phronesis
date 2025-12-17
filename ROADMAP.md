# Phronesis Roadmap

> A consensus-gated policy language for network configuration

This roadmap outlines the development trajectory for Phronesis across all components: language, tooling, frameworks, libraries, and runtime systems.

---

## Version Overview

| Version | Codename | Focus | Target |
|---------|----------|-------|--------|
| 0.1.x | Foundation | Core language, basic tooling | Q1 2025 |
| 0.2.x | Consensus | Distributed execution, Raft | Q2 2025 |
| 0.3.x | Validation | RPKI integration, type system | Q3 2025 |
| 0.4.x | Tooling | IDE support, debugging | Q4 2025 |
| 0.5.x | Production | Performance, security audit | Q1 2026 |
| 1.0.0 | Genesis | Stable release | Q2 2026 |

---

## Language Evolution

### Phase 1: Core Language (v0.1.x) ✅

- [x] EBNF grammar specification (~40 lines, 15 keywords)
- [x] Formal operational semantics (5 evaluation rules)
- [x] Basic type system (Integer, Float, String, Boolean, IP, DateTime, List, Record)
- [x] Policy declarations with priority ordering
- [x] Constant declarations
- [x] Module imports
- [x] Conditional expressions (IF/THEN/ELSE)
- [x] Logical operators (AND, OR, NOT)
- [x] Comparison operators (==, !=, <, >, <=, >=)
- [x] Arithmetic operators (+, -, *, /, %)
- [x] Actions (ACCEPT, REJECT, REPORT, EXECUTE)

### Phase 2: Enhanced Expressions (v0.2.x)

- [ ] Pattern matching on records
  ```
  POLICY route_match:
    route MATCHES {prefix: p, origin_as: as} WHERE p STARTS_WITH "10."
    THEN REJECT("Private prefix")
    PRIORITY: 100
  ```
- [ ] List comprehensions (bounded)
  ```
  filtered = [x FOR x IN routes WHERE x.prefix_len < 24]
  ```
- [ ] String interpolation
  ```
  REPORT("Rejected route from AS ${route.origin_as}")
  ```
- [ ] Optional chaining for records
  ```
  route.community?.first OR "none"
  ```

### Phase 3: Type System (v0.3.x)

- [ ] Static type inference
- [ ] Type annotations (optional)
  ```
  CONST max_len: Integer = 24
  ```
- [ ] Generic module parameters
- [ ] Union types for validation results
  ```
  type ValidationResult = Valid | Invalid | NotFound
  ```
- [ ] Refinement types for constraints
  ```
  type PrefixLength = Integer WHERE 0 <= _ <= 128
  ```

### Phase 4: Advanced Features (v0.4.x)

- [ ] Temporal operators (ALWAYS, EVENTUALLY, UNTIL)
  ```
  POLICY temporal_constraint:
    EVENTUALLY(route.validated, deadline: "1h")
    THEN ACCEPT(route)
    PRIORITY: 50
  ```
- [ ] Aggregate functions over policy sets
- [ ] Policy composition operators
  ```
  POLICY combined = rpki_check COMPOSE as_path_filter COMPOSE bogon_filter
  ```
- [ ] Scoped policy namespaces

### Phase 5: Stability (v0.5.x - v1.0.0)

- [ ] Language specification freeze
- [ ] Backward compatibility guarantees
- [ ] Deprecation policy
- [ ] Long-term support (LTS) versioning

---

## Lexer Roadmap

### Current State (v0.1.x) ✅

- [x] Hand-written tokenizer
- [x] 15 keyword recognition
- [x] IP address literals (IPv4)
- [x] DateTime literals (ISO 8601)
- [x] String literals with escape sequences
- [x] Integer and float literals
- [x] Single-line comments (#)
- [x] Position tracking (line, column)

### Planned Enhancements

#### v0.2.x: Extended Literals
- [ ] IPv6 address literals
- [ ] CIDR notation validation
- [ ] Hexadecimal integers (0xFF)
- [ ] Binary integers (0b1010)
- [ ] Scientific notation (1.5e10)
- [ ] Multi-line strings (triple quotes)
- [ ] Raw strings (r"no\escapes")

#### v0.3.x: Advanced Features
- [ ] Unicode identifier support
- [ ] Multi-line comments (/* */)
- [ ] Doc comments (## or ///)
- [ ] String interpolation tokens
- [ ] Heredoc syntax for policies

#### v0.4.x: Error Recovery
- [ ] Lexer error recovery
- [ ] Fuzzy token matching for suggestions
- [ ] Incremental lexing for IDE support
- [ ] Token streaming API

#### v0.5.x: Performance
- [ ] Zero-copy tokenization
- [ ] SIMD-accelerated scanning
- [ ] Memory-mapped file support
- [ ] Parallel lexing for large files

---

## Parser Roadmap

### Current State (v0.1.x) ✅

- [x] LL(1) recursive descent parser
- [x] Full grammar coverage
- [x] AST generation
- [x] Basic error messages
- [x] Position tracking in AST nodes

### Planned Enhancements

#### v0.2.x: Error Handling
- [ ] Error recovery (panic mode)
- [ ] Multiple error reporting
- [ ] Contextual error messages
  ```
  Error at line 5, column 12:
    POLICY test: x = 5
                   ^
  Expected 'THEN' after condition, found '='
  Did you mean to use '==' for comparison?
  ```
- [ ] Syntax suggestions

#### v0.3.x: Advanced Parsing
- [ ] Incremental parsing for IDE
- [ ] Concrete Syntax Tree (CST) preservation
- [ ] Comment attachment to AST
- [ ] Source map generation
- [ ] Macro expansion hooks

#### v0.4.x: Parser Combinators
- [ ] Alternative parser implementation using combinators
- [ ] Grammar extension points
- [ ] Custom operator precedence
- [ ] Plugin system for syntax extensions

#### v0.5.x: Verification
- [ ] Grammar ambiguity detection
- [ ] LL(1) property verification
- [ ] Parser generator from EBNF
- [ ] Fuzz testing infrastructure

---

## Interpreter Roadmap

### Current State (v0.1.x) ✅

- [x] Tree-walking interpreter
- [x] Operational semantics implementation
- [x] State management (PolicyTable, ConsensusLog, Environment, PendingActions)
- [x] Module system with capability checking
- [x] Basic standard library (RPKI, BGP, Consensus, Temporal)

### Planned Enhancements

#### v0.2.x: Runtime Features
- [ ] Tail call optimization
- [ ] Lazy evaluation for large lists
- [ ] Memoization of pure functions
- [ ] Garbage collection tuning
- [ ] Resource limits (memory, CPU)

#### v0.3.x: Debugging Support
- [ ] Step-through execution
- [ ] Breakpoint support
- [ ] Variable inspection
- [ ] Call stack visualization
- [ ] Execution tracing

#### v0.4.x: Performance
- [ ] Bytecode compilation
- [ ] JIT compilation (via BEAM)
- [ ] Hot code reloading
- [ ] Profiling hooks
- [ ] Memory profiling

#### v0.5.x: Production
- [ ] Sandboxed execution environments
- [ ] Resource quotas
- [ ] Execution timeouts
- [ ] Audit logging
- [ ] Metrics export (Prometheus)

---

## Compiler Roadmap

### Phase 1: Analysis Pipeline (v0.2.x)

- [ ] Semantic analysis
  - [ ] Scope resolution
  - [ ] Type checking
  - [ ] Constant folding
  - [ ] Dead code detection
- [ ] Intermediate representation (IR)
- [ ] Control flow graph generation
- [ ] Data flow analysis

### Phase 2: Optimization (v0.3.x)

- [ ] Constant propagation
- [ ] Common subexpression elimination
- [ ] Policy merging optimization
- [ ] Predicate simplification
- [ ] Unreachable policy detection

### Phase 3: Code Generation (v0.4.x)

- [ ] BEAM bytecode generation
- [ ] Native code via Rustler NIFs
- [ ] WebAssembly target
- [ ] eBPF target for XDP integration

### Phase 4: Verification (v0.5.x)

- [ ] SMT solver integration (Z3)
- [ ] Policy conflict detection
- [ ] Termination verification
- [ ] Coverage analysis
- [ ] Symbolic execution

---

## REPL Roadmap

### Current State (v0.1.x) ✅

- [x] Basic read-eval-print loop
- [x] Policy parsing and execution
- [x] State inspection
- [x] Multi-line input

### Planned Enhancements

#### v0.2.x: Usability
- [ ] Syntax highlighting
- [ ] Tab completion
  - [ ] Keywords
  - [ ] Module names
  - [ ] Function names
  - [ ] Variable names
- [ ] History persistence
- [ ] History search (Ctrl+R)
- [ ] Multi-line editing

#### v0.3.x: Features
- [ ] REPL commands
  ```
  :help          - Show help
  :load FILE     - Load policy file
  :reload        - Reload current file
  :type EXPR     - Show expression type
  :state         - Show current state
  :policies      - List loaded policies
  :clear         - Clear state
  :quit          - Exit REPL
  ```
- [ ] Pretty printing
- [ ] Output formatting options (JSON, table)
- [ ] Timing information

#### v0.4.x: Advanced
- [ ] Debugger integration
- [ ] Breakpoint commands
- [ ] Step execution
- [ ] Watch expressions
- [ ] Remote REPL (network)
- [ ] Jupyter kernel

#### v0.5.x: Integration
- [ ] Web-based REPL
- [ ] Notebook interface
- [ ] Collaboration features
- [ ] Session recording/playback

---

## CLI Tooling Roadmap

### Current State (v0.1.x) ✅

- [x] `phronesis run` - Execute policy files
- [x] `phronesis parse` - Parse and show AST
- [x] `phronesis check` - Syntax validation
- [x] `phronesis repl` - Interactive mode

### Planned Commands

#### v0.2.x: Development Tools
```bash
phronesis fmt           # Format policy files
phronesis lint          # Static analysis
phronesis test          # Run policy tests
phronesis doc           # Generate documentation
phronesis new           # Create new project
```

#### v0.3.x: Analysis Tools
```bash
phronesis analyze       # Deep policy analysis
phronesis conflicts     # Detect policy conflicts
phronesis coverage      # Policy coverage report
phronesis deps          # Dependency graph
phronesis graph         # Visualize policy flow
```

#### v0.4.x: Operations Tools
```bash
phronesis deploy        # Deploy to network
phronesis validate      # Validate against live network
phronesis diff          # Compare policy versions
phronesis rollback      # Rollback deployment
phronesis audit         # Audit trail
```

#### v0.5.x: Integration Tools
```bash
phronesis serve         # Language server
phronesis export        # Export to other formats
phronesis import        # Import from other systems
phronesis migrate       # Migration assistant
```

---

## IDE & Editor Support Roadmap

### Phase 1: Basic Support (v0.2.x)

- [ ] VS Code Extension
  - [ ] Syntax highlighting
  - [ ] Bracket matching
  - [ ] Code folding
  - [ ] Snippets
- [ ] Vim/Neovim plugin
- [ ] Emacs mode
- [ ] Sublime Text package

### Phase 2: Language Server (v0.3.x)

- [ ] LSP implementation
  - [ ] Go to definition
  - [ ] Find references
  - [ ] Hover information
  - [ ] Signature help
  - [ ] Document symbols
  - [ ] Workspace symbols
- [ ] Diagnostics (errors, warnings)
- [ ] Quick fixes

### Phase 3: Advanced Features (v0.4.x)

- [ ] Code completion
  - [ ] Context-aware suggestions
  - [ ] Import suggestions
  - [ ] Snippet completion
- [ ] Refactoring
  - [ ] Rename symbol
  - [ ] Extract policy
  - [ ] Inline constant
- [ ] Code actions
- [ ] Formatting provider

### Phase 4: Rich Features (v0.5.x)

- [ ] Semantic highlighting
- [ ] Inlay hints (types, parameters)
- [ ] Call hierarchy
- [ ] Type hierarchy
- [ ] Code lens (run policy, test count)
- [ ] Debugging support (DAP)
- [ ] Notebook support

---

## Framework Roadmap

### Phronesis Core Framework

#### v0.2.x: Testing Framework
```elixir
defmodule MyPolicyTest do
  use Phronesis.Test

  describe "RPKI validation" do
    setup do
      %{route: %{prefix: "1.1.1.0/24", origin_as: 13335}}
    end

    test "accepts valid RPKI route", %{route: route} do
      assert_accept "rpki_policy", route
    end

    test "rejects invalid origin", %{route: route} do
      route = %{route | origin_as: 99999}
      assert_reject "rpki_policy", route
    end
  end
end
```

#### v0.3.x: Simulation Framework
```elixir
defmodule NetworkSimulation do
  use Phronesis.Simulation

  network do
    router :r1, as: 65001, location: "us-east"
    router :r2, as: 65002, location: "us-west"
    router :r3, as: 65003, location: "eu-west"

    link :r1, :r2, latency: "20ms"
    link :r2, :r3, latency: "80ms"
  end

  scenario "route propagation" do
    announce :r1, prefix: "10.0.0.0/24"
    wait_for_convergence()
    assert_route :r3, prefix: "10.0.0.0/24", via: :r2
  end
end
```

#### v0.4.x: Deployment Framework
```elixir
defmodule ProductionDeployment do
  use Phronesis.Deploy

  config :canary,
    percentage: 10,
    duration: "1h",
    rollback_on: [:error_rate, :latency]

  stage :validate do
    check_syntax()
    check_conflicts()
    check_coverage(min: 80)
  end

  stage :canary do
    deploy_to(nodes: canary_nodes())
    monitor(duration: "1h")
    verify_metrics()
  end

  stage :production do
    deploy_to(nodes: all_nodes())
    verify_convergence()
  end
end
```

### Integration Frameworks

#### v0.3.x: Router Integration
- [ ] Cisco IOS-XR integration
- [ ] Juniper Junos integration
- [ ] Arista EOS integration
- [ ] Nokia SR OS integration
- [ ] OpenConfig/gNMI support
- [ ] NETCONF/YANG support

#### v0.4.x: Orchestration Integration
- [ ] Kubernetes NetworkPolicy generation
- [ ] Terraform provider
- [ ] Ansible modules
- [ ] Puppet types
- [ ] Chef resources

#### v0.5.x: Observability Integration
- [ ] Prometheus metrics exporter
- [ ] Grafana dashboards
- [ ] OpenTelemetry tracing
- [ ] Jaeger integration
- [ ] ELK stack integration

---

## Library Roadmap

### Standard Library (Std.*)

#### Current (v0.1.x) ✅
- [x] Std.RPKI - RPKI validation
- [x] Std.BGP - BGP operations
- [x] Std.Consensus - Distributed consensus
- [x] Std.Temporal - Time-based constraints

#### v0.2.x: Network Libraries
- [ ] Std.IP - IP address manipulation
  ```
  Std.IP.in_subnet("10.0.0.1", "10.0.0.0/24")  # true
  Std.IP.is_private("192.168.1.1")              # true
  Std.IP.to_integer("10.0.0.1")                 # 167772161
  ```
- [ ] Std.ASN - AS number utilities
  ```
  Std.ASN.is_private(65000)                     # true
  Std.ASN.is_documentation(64496)               # true
  ```
- [ ] Std.DNS - DNS lookups (async)
- [ ] Std.GeoIP - Geographic lookups

#### v0.3.x: Security Libraries
- [ ] Std.Crypto - Cryptographic operations
- [ ] Std.Auth - Authentication helpers
- [ ] Std.Audit - Audit logging
- [ ] Std.Rate - Rate limiting

#### v0.4.x: Data Libraries
- [ ] Std.JSON - JSON parsing/generation
- [ ] Std.YAML - YAML support
- [ ] Std.CSV - CSV handling
- [ ] Std.HTTP - HTTP client (async)

#### v0.5.x: Advanced Libraries
- [ ] Std.ML - Machine learning integration
- [ ] Std.Stats - Statistical functions
- [ ] Std.Graph - Graph algorithms
- [ ] Std.Cache - Caching utilities

### Third-Party Library Ecosystem

#### Package Manager (v0.3.x)
```bash
# Initialize project
phronesis init my_policies

# Add dependencies
phronesis add phronesis-community/bgp-filters
phronesis add phronesis-community/rpki-strict

# Install dependencies
phronesis deps.get

# Publish package
phronesis publish
```

#### Package Registry
- [ ] Central package registry (phr.pm)
- [ ] Private registry support
- [ ] Package signing
- [ ] Vulnerability scanning
- [ ] License compliance checking

---

## Consensus & Distributed Systems Roadmap

### Current State (v0.1.x) ✅
- [x] Raft consensus implementation
- [x] Leader election
- [x] Log replication
- [x] Local and distributed RPC

### v0.2.x: Raft Enhancements
- [ ] Log compaction (snapshotting)
- [ ] Membership changes
- [ ] Pre-vote protocol
- [ ] Witness replicas
- [ ] Learner nodes

### v0.3.x: Alternative Protocols
- [ ] PBFT implementation
- [ ] Tendermint BFT
- [ ] HotStuff
- [ ] Protocol selection at runtime

### v0.4.x: Production Features
- [ ] Automatic failover
- [ ] Split-brain detection
- [ ] Network partition handling
- [ ] Cross-datacenter replication
- [ ] Conflict resolution strategies

### v0.5.x: Advanced
- [ ] Multi-Raft (sharding)
- [ ] Hierarchical consensus
- [ ] Hybrid consensus modes
- [ ] Formal verification (TLA+ model checking)

---

## Security Roadmap

### v0.2.x: Basic Security
- [ ] Input validation hardening
- [ ] Resource exhaustion protection
- [ ] Capability audit logging
- [ ] Security event monitoring

### v0.3.x: Authentication
- [ ] mTLS for node communication
- [ ] Certificate management
- [ ] Key rotation
- [ ] HSM support

### v0.4.x: Authorization
- [ ] Fine-grained RBAC
- [ ] Policy-based access control
- [ ] Multi-tenancy support
- [ ] Audit compliance (SOC2, etc.)

### v0.5.x: Hardening
- [ ] Security audit (external)
- [ ] Penetration testing
- [ ] CVE monitoring
- [ ] Bug bounty program
- [ ] FIPS 140-2 compliance (optional)

---

## Performance Roadmap

### Benchmarks & Targets

| Metric | v0.1 | v0.5 | v1.0 |
|--------|------|------|------|
| Parse (policies/sec) | 1K | 100K | 1M |
| Execute (decisions/sec) | 10K | 500K | 2M |
| Consensus (commits/sec) | 100 | 10K | 100K |
| Memory (per policy) | 10KB | 1KB | 100B |
| Startup time | 500ms | 50ms | 10ms |

### Optimization Phases

#### v0.3.x: Algorithmic
- [ ] Parser optimization
- [ ] AST memory layout
- [ ] Evaluation caching
- [ ] Policy indexing

#### v0.4.x: System
- [ ] BEAM tuning
- [ ] NIF acceleration (Rust)
- [ ] Memory pooling
- [ ] I/O optimization

#### v0.5.x: Advanced
- [ ] Bytecode interpreter
- [ ] JIT compilation
- [ ] SIMD operations
- [ ] GPU acceleration (experimental)

---

## Documentation Roadmap

### v0.2.x: Core Documentation
- [ ] Complete language reference
- [ ] Standard library reference
- [ ] API documentation
- [ ] Architecture guide

### v0.3.x: Learning Resources
- [ ] Tutorial series
- [ ] Video tutorials
- [ ] Interactive playground
- [ ] Example repository

### v0.4.x: Advanced Topics
- [ ] Performance tuning guide
- [ ] Security hardening guide
- [ ] Deployment guides
- [ ] Migration guides

### v0.5.x: Community
- [ ] Community wiki
- [ ] Best practices
- [ ] Design patterns
- [ ] Case studies

---

## Community & Ecosystem Roadmap

### v0.2.x: Foundation
- [ ] Code of conduct
- [ ] Contributing guidelines
- [ ] Issue templates
- [ ] PR templates
- [ ] Discussion forums

### v0.3.x: Governance
- [ ] Technical steering committee
- [ ] RFC process
- [ ] Release process
- [ ] Security policy

### v0.4.x: Growth
- [ ] Conference talks
- [ ] Blog posts
- [ ] Newsletters
- [ ] User groups

### v0.5.x: Sustainability
- [ ] Foundation/sponsorship
- [ ] Certification program
- [ ] Partner ecosystem
- [ ] Enterprise support

---

## Release Schedule

### 2025
- **Q1**: v0.1.0 (Foundation) ✅
- **Q2**: v0.2.0 (Consensus)
- **Q3**: v0.3.0 (Validation)
- **Q4**: v0.4.0 (Tooling)

### 2026
- **Q1**: v0.5.0 (Production)
- **Q2**: v1.0.0 (Genesis) - Stable Release
- **Q3**: v1.1.0 (First feature release)
- **Q4**: v1.2.0 (LTS candidate)

---

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to get involved.

### Priority Areas
1. **Testing**: More test coverage, edge cases
2. **Documentation**: Tutorials, examples, guides
3. **Tooling**: Editor support, CLI improvements
4. **Libraries**: Standard library extensions
5. **Integration**: Router vendor support

### How to Propose Features
1. Check existing issues and roadmap
2. Open a discussion for feedback
3. Submit RFC for significant changes
4. Implement with tests and documentation

---

## License

Phronesis is licensed under AGPL-3.0-or-later. See [LICENSE](LICENSE) for details.

# Phronesis Implementation Roadmap
## From 25% Specification to Working Compiler

**Current State:** 25% complete (specification phase)
**Goal:** Working BEAM bytecode compiler with standard library
**Strategy:** Shortest path to functional compiler

---

## ✅ Theoretical Foundation (COMPLETE)

### Formal Semantics
- [x] `SPEC.core.scm` - Operational semantics in Guile Scheme
- [x] `docs/draft-phronesis-policy-language.txt` - IETF RFC draft
- [x] `docs/safety_proofs.md` - Safety guarantees (isolation, capabilities, BFT)
- [x] Grammar definition
- [x] Type system specification
- [x] Termination proof (by structural induction)
- [x] Consensus model (Raft-based)

### What This Gives Us
- **Decidability:** All programs terminate (no loops, no recursion)
- **Type Safety:** Static type checking prevents runtime errors
- **Consensus Safety:** No action executes without distributed agreement
- **Audit Trail:** Complete decision trace for every execution

---

## 🔧 Implementation Components (Current Status)

### ✅ Complete
- [x] Lexer (`lib/phronesis/lexer.ex`) - 27KB, tokenizes source
- [x] Parser (`lib/phronesis/parser.ex`) - 19KB, builds AST
- [x] AST (`lib/phronesis/ast.ex`) - 6KB, node definitions
- [x] Token (`lib/phronesis/token.ex`) - 4KB, token types
- [x] Demo (`lib/phronesis/demo.ex`) - 9KB, working scenarios
- [x] Formatter (`lib/phronesis/formatter.ex`) - 11KB, code formatting
- [x] Linter (`lib/phronesis/linter.ex`) - 12KB, policy validation

### ⚠️ Partially Complete
- [~] Compiler (`lib/phronesis/compiler.ex`) - 22KB, **needs BEAM codegen**
- [~] Interpreter (`lib/phronesis/interpreter.ex`) - 12KB, **needs stdlib integration**
- [~] TracingInterpreter (`lib/phronesis/tracing_interpreter.ex`) - 15KB, **needs consensus**
- [~] State (`lib/phronesis/state.ex`) - 6KB, **needs persistence**

### ❌ Missing
- [ ] Standard Library (Std.RPKI, Std.BGP, Std.Consensus, Std.Temporal)
- [ ] Consensus Protocol (Raft integration)
- [ ] BEAM Bytecode Generator
- [ ] Module System
- [ ] Runtime (standalone executable)
- [ ] Test Suite (beyond conformance tests)

---

## 🎯 Shortest Path to Working Compiler

### Phase 1: Core Compiler (Week 1)
**Goal:** Generate executable BEAM bytecode from Phronesis AST

**Tasks:**
1. **BEAM Codegen Module** (`lib/phronesis/codegen.ex`)
   - [ ] Convert AST nodes to BEAM instructions
   - [ ] Variable binding/environment setup
   - [ ] Expression evaluation
   - [ ] Action execution
   - [ ] Module calls

2. **Compilation Pipeline**
   - [ ] Source → Tokens (lexer) ✅
   - [ ] Tokens → AST (parser) ✅
   - [ ] AST → BEAM bytecode (NEW)
   - [ ] Write `.beam` files

3. **Runtime Loader**
   - [ ] Load compiled `.beam` modules
   - [ ] Execute policies with initial state
   - [ ] Return decision + trace

**Deliverable:** `phronesis compile input.phr -o output.beam`

---

### Phase 2: Standard Library (Week 2)
**Goal:** Implement minimal stdlib for network policy use cases

**Priority Modules:**

1. **Std.Consensus** (CRITICAL)
   ```elixir
   defmodule Phronesis.Stdlib.Consensus do
     def vote(action, agents, threshold)
     def log_action(action, votes, result)
     def get_consensus_log(state)
   end
   ```

2. **Std.BGP** (Network policies)
   ```elixir
   defmodule Phronesis.Stdlib.BGP do
     def extract_as_path(route)
     def get_origin(route)
     def path_length(route)
     def validate_route(route)
   end
   ```

3. **Std.RPKI** (Security policies)
   ```elixir
   defmodule Phronesis.Stdlib.RPKI do
     def validate(route)
     def check_origin(asn, prefix)
   end
   ```

4. **Std.Temporal** (Time-based policies)
   ```elixir
   defmodule Phronesis.Stdlib.Temporal do
     def now()
     def is_expired(timestamp, duration)
     def within_window(start_time, end_time)
   end
   ```

**Deliverable:** Example policies from `priv/examples/` work end-to-end

---

### Phase 3: Consensus Integration (Week 3)
**Goal:** Distributed execution with Raft consensus

**Tasks:**
1. **Raft Library Integration**
   - [ ] Add `ra` (Erlang Raft) or `partisan` to deps
   - [ ] Configure cluster nodes
   - [ ] Replicated state machine

2. **Consensus Execution**
   - [ ] Submit policy execution to Raft cluster
   - [ ] Collect votes from replicas
   - [ ] Commit decision to consensus log
   - [ ] Broadcast result

3. **Multi-Node Demo**
   - [ ] Launch 3-node cluster
   - [ ] Submit policy requiring 2/3 consensus
   - [ ] Show decision propagation

**Deliverable:** Multi-node consensus demo with decision trace

---

### Phase 4: Runtime & CLI (Week 4)
**Goal:** Standalone executable for production use

**Tasks:**
1. **Escript Build**
   - [x] `mix.exs` escript config already exists
   - [ ] Test: `mix escript.build`
   - [ ] Verify: `./phronesis --version`

2. **CLI Commands**
   ```bash
   phronesis compile input.phr -o output.beam
   phronesis run policy.beam --state state.json
   phronesis repl  # Interactive REPL
   phronesis check policy.phr  # Lint + validate
   phronesis trace policy.beam  # Show decision trace
   ```

3. **REPL Integration**
   - [ ] Interactive policy evaluation
   - [ ] Live state inspection
   - [ ] Trace visualization

**Deliverable:** Production-ready `phronesis` binary

---

## 📋 Technical Decisions

### Why BEAM Bytecode?
- **Fault tolerance:** BEAM VM has 99.9999999% uptime guarantees
- **Distribution:** Built-in multi-node communication
- **Concurrency:** Lightweight processes (needed for consensus)
- **Hot code loading:** Update policies without downtime

### Why Raft Consensus?
- **Proven:** Used in etcd, Consul, CockroachDB
- **Simple:** Leader election + log replication
- **Available on BEAM:** `ra` library by RabbitMQ team
- **Matches spec:** SPEC.core.scm assumes consensus voting

### Deferred (Not on Shortest Path)
- ❌ Haskell interpreter (prototyping tool, not production)
- ❌ Rust compiler (faster but longer dev time)
- ❌ TLA+ formal verification (already have Scheme spec)
- ❌ Coq proofs (already have termination proof)
- ❌ WASM-on-BEAM (optimization, not core)

---

## 🧪 Testing Strategy

### Conformance Tests (Already Exist)
- `priv/conformance/valid/*.phr` - Must parse successfully
- `priv/conformance/invalid/*.phr` - Must fail deterministically
- Run with: `Phronesis.Demo.run_conformance()`

### Integration Tests (Need to Create)
1. **End-to-End Policy Execution**
   - Parse → Compile → Execute → Trace
   - Verify decision matches expected outcome

2. **Standard Library Tests**
   - BGP route validation
   - RPKI validation
   - Consensus voting
   - Temporal expiration

3. **Consensus Tests**
   - 3-node cluster
   - Byzantine fault injection
   - Network partition recovery

### Property-Based Tests (Future)
- QuickCheck/PropEr for fuzzing
- Invariant checking (trace completeness, consensus safety)

---

## 📊 Success Criteria

### Minimum Viable Compiler (MVC)
- [ ] Compiles all example policies without errors
- [ ] Executes `bgp_security.phr` with correct decision
- [ ] Produces complete decision trace
- [ ] Standard library functions work
- [ ] Consensus achieves 2/3 threshold

### Production Ready (v1.0)
- [ ] Multi-node consensus cluster works
- [ ] Hot code reloading tested
- [ ] All conformance tests pass
- [ ] CLI supports compile/run/repl/check/trace
- [ ] Documentation complete (tutorial, reference, examples)
- [ ] Performance: 10k policies/sec on single node

---

## 🔬 Formal Verification Integration (Optional)

### TLA+ Specification
- Model consensus protocol in TLA+
- Use TLC model checker to verify liveness/safety
- Prove: "No decision without consensus"

### Isabelle/HOL Proofs
- Formalize operational semantics
- Prove type safety theorem
- Prove termination theorem

### Position
These are **validation** tools, not **implementation** dependencies.
Focus on working compiler first, formal proofs later.

---

## 🚀 Getting Started (Next Steps)

### Immediate Actions (Today)
1. Create `lib/phronesis/codegen.ex` - BEAM bytecode generator skeleton
2. Implement AST → BEAM instruction mapping for literals/variables
3. Test: compile simple policy `CONST x = 42` to BEAM
4. Verify: load .beam file and read constant

### This Week
1. Complete BEAM codegen for all AST nodes
2. Implement Std.Consensus module (voting, logging)
3. End-to-end test: `bgp_security.phr` → `.beam` → decision

### Next Week
1. Implement Std.BGP, Std.RPKI, Std.Temporal
2. Integrate Raft consensus library
3. Multi-node consensus demo

---

## 📚 References

- **SPEC.core.scm** - Formal semantics (ground truth)
- **draft-phronesis-policy-language.txt** - Language specification
- **priv/examples/** - Example policies (test cases)
- **lib/phronesis/demo.ex** - Working interpreter (reference implementation)

---

## 🎓 Learning Resources

### BEAM Bytecode
- Erlang/OTP Design Principles: https://erlang.org/doc/design_principles
- BEAM Book (Hakansson): https://blog.stenmans.org/theBeamBook/
- `beam_disasm` module for reverse engineering

### Raft Consensus
- Raft paper: https://raft.github.io/raft.pdf
- `ra` library: https://github.com/rabbitmq/ra
- Visualization: https://raft.github.io/

### Phronesis Philosophy
- README.adoc - High-level vision
- META.scm - Architectural decisions
- ECOSYSTEM.scm - Related projects

---

**Status:** Ready to begin Phase 1 (Core Compiler)
**Updated:** 2026-01-30
**Maintainer:** Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

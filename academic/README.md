# Phronesis Academic Documentation

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This directory contains comprehensive academic documentation for Phronesis, including formal proofs, white papers, and mechanized verification. The documentation is designed to withstand rigorous academic scrutiny across multiple fields of mathematics and computer science.

---

## Overview

Phronesis is a formally verified consensus-gated policy language for network configuration. This documentation provides rigorous mathematical foundations suitable for academic peer review, covering 20+ areas of mathematics and computer science.

---

## Directory Structure

```
academic/
├── papers/
│   └── phronesis-white-paper.md              # Main academic paper
│
├── proofs/
│   ├── type-theory/
│   │   └── type-theory-proofs.md             # Type safety (progress + preservation)
│   │
│   ├── category-theory/
│   │   └── category-theory-foundations.md    # Categorical semantics, functors, monads
│   │
│   ├── lattice-theory/
│   │   └── type-lattice-proofs.md            # Type lattice structure, meets/joins
│   │
│   ├── proof-theory/
│   │   └── curry-howard-correspondence.md    # Curry-Howard, proof normalization
│   │
│   ├── model-theory/
│   │   ├── model-theory-specification.md     # First-order semantics
│   │   └── denotational-semantics.md         # Denotational semantics, adequacy
│   │
│   ├── domain-theory/
│   │   └── domain-theory-foundations.md      # CPOs, Scott topology, fixed points
│   │
│   ├── axiomatic-semantics/
│   │   └── hoare-logic.md                    # Hoare logic, WP/SP calculus
│   │
│   ├── operational-semantics/
│   │   └── complete-operational-semantics.md # All 45+ evaluation rules
│   │
│   ├── algebraic-semantics/
│   │   └── algebraic-semantics.md            # Initial algebras, F-algebras
│   │
│   ├── automata-theory/
│   │   └── automata-theory-proofs.md         # Lexer DFA, parser PDA, LL(1)
│   │
│   ├── complexity-theory/
│   │   └── computational-complexity-analysis.md  # Time/space bounds, P membership
│   │
│   ├── game-theory/
│   │   └── consensus-game-theory.md          # Nash equilibrium, mechanism design
│   │
│   ├── graph-theory/
│   │   └── bgp-graph-theory.md               # AS graphs, valley-free routing
│   │
│   ├── temporal-logic/
│   │   └── temporal-logic-specifications.md  # LTL, CTL, TLA+
│   │
│   ├── concurrency-theory/
│   │   └── process-algebra.md                # CSP, CCS, π-calculus, session types
│   │
│   ├── information-theory/
│   │   └── information-flow-analysis.md      # Noninterference, security types
│   │
│   ├── cryptography/
│   │   └── cryptographic-proofs.md           # Signatures, BFT, UC framework
│   │
│   ├── abstract-interpretation/
│   │   └── abstract-interpretation-framework.md  # Galois connections, widening
│   │
│   ├── separation-logic/
│   │   └── separation-logic.md               # Capability reasoning, frame rule
│   │
│   ├── order-theory/
│   │   └── order-theory-foundations.md       # Well-foundedness, WQOs, lattices
│   │
│   ├── number-theory/
│   │   └── number-theory-foundations.md      # IP arithmetic, modular crypto
│   │
│   ├── probabilistic-analysis/
│   │   └── probabilistic-analysis.md         # Voting probability, tail bounds
│   │
│   ├── protocol-verification/
│   │   └── dolev-yao-model.md                # Symbolic security, ProVerif
│   │
│   ├── set-theory/
│   │   └── set-theoretic-foundations.md      # ZFC, cardinals, ordinals
│   │
│   └── real-analysis/
│       └── ieee754-analysis.md               # Floating-point, error bounds
│
├── formal-verification/
│   ├── coq/
│   │   └── Phronesis.v                       # Coq formalization (complete proofs)
│   │
│   ├── lean4/
│   │   └── Phronesis.lean                    # Lean 4 formalization
│   │
│   └── agda/
│       └── Phronesis.agda                    # Agda intrinsic typing
│
├── notation-guide.md                         # Unified notation reference
├── theorem-index.md                          # Cross-referenced theorem index
└── TODO.md                                   # Remaining work items
```

---

## Complete Theorem Coverage

### Foundations (120+ Theorems)

| Area | Key Theorems | Document |
|------|--------------|----------|
| **Type Theory** | Progress, Preservation, Strong Normalization | type-theory-proofs.md |
| **Category Theory** | Functor Laws, Monad Laws, CCC Structure | category-theory-foundations.md |
| **Domain Theory** | CPO Completeness, Scott Continuity, Fixed Points | domain-theory-foundations.md |
| **Order Theory** | Well-Foundedness, WQO Closure, Lattice Properties | order-theory-foundations.md |
| **Set Theory** | ZFC Axioms, Cardinality, Transfinite Induction | set-theoretic-foundations.md |

### Semantics

| Area | Key Theorems | Document |
|------|--------------|----------|
| **Operational** | Determinism, Totality, 45+ Rules | complete-operational-semantics.md |
| **Denotational** | Compositionality, Adequacy, Full Abstraction | denotational-semantics.md |
| **Axiomatic** | Soundness, Completeness, WP Characterization | hoare-logic.md |
| **Algebraic** | Initial Algebra, Catamorphism, Hylomorphism | algebraic-semantics.md |

### Security

| Area | Key Theorems | Document |
|------|--------------|----------|
| **Information Flow** | Noninterference, TINI, Declassification | information-flow-analysis.md |
| **Cryptography** | EUF-CMA, BFT Safety, UC Security | cryptographic-proofs.md |
| **Protocol** | Authentication, Agreement, Replay Prevention | dolev-yao-model.md |
| **Separation Logic** | Frame Rule, Capability Isolation | separation-logic.md |

### Consensus

| Area | Key Theorems | Document |
|------|--------------|----------|
| **Game Theory** | Nash Equilibrium, Incentive Compatibility | consensus-game-theory.md |
| **Temporal Logic** | Safety, Liveness, Fairness | temporal-logic-specifications.md |
| **Concurrency** | Deadlock Freedom, Bisimulation | process-algebra.md |
| **Probability** | Vote Distribution, Tail Bounds | probabilistic-analysis.md |

### Language Theory

| Area | Key Theorems | Document |
|------|--------------|----------|
| **Automata** | DFA Recognition, LL(1) Parsing | automata-theory-proofs.md |
| **Complexity** | O(n) Parsing, P Membership | computational-complexity-analysis.md |
| **Graph Theory** | Valley-Free Routing, Cycle Detection | bgp-graph-theory.md |

---

## Formal Verification Status

| Property | Coq | Lean 4 | Agda | TLA+ | ProVerif |
|----------|-----|--------|------|------|----------|
| Type Safety | ✓ | ✓ | ✓ | - | - |
| Preservation | ✓ | ✓ | ✓ | - | - |
| Determinism | ✓ | ✓ | ✓ | - | - |
| Termination | ✓ | ✓ | ✓ | - | - |
| Subtyping | ✓ | ✓ | - | - | - |
| Consensus Safety | - | - | - | ✓ | - |
| Liveness | - | - | - | ✓ | - |
| Authentication | - | - | - | - | ✓ |
| Noninterference | - | - | - | - | - |

**Legend:**
- ✓ = Fully mechanized and verified
- `-` = Not applicable or symbolic proof only

---

## Quick Start

### View Documentation
All proofs are in Markdown format for easy reading:
```bash
# Main paper
less academic/papers/phronesis-white-paper.md

# Type safety proofs
less academic/proofs/type-theory/type-theory-proofs.md

# Theorem index
less academic/theorem-index.md
```

### Verify Coq Proofs
```bash
opam install coq coq-mathcomp
coqc academic/formal-verification/coq/Phronesis.v
```

### Check TLA+ Specification
```bash
tlc formal/PhronesisConsensus.tla
```

---

## Navigation Aids

- **notation-guide.md**: Comprehensive notation reference across all documents
- **theorem-index.md**: Cross-referenced index of 120+ theorems with dependencies

---

## Citation

```bibtex
@techreport{phronesis2025,
  title={Phronesis: A Formally Verified Consensus-Gated Policy Language},
  author={Phronesis Development Team},
  year={2025},
  institution={Open Source},
  note={Available at https://github.com/hyperpolymath/phronesis}
}
```

---

## Contributing

Academic contributions are welcome. Please:

1. Follow notation conventions in `notation-guide.md`
2. Include complete proofs with all steps justified
3. Add theorem to `theorem-index.md` with dependencies
4. Provide mechanized proofs where possible
5. Reference existing work appropriately

---

## License

All academic documentation is dual-licensed under Apache-2.0 and MIT.
See SPDX headers in individual files.

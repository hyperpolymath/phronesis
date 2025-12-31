# Phronesis Academic Documentation

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This directory contains comprehensive academic documentation for Phronesis, including formal proofs, white papers, and mechanized verification.

---

## Overview

Phronesis is a formally verified consensus-gated policy language for network configuration. This documentation provides rigorous mathematical foundations suitable for academic peer review.

---

## Directory Structure

```
academic/
├── papers/
│   └── phronesis-white-paper.md        # Main academic paper
│
├── proofs/
│   ├── type-theory/
│   │   └── type-theory-proofs.md       # Type safety (progress + preservation)
│   │
│   ├── category-theory/
│   │   └── category-theory-foundations.md  # Categorical semantics
│   │
│   ├── lattice-theory/
│   │   └── type-lattice-proofs.md      # Type lattice structure
│   │
│   ├── proof-theory/
│   │   └── curry-howard-correspondence.md  # Curry-Howard, proof normalization
│   │
│   ├── model-theory/
│   │   ├── model-theory-specification.md   # First-order semantics
│   │   └── denotational-semantics.md       # Denotational semantics
│   │
│   ├── automata-theory/
│   │   └── automata-theory-proofs.md   # Lexer/parser automata
│   │
│   ├── complexity-theory/
│   │   └── computational-complexity-analysis.md  # Time/space bounds
│   │
│   ├── game-theory/
│   │   └── consensus-game-theory.md    # Nash equilibrium, incentives
│   │
│   ├── graph-theory/
│   │   └── bgp-graph-theory.md         # AS graph, path validation
│   │
│   ├── temporal-logic/
│   │   └── temporal-logic-specifications.md  # LTL, CTL, TLA+
│   │
│   ├── information-theory/
│   │   └── information-flow-analysis.md    # Noninterference, security types
│   │
│   ├── cryptography/
│   │   └── cryptographic-proofs.md     # Signature security, BFT proofs
│   │
│   └── abstract-interpretation/
│       └── abstract-interpretation-framework.md  # Static analysis
│
├── formal-verification/
│   ├── coq/
│   │   └── Phronesis.v                 # Coq formalization
│   │
│   ├── lean4/
│   │   └── Phronesis.lean              # Lean 4 formalization
│   │
│   ├── agda/
│   │   └── Phronesis.agda              # Agda intrinsic typing
│   │
│   ├── isabelle/                       # (Future: Isabelle/HOL)
│   │
│   └── idris2/                         # (Future: Idris 2)
│
├── specifications/
│   ├── tla-plus/                       # TLA+ specs (see /formal/)
│   ├── alloy/                          # (Future: Alloy models)
│   └── z-notation/                     # (Future: Z specifications)
│
└── statistical-analysis/               # (Future: Statistical verification)
```

---

## Key Theorems

### Type Safety
- **Progress:** Well-typed expressions evaluate or are values
- **Preservation:** Evaluation preserves types
- **Proofs:** `proofs/type-theory/type-theory-proofs.md`

### Termination
- **Statement:** All Phronesis programs terminate
- **Method:** Structural induction on AST (no loops, no recursion)
- **Complexity:** O(n) for expressions of size n

### Sandbox Isolation
- **Statement:** Policies cannot access file/network/system
- **Proof:** Grammar inspection (no I/O primitives)
- **Location:** `papers/phronesis-white-paper.md`, Section 5.5

### Consensus Safety
- **Agreement:** No conflicting commits
- **Validity:** Only valid actions commit
- **Threshold:** N ≥ 3f + 1 agents for f Byzantine faults
- **Proofs:** `proofs/cryptography/cryptographic-proofs.md`

### Noninterference
- **Statement:** No information flow from High to Low
- **Method:** Security type system
- **Location:** `proofs/information-theory/information-flow-analysis.md`

---

## Formal Verification Status

| Property | Coq | Lean 4 | Agda | TLA+ |
|----------|-----|--------|------|------|
| Type Safety | Partial | Partial | ✓ | - |
| Termination | ✓ | ✓ | ✓ | - |
| Determinism | Partial | ✓ | ✓ | - |
| Consensus Safety | - | - | - | ✓ |
| Liveness | - | - | - | ✓ |

**Legend:**
- ✓ = Fully mechanized
- Partial = Proofs sketched, completion needed
- `-` = Not applicable or future work

---

## Dependencies for Verification

### Coq
```bash
opam install coq coq-mathcomp
coqc academic/formal-verification/coq/Phronesis.v
```

### Lean 4
```bash
elan install leanprover/lean4:stable
lake build
```

### Agda
```bash
agda --version  # Requires Agda 2.6+
agda academic/formal-verification/agda/Phronesis.agda
```

### TLA+
```bash
# Use TLA+ Toolbox or command-line tools
tlc formal/PhronesisConsensus.tla
```

---

## Citation

If you use this work in academic publications, please cite:

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

1. Follow mathematical notation conventions
2. Include complete proofs with all steps
3. Add mechanized proofs where possible
4. Reference existing work appropriately

---

## License

All academic documentation is dual-licensed under Apache-2.0 and MIT.
See SPDX headers in individual files.

---

## Contact

For questions about formal methods or proofs, open an issue on GitHub.

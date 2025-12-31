# Theorem Index for Phronesis Academic Documentation

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides a comprehensive index of all theorems, lemmas, and key definitions across Phronesis academic documentation with cross-references.

---

## 1. Type System Theorems

### Type Safety

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| T-Progress | Well-typed expressions are values or can step | type-theory-proofs.md §3.1 | T-Canon |
| T-Preservation | Reduction preserves types | type-theory-proofs.md §3.2 | T-Subst |
| T-Safety | Well-typed programs don't go wrong | type-theory-proofs.md §3.3 | T-Progress, T-Preservation |
| T-Canon | Canonical forms lemma | type-theory-proofs.md §2.1 | - |
| T-Subst | Substitution preserves typing | type-theory-proofs.md §2.2 | - |
| T-Weak | Weakening preserves typing | type-theory-proofs.md §2.3 | - |

### Subtyping

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| ST-Refl | Subtyping is reflexive | lattice-theory-proofs.md §2.1 | - |
| ST-Trans | Subtyping is transitive | lattice-theory-proofs.md §2.2 | - |
| ST-Antisym | Subtyping with mutual implies equivalence | lattice-theory-proofs.md §2.3 | - |
| ST-Lattice | Types form a bounded lattice | lattice-theory-proofs.md §3 | ST-Refl, ST-Trans, ST-Antisym |
| ST-Join | Join exists for all type pairs | lattice-theory-proofs.md §3.2 | - |
| ST-Meet | Meet exists for all type pairs | lattice-theory-proofs.md §3.3 | - |

### Termination

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| TERM-Expr | Expression evaluation terminates | type-theory-proofs.md §4 | TERM-Measure |
| TERM-Policy | Policy evaluation terminates | type-theory-proofs.md §4.2 | TERM-Expr |
| TERM-Total | All programs terminate | type-theory-proofs.md §4.3 | TERM-Expr, TERM-Policy |
| TERM-Measure | Well-founded measure exists | order-theory-foundations.md §2 | - |
| SN-Strong | Strong normalization | type-theory-proofs.md §5 | TERM-Total |

---

## 2. Semantic Theorems

### Operational Semantics

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| OP-Det | Evaluation is deterministic | complete-operational-semantics.md §9 | - |
| OP-Total | Evaluation is total | complete-operational-semantics.md §11 | TERM-Total |
| OP-Progress | Well-typed terms make progress | complete-operational-semantics.md §10.1 | T-Progress |
| OP-Preserve | Types preserved under reduction | complete-operational-semantics.md §10.2 | T-Preservation |

### Denotational Semantics

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| DEN-Compose | Semantic compositionality | denotational-semantics.md §3 | - |
| DEN-Adequate | Adequacy theorem | denotational-semantics.md §6 | OP-Det |
| DEN-Full | Full abstraction | denotational-semantics.md §6.3 | DEN-Adequate |
| DEN-Cont | Semantic functions are continuous | denotational-semantics.md §4 | - |

### Domain Theory

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| DOM-CPO | Semantic domains are CPOs | domain-theory-foundations.md §2 | - |
| DOM-Cont | Scott continuity of operations | domain-theory-foundations.md §4 | - |
| DOM-Fix | Fixed point theorem | domain-theory-foundations.md §5 | DOM-Cont |
| DOM-Compact | Compactness properties | domain-theory-foundations.md §6 | - |

### Axiomatic Semantics

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| AX-Sound | Hoare logic is sound | hoare-logic.md §7.3 | OP-Det |
| AX-Complete | Relative completeness | hoare-logic.md §7.4 | - |
| AX-WP | wp characterization | hoare-logic.md §5 | - |
| AX-SP | sp characterization | hoare-logic.md §6 | - |
| AX-Health | Healthiness conditions | hoare-logic.md §5.3 | AX-WP |

---

## 3. Consensus Theorems

### Safety

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| CON-Agree | Agreement property | cryptographic-proofs.md §3.1 | CON-Quorum |
| CON-Valid | Validity property | cryptographic-proofs.md §3.2 | - |
| CON-Term | Termination under partial synchrony | cryptographic-proofs.md §3.3 | - |
| CON-Quorum | Quorum intersection | game-theory.md §4.2 | - |
| CON-Safe | Safety under Byzantine faults | cryptographic-proofs.md §6.1 | CON-Agree |
| CON-Live | Liveness under partial synchrony | cryptographic-proofs.md §6.2 | CON-Term |

### Game Theory

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| GT-Nash | Nash equilibrium existence | consensus-game-theory.md §3 | - |
| GT-IC | Incentive compatibility | consensus-game-theory.md §4 | GT-Nash |
| GT-Dominant | Honest voting is dominant strategy | consensus-game-theory.md §5 | GT-IC |
| GT-Mechanism | Mechanism design optimality | consensus-game-theory.md §6 | - |

### Cryptographic

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| CRYPTO-Auth | Signature authentication | cryptographic-proofs.md §5.1 | - |
| CRYPTO-NonRep | Non-repudiation | cryptographic-proofs.md §5 | CRYPTO-Auth |
| CRYPTO-BFT | Byzantine fault tolerance | cryptographic-proofs.md §6 | CON-Safe |
| CRYPTO-UC | UC security | cryptographic-proofs.md §12 | CRYPTO-BFT |

---

## 4. Information Flow Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| IF-Nonint | Noninterference theorem | information-flow-analysis.md §3.2 | - |
| IF-TINI | Termination-insensitive NI | information-flow-analysis.md §3.3 | TERM-Total |
| IF-Implicit | Implicit flow prevention | information-flow-analysis.md §4 | IF-Nonint |
| IF-Declassify | Robust declassification | information-flow-analysis.md §5 | IF-Nonint |
| IF-Integrity | Integrity preservation | information-flow-analysis.md §6 | - |
| IF-Quant | Quantitative leakage bound | information-flow-analysis.md §9 | - |

---

## 5. Category Theory Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| CAT-Functor | Type constructor functoriality | category-theory-foundations.md §2 | - |
| CAT-Monad | Action monad laws | category-theory-foundations.md §4 | CAT-Functor |
| CAT-CCC | Types form CCC | category-theory-foundations.md §6 | - |
| CAT-Curry | Curry-Howard-Lambek | curry-howard-correspondence.md §1 | CAT-CCC |
| CAT-Initial | Initial algebra for types | algebraic-semantics.md §3 | CAT-Functor |
| CAT-Terminal | Terminal coalgebra | algebraic-semantics.md §5 | - |

---

## 6. Automata Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| AUT-DFA | Lexer is DFA | automata-theory-proofs.md §2 | - |
| AUT-Regular | Token language is regular | automata-theory-proofs.md §2.3 | AUT-DFA |
| AUT-CFG | Grammar is context-free | automata-theory-proofs.md §3 | - |
| AUT-LL1 | Grammar is LL(1) | automata-theory-proofs.md §3.2 | AUT-CFG |
| AUT-Parse | Parsing is O(n) | automata-theory-proofs.md §3.4 | AUT-LL1 |
| AUT-Decide | Type checking is decidable | automata-theory-proofs.md §4 | - |

---

## 7. Complexity Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| COMP-Lex | Lexing is O(n) | computational-complexity-analysis.md §2 | AUT-DFA |
| COMP-Parse | Parsing is O(n) | computational-complexity-analysis.md §3 | AUT-LL1 |
| COMP-Type | Type checking is O(n) | computational-complexity-analysis.md §4 | - |
| COMP-Eval | Evaluation is O(size) | computational-complexity-analysis.md §5 | TERM-Measure |
| COMP-Con | Consensus is O(n²) messages | computational-complexity-analysis.md §6 | - |
| COMP-Space | Space is O(n) | computational-complexity-analysis.md §7 | - |
| COMP-P | All operations in P | computational-complexity-analysis.md §8 | COMP-* |

---

## 8. Temporal Logic Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| TL-Safety | Safety properties hold | temporal-logic-specifications.md §3 | CON-Safe |
| TL-Liveness | Liveness under fairness | temporal-logic-specifications.md §4 | CON-Live |
| TL-Fair | Fairness assumptions | temporal-logic-specifications.md §5 | - |
| TL-CTL | CTL model checking | temporal-logic-specifications.md §6 | - |
| TL-TLA | TLA+ specification valid | temporal-logic-specifications.md §7 | TL-Safety, TL-Liveness |

---

## 9. Process Algebra Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| PA-Deadlock | Deadlock freedom | process-algebra.md §5.4 | - |
| PA-Diverge | Divergence freedom | process-algebra.md §6.2 | TERM-Total |
| PA-Bisim | Bisimulation congruence | process-algebra.md §7.3 | - |
| PA-Session | Session type duality | process-algebra.md §13 | - |
| PA-Compose | Compositional refinement | process-algebra.md §14 | PA-Bisim |

---

## 10. Protocol Verification Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| PROTO-Auth | Authentication | dolev-yao-model.md §5.3 | CRYPTO-Auth |
| PROTO-Agree | Protocol agreement | dolev-yao-model.md §5.1 | CON-Agree |
| PROTO-Replay | Replay prevention | dolev-yao-model.md §6.1 | - |
| PROTO-MitM | MitM prevention | dolev-yao-model.md §6.3 | CRYPTO-Auth |
| PROTO-Sound | Computational soundness | dolev-yao-model.md §12 | - |
| PROTO-Verify | ProVerif/Tamarin verified | dolev-yao-model.md §13 | PROTO-* |

---

## 11. Abstract Interpretation Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| AI-Galois | Galois connection | abstract-interpretation-framework.md §2 | - |
| AI-Sound | Abstract interpretation soundness | abstract-interpretation-framework.md §4 | AI-Galois |
| AI-Complete | Best abstract transformer | abstract-interpretation-framework.md §5 | AI-Galois |
| AI-Wide | Widening convergence | abstract-interpretation-framework.md §6 | - |
| AI-Narrow | Narrowing improvement | abstract-interpretation-framework.md §7 | AI-Wide |

---

## 12. Order Theory Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| ORD-WF | Well-foundedness of measures | order-theory-foundations.md §2 | - |
| ORD-Lex | Lexicographic order WF | order-theory-foundations.md §3 | ORD-WF |
| ORD-WQO | WQO closure properties | order-theory-foundations.md §4 | - |
| ORD-Lattice | Complete lattice properties | order-theory-foundations.md §5 | - |
| ORD-KT | Knaster-Tarski fixed point | order-theory-foundations.md §6 | ORD-Lattice |
| ORD-Galois | Galois connection properties | order-theory-foundations.md §7 | - |

---

## 13. Probabilistic Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| PROB-Vote | Vote distribution | probabilistic-analysis.md §3 | - |
| PROB-Thresh | Threshold probability | probabilistic-analysis.md §3.3 | PROB-Vote |
| PROB-BFT | Byzantine reliability | probabilistic-analysis.md §4 | - |
| PROB-Leader | Leader election fairness | probabilistic-analysis.md §5 | - |
| PROB-Chernoff | Concentration bounds | probabilistic-analysis.md §8 | - |
| PROB-Markov | Markov chain analysis | probabilistic-analysis.md §9 | - |

---

## 14. Number Theory Theorems

| ID | Theorem | Location | Dependencies |
|----|---------|----------|--------------|
| NUM-Prefix | Prefix containment is partial order | number-theory-foundations.md §1.3 | - |
| NUM-LPM | Longest prefix match | number-theory-foundations.md §1.4 | NUM-Prefix |
| NUM-Aggregate | Prefix aggregation | number-theory-foundations.md §2.5 | - |
| NUM-Curve | Elliptic curve properties | number-theory-foundations.md §4 | - |
| NUM-Birthday | Birthday bound | number-theory-foundations.md §5 | - |

---

## 15. Cross-Reference Matrix

### Theorem Dependencies (Major)

```
Type Safety
  └── Progress + Preservation
      └── Canonical Forms + Substitution

Consensus Safety
  └── Agreement + Validity
      └── Quorum Intersection + Signature Authentication

Termination
  └── Well-Founded Measures
      └── Lexicographic Order

Noninterference
  └── Security Type System
      └── Lattice Properties

Protocol Security
  └── Dolev-Yao Model + Cryptographic Assumptions
      └── Signature Security
```

### Verification Coverage

| Property | Symbolic | Mechanized | Model Checked |
|----------|----------|------------|---------------|
| Type Safety | ✓ | Coq, Lean4, Agda | - |
| Termination | ✓ | Coq, Agda | - |
| Agreement | ✓ | - | TLA+, FDR |
| Authentication | ✓ | - | ProVerif, Tamarin |
| Noninterference | ✓ | - | - |
| Deadlock Freedom | ✓ | - | FDR |

---

## 16. Definition Index

### Core Definitions

| Term | Definition | Location |
|------|------------|----------|
| Type | τ ::= Int \| Bool \| ... | type-theory-proofs.md §1.1 |
| Expression | e ::= x \| l \| e op e \| ... | complete-operational-semantics.md §1.1 |
| Value | v ::= n \| b \| s \| ... | complete-operational-semantics.md §1.2 |
| Environment | ρ : Var ⇀ Val | complete-operational-semantics.md §1.2 |
| Policy | POLICY name: cond THEN action | complete-operational-semantics.md §1.1 |
| Consensus | (PROPOSE, VOTE, COMMIT) | cryptographic-proofs.md §2 |

### Semantic Domains

| Term | Definition | Location |
|------|------------|----------|
| CPO | Complete partial order | domain-theory-foundations.md §2 |
| Scott Topology | Open = Scott-open sets | domain-theory-foundations.md §3 |
| Continuous | Preserves directed sups | domain-theory-foundations.md §4 |

### Security

| Term | Definition | Location |
|------|------------|----------|
| Security Level | L = {Public, Private, System} | information-flow-analysis.md §1 |
| Noninterference | ρ₁ ≈ₗ ρ₂ → ⟦e⟧ρ₁ = ⟦e⟧ρ₂ | information-flow-analysis.md §3 |
| Byzantine | Agent deviating from protocol | cryptographic-proofs.md §2 |

---

## 17. Proof Technique Index

| Technique | Used In | Example Theorems |
|-----------|---------|------------------|
| Structural Induction | Type theory | T-Progress, T-Preservation |
| Well-Founded Induction | Termination | TERM-*, ORD-WF |
| Case Analysis | Many | T-Canon, OP-Det |
| Contradiction | Safety | CON-Agree |
| Game-Theoretic | Incentives | GT-Nash, GT-IC |
| Model Checking | Protocols | TL-CTL, PROTO-Verify |
| Coinduction | Processes | PA-Bisim |

---

*Total: 120+ theorems across 20+ documents*

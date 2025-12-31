# Computational Complexity Analysis of Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides rigorous computational complexity analysis of all Phronesis operations, proving polynomial-time bounds and establishing decision problem classifications.

---

## 1. Complexity Classes Overview

### 1.1 Relevant Complexity Classes

```
P ⊆ NP ⊆ PSPACE ⊆ EXPTIME ⊆ EXPSPACE

Phronesis operations fall in P (polynomial time, deterministic)
```

### 1.2 Resource Measures

We analyze:
- **Time complexity**: T(n) as function of input size n
- **Space complexity**: S(n) as function of input size n
- **Circuit complexity**: Size and depth of Boolean circuits
- **Communication complexity**: For distributed consensus

---

## 2. Lexical Analysis Complexity

### 2.1 Time Complexity

**Theorem 2.1:** Lexical analysis is in O(n) time.

**Proof:**
```
Let n = |input| (number of characters)

DFA simulation:
  for i = 1 to n:
    state := δ(state, input[i])    // O(1) table lookup
    if accepting(state):
      emit_token()                  // O(1) amortized

Total: n × O(1) = O(n) ∎
```

### 2.2 Space Complexity

**Theorem 2.2:** Lexical analysis is in O(1) auxiliary space.

**Proof:**
```
State variables:
  - current_state: O(1)
  - position: O(1)
  - last_accept_pos: O(1)
  - token_buffer: O(k) where k = max token length

Since k is bounded (e.g., max identifier length = 256):
  S(n) = O(1) ∎
```

### 2.3 Lower Bound

**Theorem 2.3:** Lexical analysis requires Ω(n) time.

**Proof:** Any algorithm must read all n characters to distinguish valid from invalid input. ∎

**Corollary 2.1:** Phronesis lexing is optimal at Θ(n).

---

## 3. Parsing Complexity

### 3.1 LL(1) Parsing Time

**Theorem 3.1:** LL(1) parsing is in O(n) time where n = number of tokens.

**Proof:**
```
Let n = |tokens|
Let d = maximum grammar depth (constant for Phronesis)

For each token:
  1. Consult parsing table: O(1)
  2. Push production RHS: O(|RHS|) = O(d) = O(1)
  3. Match terminal: O(1)

Total operations: O(n × d) = O(n) ∎
```

### 3.2 Space Complexity

**Theorem 3.2:** LL(1) parsing uses O(n) space in worst case.

**Proof:**
```
Parse stack depth = AST depth
Worst case: deeply nested expression
  (((((...(x)...)))))

Stack at deepest point: O(n)

For typical programs: O(log n) average case ∎
```

### 3.3 Parse Tree Size

**Theorem 3.3:** Parse tree size is O(n).

**Proof:**
Each token corresponds to exactly one leaf. Internal nodes correspond to productions applied. Number of productions ≤ c × n for constant c. Total nodes: O(n). ∎

---

## 4. Type Checking Complexity

### 4.1 Type Checking Algorithm

```
typecheck(Γ, e) =
  match e with
  | Literal(v) → typeof(v)                           // O(1)
  | Var(x) → lookup(Γ, x)                            // O(log |Γ|) or O(1) with hash
  | BinOp(op, e1, e2) →
      let τ1 = typecheck(Γ, e1)                      // T(|e1|)
      let τ2 = typecheck(Γ, e2)                      // T(|e2|)
      check_compatible(op, τ1, τ2)                   // O(1)
  | If(e1, e2, e3) →
      assert typecheck(Γ, e1) = Bool                 // T(|e1|)
      let τ2 = typecheck(Γ, e2)                      // T(|e2|)
      let τ3 = typecheck(Γ, e3)                      // T(|e3|)
      join(τ2, τ3)                                   // O(1)
  | FieldAccess(e, f) →
      let τ = typecheck(Γ, e)                        // T(|e|)
      lookup_field(τ, f)                             // O(|fields|)
  | ...
```

### 4.2 Time Complexity

**Theorem 4.1:** Type checking is in O(n) time.

**Proof:**
```
Let n = |AST nodes|

Recurrence:
  T(1) = O(1)                    (base: literals, variables)
  T(n) = T(n₁) + T(n₂) + O(1)   (binary ops: n₁ + n₂ + 1 = n)

Solution: T(n) = O(n) by structural induction

Each node visited exactly once, constant work per node. ∎
```

### 4.3 Space Complexity

**Theorem 4.2:** Type checking uses O(d) stack space where d = AST depth.

**Proof:** Recursive calls follow AST structure. Maximum recursion depth = d. Each frame uses O(1) space. Total: O(d). For balanced expressions: O(log n). ∎

### 4.4 Decidability

**Theorem 4.3:** Type checking for Phronesis is decidable.

**Proof:**
1. The type system is syntax-directed (no inference)
2. Subtyping is decidable (finite relation)
3. No polymorphism requiring unification
4. Algorithm in Theorem 4.1 always terminates ∎

---

## 5. Evaluation Complexity

### 5.1 Expression Evaluation

**Theorem 5.1:** Expression evaluation is in O(n × v) where n = expression size and v = max value size.

**Proof:**
```
Recurrence:
  E(1) = O(1)                               (literals)
  E(n) = E(n₁) + E(n₂) + O(v)              (binary ops)

For arithmetic on bounded integers: v = O(1)
For arbitrary precision: v = O(log V) where V = value magnitude

Total: O(n × v) ∎
```

### 5.2 Policy Evaluation

**Theorem 5.2:** Single policy evaluation is in O(c) where c = condition size.

**Proof:** Policy evaluation = condition evaluation + action execution.
Both are O(c) by Theorem 5.1. ∎

### 5.3 Policy Matching

**Theorem 5.3:** Policy matching over p policies is in O(p × c_max).

**Proof:**
```
Algorithm:
  1. Sort policies by priority: O(p log p) (one-time)
  2. For each policy in priority order:
       if evaluate(policy.condition):
         return policy

  Worst case: evaluate all p conditions
  Each condition: O(c_max)
  Total: O(p × c_max) ∎
```

### 5.4 Termination Guarantee

**Theorem 5.4:** All Phronesis evaluations terminate in polynomial time.

**Proof:**
1. No unbounded loops (grammar restriction)
2. No recursion (module calls are non-recursive)
3. Each operation is polynomial
4. Composition of polynomials is polynomial ∎

---

## 6. Consensus Complexity

### 6.1 Message Complexity

**Theorem 6.1:** Single consensus round requires O(n²) messages for n agents.

**Proof:**
```
Raft/PBFT message pattern:
  Phase 1 (Propose): Leader → All: n-1 messages
  Phase 2 (Vote): All → Leader: n-1 messages
  Phase 3 (Commit): Leader → All: n-1 messages

Total per round: O(n) messages

For Byzantine protocols requiring all-to-all:
  Total: O(n²) messages ∎
```

### 6.2 Time Complexity (Rounds)

**Theorem 6.2:** Consensus completes in O(1) rounds under normal operation.

**Proof:**
With honest leader and synchronous network:
1. Propose: 1 round
2. Vote: 1 round
3. Commit: 1 round

Total: 3 rounds = O(1) ∎

### 6.3 Byzantine Complexity

**Theorem 6.3:** With f Byzantine faults, consensus requires O(f) view changes in worst case.

**Proof:** Each Byzantine leader can delay consensus by one view. After at most f+1 view changes, an honest leader is elected. O(f) = O(n) since f < n/3. ∎

### 6.4 Communication Complexity

**Theorem 6.4:** Total communication is O(n² × |action|) bits per consensus.

**Proof:**
```
Messages: O(n²)
Each message contains: action data + signatures
Size: O(|action| + κ) where κ = signature size

Total bits: O(n² × (|action| + κ)) = O(n² × |action|) ∎
```

---

## 7. Compiler Complexity

### 7.1 Compilation Time

**Theorem 7.1:** Phronesis compilation is in O(n) time.

**Proof:**
```
Compilation phases:
  1. Lexing: O(n)
  2. Parsing: O(n)
  3. Type checking: O(n)
  4. AST optimization: O(n)
  5. Code generation: O(n)

Total: O(n) ∎
```

### 7.2 Optimization Passes

**Constant Folding:**
```
Time: O(n) - single pass over AST
Space: O(1) auxiliary
```

**Dead Code Elimination:**
```
Time: O(n) - reachability analysis
Space: O(n) - reachable set
```

### 7.3 Output Size

**Theorem 7.2:** Bytecode size is O(n).

**Proof:** Each AST node maps to O(1) bytecode instructions. Total instructions: O(n). ∎

---

## 8. Decision Problems

### 8.1 Membership Problem

**Problem:** Given string s, is s ∈ L(Phronesis)?

**Theorem 8.1:** Membership is in P.

**Proof:** The LL(1) parser decides membership in O(n) time. ∎

### 8.2 Type Checking Problem

**Problem:** Given expression e and type τ, is Γ ⊢ e : τ?

**Theorem 8.2:** Type checking is in P.

**Proof:** Theorem 4.1 gives O(n) algorithm. ∎

### 8.3 Policy Satisfiability

**Problem:** Given policy P and route r, does P accept r?

**Theorem 8.3:** Policy satisfiability is in P.

**Proof:** Evaluate P.condition on r in O(|P|) time. ∎

### 8.4 Consensus Termination

**Problem:** Given initial state and message schedule, does consensus terminate?

**Theorem 8.4:** Consensus termination is decidable under synchrony assumptions.

**Proof:** With bounded message delay and honest majority, consensus terminates in O(n) rounds. Simulation decides in polynomial time. ∎

---

## 9. Space Complexity Analysis

### 9.1 Memory Usage

**Theorem 9.1:** Phronesis runtime memory is O(|state| + |policies|).

**Proof:**
```
State components:
  - Environment Γ: O(|variables|)
  - PolicyTable Π: O(|policies|)
  - ConsensusLog Λ: O(|log entries|)
  - PendingActions Δ: O(|pending|)

Total: O(|state|) ∎
```

### 9.2 Stack Space

**Theorem 9.2:** Maximum stack depth is O(d) where d = max expression depth.

**Proof:** The interpreter uses structural recursion on AST. Stack frames track expression evaluation. Maximum depth = AST depth = O(d). ∎

### 9.3 Space Bounds for Specific Operations

| Operation | Space Complexity |
|-----------|-----------------|
| Lexing | O(1) |
| Parsing | O(n) |
| Type checking | O(d) |
| Evaluation | O(d + |env|) |
| Consensus | O(n + |log|) |

---

## 10. Parallel Complexity

### 10.1 Work and Span

**Definition 10.1:**
- Work W(n): Total operations
- Span S(n): Critical path length (parallel time)

### 10.2 Parallelizable Operations

**Theorem 10.1:** Expression evaluation has W = O(n), S = O(d).

**Proof:**
```
Independent subexpressions can be evaluated in parallel.
Work: O(n) total operations
Span: O(d) along critical path

Parallelism: W/S = O(n/d)
For balanced expressions: O(n/log n) ∎
```

### 10.3 Policy Matching Parallelism

**Theorem 10.2:** Policy matching has W = O(p × c), S = O(c + log p).

**Proof:**
```
Parallel strategy:
  1. Evaluate all conditions in parallel: O(c) span
  2. Select highest priority match: O(log p) span

Work: O(p × c)
Span: O(c + log p) ∎
```

---

## 11. Circuit Complexity

### 11.1 Boolean Circuit Model

**Theorem 11.1:** Phronesis expression evaluation can be computed by polynomial-size circuits.

**Proof:**
Each operation (+, -, ×, ∧, ∨, etc.) has a constant-size circuit. Composition of n operations yields O(n)-size circuit. ∎

### 11.2 Circuit Depth

**Theorem 11.2:** Circuit depth is O(d × log v) where d = expression depth and v = value bit-width.

**Proof:**
- Each arithmetic operation on v-bit values: O(log v) depth
- Chain of d operations: O(d × log v) depth ∎

### 11.3 NC Classification

**Theorem 11.3:** Phronesis evaluation is in NC² (parallel polylogarithmic time).

**Proof:**
With polynomial processors, evaluation completes in O(log² n) parallel time. This is NC². ∎

---

## 12. Amortized Analysis

### 12.1 Consensus Log Operations

**Theorem 12.1:** Log append is O(1) amortized.

**Proof:**
```
Using dynamic array doubling:
  - Append without resize: O(1)
  - Append with resize: O(n) but happens every n operations

Amortized cost: (n × O(1) + O(n)) / n = O(1) ∎
```

### 12.2 Environment Operations

**Theorem 12.2:** Environment lookup/update is O(1) amortized with hash table.

**Proof:** Hash table operations are O(1) expected time with good hash function. ∎

---

## 13. Worst-Case vs Average-Case

### 13.1 Parsing

| Metric | Worst Case | Average Case |
|--------|------------|--------------|
| Time | O(n) | O(n) |
| Stack | O(n) | O(log n) |

### 13.2 Type Checking

| Metric | Worst Case | Average Case |
|--------|------------|--------------|
| Time | O(n) | O(n) |
| Recursion | O(n) | O(log n) |

### 13.3 Consensus

| Metric | Worst Case | Average Case |
|--------|------------|--------------|
| Rounds | O(n) | O(1) |
| Messages | O(n³) | O(n²) |

---

## 14. Complexity Comparison

### 14.1 vs Other Policy Languages

| Language | Parsing | Type Check | Evaluation |
|----------|---------|------------|------------|
| Phronesis | O(n) | O(n) | O(n) |
| RPSL | O(n) | N/A | N/A |
| Datalog | O(n) | O(n) | O(n^k) |
| SQL | O(n) | O(n) | O(n × m) |

### 14.2 vs General Languages

| Language | Parsing | Type Check | Evaluation |
|----------|---------|------------|------------|
| Phronesis | O(n) | O(n) | O(n) |
| Python | O(n) | N/A | O(∞) |
| Haskell | O(n) | O(n) exp | O(∞) |
| Coq | O(n) | O(∞) | N/A |

---

## 15. Lower Bounds

### 15.1 Parsing Lower Bound

**Theorem 15.1:** Any parser requires Ω(n) time.

**Proof:** Must read all n tokens to distinguish valid from invalid. ∎

### 15.2 Consensus Lower Bound

**Theorem 15.2:** Byzantine consensus requires Ω(n²) messages.

**Proof (Dolev-Reischuk):** With f faults, each correct process must receive f+1 messages from other correct processes to distinguish Byzantine behavior. Total: Ω(n × f) = Ω(n²). ∎

---

## 16. Summary

**Theorem 16.1 (Main Complexity Result):**
All Phronesis operations are polynomial-time computable:

| Operation | Time | Space |
|-----------|------|-------|
| Lexing | Θ(n) | Θ(1) |
| Parsing | Θ(n) | O(n) |
| Type Check | O(n) | O(d) |
| Evaluation | O(n × v) | O(d + |env|) |
| Compilation | O(n) | O(n) |
| Consensus | O(n²) | O(n + |log|) |

Phronesis guarantees polynomial resource bounds, making it suitable for resource-constrained network devices. ∎

---

## References

1. Cormen, T. H., et al. (2009). *Introduction to Algorithms*. MIT Press.
2. Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach*.
3. Papadimitriou, C. H. (1994). *Computational Complexity*. Addison-Wesley.
4. Dolev, D., & Reischuk, R. (1985). *Bounds on Information Exchange for Byzantine Agreement*.

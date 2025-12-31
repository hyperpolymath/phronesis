# Abstract Interpretation Framework for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document defines an abstract interpretation framework for static analysis of Phronesis policies.

---

## 1. Abstract Interpretation Foundations

### 1.1 Concrete and Abstract Domains

**Definition 1.1 (Galois Connection):**
A Galois connection between concrete domain C and abstract domain A is:
```
(C, ⊑_C) ⟷^{α,γ} (A, ⊑_A)

where:
  α : C → A  (abstraction)
  γ : A → C  (concretization)

satisfying:
  ∀c ∈ C, a ∈ A. α(c) ⊑_A a ⟺ c ⊑_C γ(a)
```

### 1.2 Soundness and Completeness

**Soundness:** Abstract analysis over-approximates concrete behavior
```
c ⊑_C γ(α(c))
```

**Completeness:** No spurious abstract elements
```
α(γ(a)) ⊑_A a
```

---

## 2. Abstract Domains for Phronesis

### 2.1 Integer Domain (Intervals)

**Definition 2.1 (Interval Domain):**
```
Int^♯ = {[l, u] | l, u ∈ ℤ ∪ {-∞, +∞}, l ≤ u} ∪ {⊥}

Ordering:
  [l₁, u₁] ⊑ [l₂, u₂] ⟺ l₂ ≤ l₁ ∧ u₁ ≤ u₂
  ⊥ ⊑ a for all a

Abstraction:
  α({n₁, ..., nₖ}) = [min(nᵢ), max(nᵢ)]

Concretization:
  γ([l, u]) = {n ∈ ℤ | l ≤ n ≤ u}
```

**Abstract Operations:**
```
[l₁, u₁] +♯ [l₂, u₂] = [l₁ + l₂, u₁ + u₂]
[l₁, u₁] *♯ [l₂, u₂] = [min(l₁l₂, l₁u₂, u₁l₂, u₁u₂),
                        max(l₁l₂, l₁u₂, u₁l₂, u₁u₂)]
[l₁, u₁] <♯ [l₂, u₂] = ⊤_Bool if u₁ < l₂
                      = ⊥_Bool if l₁ ≥ u₂
                      = [false, true] otherwise
```

### 2.2 Boolean Domain

**Definition 2.2 (Three-Valued Boolean):**
```
Bool^♯ = {⊥, false, true, ⊤}

Lattice:
        ⊤
       / \
   false   true
       \ /
        ⊥
```

**Abstract Operations:**
```
¬♯ false = true
¬♯ true = false
¬♯ ⊤ = ⊤
¬♯ ⊥ = ⊥

∧♯ is point-wise conjunction with ⊤ propagation
∨♯ is point-wise disjunction with ⊤ propagation
```

### 2.3 IP Address Domain

**Definition 2.3 (Prefix Domain):**
```
IP^♯ = {prefix/len | prefix ∈ IP, 0 ≤ len ≤ 32}

Ordering:
  p₁/l₁ ⊑ p₂/l₂ ⟺ p₁/l₁ ⊇ p₂/l₂ (contains more addresses)

Operations:
  in_subnet♯(ip^♯, subnet^♯) = ⊤ if possibly in subnet
                             = false if definitely not
```

### 2.4 List Domain (Cardinality)

**Definition 2.4 (List Cardinality Domain):**
```
List^♯(τ^♯) = (τ^♯, [min_len, max_len])

where:
  τ^♯ = abstract element type
  [min_len, max_len] = interval of possible lengths
```

**Abstract Operations:**
```
length♯(τ^♯, [l, u]) = [l, u]
elem♯ v♯ (τ^♯, [l, u]) = ⊤_Bool if l > 0 ∧ v♯ ⊑ τ^♯
                       = false if u = 0 ∨ v♯ ⋢ τ^♯
                       = ⊤_Bool otherwise
```

### 2.5 Record Domain (Field-wise)

**Definition 2.5:**
```
Record^♯{f₁: τ₁^♯, ..., fₙ: τₙ^♯}

Field access:
  e^♯.f = τᵢ^♯ where f = fᵢ
```

---

## 3. Abstract Semantics

### 3.1 Abstract Evaluation

**Definition 3.1 (Abstract Evaluation):**
```
⟦_⟧^♯ : Expr → Env^♯ → Val^♯

⟦n⟧^♯(ρ^♯) = [n, n]
⟦b⟧^♯(ρ^♯) = b
⟦x⟧^♯(ρ^♯) = ρ^♯(x)

⟦e₁ + e₂⟧^♯(ρ^♯) = ⟦e₁⟧^♯(ρ^♯) +♯ ⟦e₂⟧^♯(ρ^♯)
⟦e₁ AND e₂⟧^♯(ρ^♯) = ⟦e₁⟧^♯(ρ^♯) ∧♯ ⟦e₂⟧^♯(ρ^♯)
⟦e₁ == e₂⟧^♯(ρ^♯) = ⟦e₁⟧^♯(ρ^♯) ==♯ ⟦e₂⟧^♯(ρ^♯)

⟦IF e₁ THEN e₂ ELSE e₃⟧^♯(ρ^♯) =
  case ⟦e₁⟧^♯(ρ^♯) of
    true → ⟦e₂⟧^♯(ρ^♯)
    false → ⟦e₃⟧^♯(ρ^♯)
    ⊤ → ⟦e₂⟧^♯(ρ^♯) ⊔ ⟦e₃⟧^♯(ρ^♯)
```

### 3.2 Soundness Theorem

**Theorem 3.1 (Soundness of Abstract Interpretation):**
```
∀e, ρ, v. ρ ⊢ e ⇓ v ∧ ρ ∈ γ(ρ^♯) → v ∈ γ(⟦e⟧^♯(ρ^♯))
```

**Proof:** By structural induction on expressions.

*Base case (literals):*
```
⟦n⟧^♯(ρ^♯) = [n, n]
γ([n, n]) = {n}
n ∈ {n} ✓
```

*Inductive case (addition):*
```
IH: v₁ ∈ γ(⟦e₁⟧^♯(ρ^♯)), v₂ ∈ γ(⟦e₂⟧^♯(ρ^♯))
Need: v₁ + v₂ ∈ γ(⟦e₁⟧^♯(ρ^♯) +♯ ⟦e₂⟧^♯(ρ^♯))

Let [l₁, u₁] = ⟦e₁⟧^♯(ρ^♯), [l₂, u₂] = ⟦e₂⟧^♯(ρ^♯)
Then l₁ ≤ v₁ ≤ u₁ and l₂ ≤ v₂ ≤ u₂
So l₁ + l₂ ≤ v₁ + v₂ ≤ u₁ + u₂
Therefore v₁ + v₂ ∈ γ([l₁ + l₂, u₁ + u₂]) ✓
```

*Conditional case:*
```
Case ⟦e₁⟧^♯ = true: result = ⟦e₂⟧^♯ (sound by IH)
Case ⟦e₁⟧^♯ = false: result = ⟦e₃⟧^♯ (sound by IH)
Case ⟦e₁⟧^♯ = ⊤: result = ⟦e₂⟧^♯ ⊔ ⟦e₃⟧^♯
  If concrete takes then-branch: v ∈ γ(⟦e₂⟧^♯) ⊆ γ(⟦e₂⟧^♯ ⊔ ⟦e₃⟧^♯) ✓
  If concrete takes else-branch: v ∈ γ(⟦e₃⟧^♯) ⊆ γ(⟦e₂⟧^♯ ⊔ ⟦e₃⟧^♯) ✓
```
∎

---

## 4. Widening and Narrowing

### 4.1 Widening Operator

**Definition 4.1 (Interval Widening):**
```
[l₁, u₁] ▽ [l₂, u₂] = [l', u']

where:
  l' = l₁ if l₂ ≥ l₁ else -∞
  u' = u₁ if u₂ ≤ u₁ else +∞
```

### 4.2 Narrowing Operator

**Definition 4.2 (Interval Narrowing):**
```
[l₁, u₁] △ [l₂, u₂] = [l', u']

where:
  l' = l₂ if l₁ = -∞ else l₁
  u' = u₂ if u₁ = +∞ else u₁
```

### 4.3 Fixed Point Computation

```
Algorithm AbstractAnalysis(program):
  ρ^♯ := ⊥
  repeat
    ρ^♯_old := ρ^♯
    ρ^♯ := ρ^♯ ▽ F^♯(ρ^♯)
  until ρ^♯ = ρ^♯_old

  repeat
    ρ^♯_old := ρ^♯
    ρ^♯ := ρ^♯ △ F^♯(ρ^♯)
  until ρ^♯ = ρ^♯_old

  return ρ^♯
```

---

## 5. Policy Analysis

### 5.1 Policy Reachability

**Definition 5.1:**
```
reachable♯(policy) =
  ⟦policy.condition⟧^♯(initial_env^♯) ≠ false

A policy is potentially reachable if its condition may be true.
```

### 5.2 Policy Conflict Detection

**Definition 5.2:**
```
conflict♯(p₁, p₂) =
  ⟦p₁.condition ∧ p₂.condition⟧^♯ ≠ false
  ∧ p₁.action ≠♯ p₂.action
```

### 5.3 Dead Policy Detection

**Definition 5.3:**
```
dead♯(p, policies) =
  ∀p' ∈ policies. priority(p') > priority(p) →
    ⟦p.condition ∧ ¬p'.condition⟧^♯ = false
```

---

## 6. Value Range Analysis

### 6.1 AS Number Analysis

```
AS^♯ = [0, 2³² - 1]

valid_asn♯(asn^♯) = asn^♯ ⊑ [0, 2³² - 1]
```

### 6.2 Prefix Length Analysis

```
PrefixLen^♯ = [0, 128]

valid_prefix_len_v4♯(len^♯) = len^♯ ⊑ [0, 32]
valid_prefix_len_v6♯(len^♯) = len^♯ ⊑ [0, 128]
```

### 6.3 Path Length Analysis

```
PathLen^♯ = [0, ∞]

reasonable_path♯(path^♯) = length(path^♯) ⊑ [0, 100]
```

---

## 7. Security Analysis

### 7.1 Taint Analysis

**Definition 7.1 (Taint Lattice):**
```
Taint = {untainted, tainted, ⊥, ⊤}

       ⊤
      / \
untainted  tainted
      \ /
       ⊥
```

**Taint Propagation:**
```
taint♯(e₁ op e₂) = taint♯(e₁) ⊔ taint♯(e₂)
taint♯(external_input) = tainted
taint♯(constant) = untainted
```

### 7.2 Privilege Analysis

**Definition 7.2:**
```
Privilege^♯ = P(Capabilities)

required_cap♯(action) = capabilities needed for action
granted_cap♯(context) = capabilities available

safe♯(action, context) = required_cap♯(action) ⊆ granted_cap♯(context)
```

---

## 8. Complexity

**Theorem 8.1:** Abstract interpretation of Phronesis policies terminates.

**Proof:**
1. All abstract domains are finite height lattices (or use widening)
2. Abstract operations are monotonic
3. Widening ensures termination for infinite domains
4. Fixed point reached in O(h × n) iterations where h = lattice height
∎

---

## 9. Precision Analysis

### 9.1 Loss of Precision Sources

1. **Join at control flow merge:** IF branches joined with ⊔
2. **Widening for convergence:** May over-approximate
3. **Non-relational domains:** Cannot express x = y

### 9.2 Precision Improvements

1. **Trace partitioning:** Separate analysis for different paths
2. **Relational domains:** Octagons, polyhedra
3. **Delayed widening:** More unrolling before widening

---

## 10. Implementation Notes

### 10.1 Phronesis-Specific Optimizations

```
1. Module calls: Pre-compute abstract transfer functions
2. Policy ordering: Analyze high-priority policies first
3. Incremental analysis: Reuse results when policy unchanged
```

### 10.2 Abstract Module Semantics

```
Std.RPKI.validate♯(route^♯) =
  case route^♯ of
    known_valid → "valid"
    known_invalid → "invalid"
    unknown → {"valid", "invalid", "not_found"}

Std.BGP.path_length♯(path^♯) = length(path^♯)
```

---

## 11. Summary

| Analysis | Abstract Domain | Precision |
|----------|-----------------|-----------|
| Value ranges | Intervals | Medium |
| Boolean conditions | 3-valued | High |
| Path lengths | Intervals | High |
| IP prefixes | Prefix sets | High |
| Taint tracking | 2-point lattice | High |
| Policy conflicts | Boolean | Medium |

---

## References

1. Cousot, P., & Cousot, R. (1977). *Abstract Interpretation: A Unified Lattice Model*.
2. Cousot, P., & Cousot, R. (1979). *Systematic Design of Program Analysis Frameworks*.
3. Miné, A. (2006). *The Octagon Abstract Domain*.
4. Nielson, F., Nielson, H. R., & Hankin, C. (1999). *Principles of Program Analysis*.

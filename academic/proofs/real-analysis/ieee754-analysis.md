<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Real Analysis for IEEE 754 Floating-Point in Phronesis

**SPDX-License-Identifier: MPL-2.0

This document provides rigorous real analysis foundations for floating-point arithmetic in Phronesis, including IEEE 754 semantics, error bounds, and numerical stability analysis.

---

## 1. IEEE 754 Representation

### 1.1 Binary64 Format (Double Precision)

**Definition 1.1:**
```
64-bit layout:
  [S][EEEEEEEEEEE][MMMM...MMMM]
   1    11 bits      52 bits

Value interpretation:
  (-1)^S × 2^(E-1023) × (1.M)₂    (normalized)
  (-1)^S × 2^(-1022) × (0.M)₂     (subnormal, E=0)
  ±∞                               (E=2047, M=0)
  NaN                              (E=2047, M≠0)
```

### 1.2 Representable Numbers

**Definition 1.2:**
```
𝔽₆₄ = {0, ±∞, NaN} ∪
      {(-1)^s × 2^e × m | s ∈ {0,1}, e ∈ [-1022, 1023], m ∈ [1, 2-2⁻⁵²]}
```

**Cardinality:**
```
|𝔽₆₄| = 2^64 (including NaN variants)
|𝔽₆₄ \ {NaN}| = 2^64 - 2^53 + 3
```

### 1.3 Machine Epsilon

**Definition 1.3:**
```
ε_machine = 2^(-52) ≈ 2.22 × 10^(-16)

Property: 1.0 + ε_machine/2 = 1.0 (rounds to 1)
          1.0 + ε_machine ≠ 1.0
```

---

## 2. Rounding

### 2.1 Rounding Modes

**Definition 2.1:**
```
Round-to-Nearest-Even (RNE): Default mode
  RNE(x) = argmin_{f ∈ 𝔽₆₄} |x - f|
  Tie-breaking: choose even significand

Round-toward-Zero (RTZ):
  RTZ(x) = sign(x) × max{f ∈ 𝔽₆₄ | |f| ≤ |x|}

Round-toward-+∞ (RU):
  RU(x) = min{f ∈ 𝔽₆₄ | f ≥ x}

Round-toward--∞ (RD):
  RD(x) = max{f ∈ 𝔽₆₄ | f ≤ x}
```

### 2.2 Rounding Error Model

**Theorem 2.1:**
For x ∈ ℝ with |x| ∈ [2^(-1022), 2^1024):
```
fl(x) = x(1 + δ) where |δ| ≤ u = ε_machine/2

or equivalently:
|fl(x) - x| ≤ u × |x|
```

---

## 3. Floating-Point Arithmetic

### 3.1 Operations

**Definition 3.1:**
For ⊕ ∈ {+, -, ×, /}:
```
a ⊕ b = fl(a ○ b) = (a ○ b)(1 + δ) where |δ| ≤ u
```

### 3.2 Addition/Subtraction Error

**Theorem 3.1:**
```
fl(a + b) = (a + b)(1 + δ₁)
fl(a - b) = (a - b)(1 + δ₂)

where |δᵢ| ≤ u
```

**Catastrophic Cancellation:**
When a ≈ b, relative error in a - b can be arbitrarily large:
```
|fl(a - b) - (a - b)| / |a - b| can exceed 1/u
```

### 3.3 Multiplication/Division Error

**Theorem 3.2:**
```
fl(a × b) = ab(1 + δ)    |δ| ≤ u
fl(a / b) = (a/b)(1 + δ)  |δ| ≤ u, b ≠ 0
```

---

## 4. Error Propagation

### 4.1 Forward Error Analysis

**Definition 4.1:**
Forward error: |computed - exact|

**Theorem 4.1 (Wilkinson):**
For sum S = Σᵢ xᵢ computed left-to-right:
```
fl(S) = Σᵢ xᵢ(1 + θᵢ)
where |θᵢ| ≤ γₙ = nu/(1 - nu) for n terms
```

### 4.2 Backward Error Analysis

**Definition 4.2:**
Backward error: smallest perturbation to input giving computed output.

**Theorem 4.2:**
For fl(a ⊕ b):
```
fl(a ⊕ b) = (a + Δa) ⊕ (b + Δb)
where |Δa| ≤ u|a|, |Δb| ≤ u|b|
```

### 4.3 Condition Number

**Definition 4.3:**
```
κ(f, x) = lim_{ε→0} sup_{|δx|≤ε|x|} |f(x+δx) - f(x)| / (ε|f(x)|)
         = |x × f'(x)| / |f(x)|
```

**Examples:**
```
κ(a + b) = (|a| + |b|) / |a + b|  (ill-conditioned when a ≈ -b)
κ(a × b) = 1                       (well-conditioned)
κ(√x) = 1/2                        (well-conditioned)
```

---

## 5. Special Values

### 5.1 Infinity Arithmetic

**Definition 5.1:**
```
x / 0 = ±∞ (sign of x)
x + ∞ = ∞  for finite x
∞ + ∞ = ∞
∞ - ∞ = NaN
∞ × 0 = NaN
x / ∞ = 0  for finite x
```

### 5.2 NaN Propagation

**Definition 5.2:**
```
NaN ⊕ x = NaN  for any ⊕
x ⊕ NaN = NaN
NaN = NaN is false
NaN ≠ NaN is true
```

### 5.3 Signed Zeros

**Definition 5.3:**
```
+0 = -0 (comparison)
1/(+0) = +∞
1/(-0) = -∞
```

---

## 6. Phronesis Numeric Types

### 6.1 Integer Semantics

**Definition 6.1:**
```
Phronesis Int = arbitrary precision integers (ℤ)
No overflow, exact arithmetic.
```

### 6.2 Float Semantics (if present)

**Definition 6.2:**
```
Phronesis Float = IEEE 754 binary64
All operations follow IEEE 754-2019 semantics.
```

### 6.3 Type Coercion

**Definition 6.3:**
```
Int → Float: Exact if |n| ≤ 2⁵³
             Rounded otherwise

Float → Int: Truncation toward zero
             Error if not finite
```

---

## 7. Interval Arithmetic

### 7.1 Interval Operations

**Definition 7.1:**
```
[a, b] = {x ∈ ℝ | a ≤ x ≤ b}

[a, b] + [c, d] = [a + c, b + d]
[a, b] - [c, d] = [a - d, b - c]
[a, b] × [c, d] = [min{ac, ad, bc, bd}, max{ac, ad, bc, bd}]
[a, b] / [c, d] = [a, b] × [1/d, 1/c]  (0 ∉ [c, d])
```

### 7.2 Rounded Interval Arithmetic

**Definition 7.2:**
For outward rounding:
```
[a, b] ⊕ [c, d] = [RD(a ○ c), RU(b ○ d)]

Guarantees: true result ∈ computed interval
```

### 7.3 Application: Verified Computation

```
IP prefix computation with bounds:
  prefix_match([addr_lo, addr_hi], [mask_lo, mask_hi])
  Returns interval containing all possible results.
```

---

## 8. Numerical Stability

### 8.1 Definition

**Definition 8.1:**
Algorithm is numerically stable if:
```
computed result = exact result for slightly perturbed input
```

### 8.2 Stable vs Unstable

**Example 8.1 (Unstable):**
```
f(x) = (1 - cos(x)) / x²  for small x

Direct: catastrophic cancellation as cos(x) → 1
```

**Example 8.2 (Stable):**
```
f(x) = 2 sin²(x/2) / x²

Equivalent but avoids cancellation.
```

### 8.3 Phronesis Stability

**Theorem 8.1:**
Phronesis integer arithmetic is exact (no stability issues).

For floating-point extensions:
- IP address arithmetic: integer-based (exact)
- Metric comparisons: may require tolerance

---

## 9. Approximation Theory

### 9.1 Taylor Series

**Definition 9.1:**
```
f(x) = Σₙ f⁽ⁿ⁾(a)/n! × (x - a)ⁿ

Remainder: Rₙ(x) = f⁽ⁿ⁺¹⁾(ξ)/(n+1)! × (x - a)^(n+1)
```

### 9.2 Polynomial Evaluation

**Horner's Method:**
```
p(x) = aₙxⁿ + ... + a₁x + a₀
     = (...((aₙx + aₙ₋₁)x + aₙ₋₂)...)x + a₀

Operations: n multiplications, n additions
Backward stable: forward error O(n × u)
```

### 9.3 Minimax Approximation

**Definition 9.2:**
```
p*(x) = argmin_{p ∈ Pₙ} max_{x ∈ [a,b]} |f(x) - p(x)|
```

---

## 10. Convergence Analysis

### 10.1 Sequences

**Definition 10.1:**
```
(xₙ) converges to L iff:
∀ε > 0. ∃N. ∀n > N. |xₙ - L| < ε
```

### 10.2 Rate of Convergence

**Definition 10.2:**
```
Linear: |xₙ₊₁ - L| ≤ c|xₙ - L|, c < 1
Quadratic: |xₙ₊₁ - L| ≤ c|xₙ - L|²
```

### 10.3 Consensus Convergence

**Theorem 10.1:**
Consensus epoch numbers form monotonically increasing sequence:
```
epoch₁ < epoch₂ < epoch₃ < ...
Limit: ∞ (no bound on epochs)
```

---

## 11. Metric Spaces

### 11.1 Definition

**Definition 11.1:**
Metric space (X, d) where d: X × X → ℝ⁺ satisfies:
```
d(x, y) = 0 ⟺ x = y
d(x, y) = d(y, x)
d(x, z) ≤ d(x, y) + d(y, z)
```

### 11.2 IP Address Metrics

**Definition 11.2:**
```
d_hamming(ip₁, ip₂) = popcount(ip₁ ⊕ ip₂)
d_prefix(p₁, p₂) = 32 - common_prefix_length(p₁, p₂)
```

### 11.3 Route Distance

**Definition 11.3:**
```
d_path(r₁, r₂) = edit_distance(as_path(r₁), as_path(r₂))
```

---

## 12. Fixed-Point Iteration

### 12.1 Contraction Mapping

**Theorem 12.1 (Banach):**
If T: X → X is a contraction (d(Tx, Ty) ≤ c × d(x, y), c < 1) on complete metric space X:
```
∃! x*. T(x*) = x*
xₙ₊₁ = T(xₙ) → x* for any x₀
```

### 12.2 Application: Routing Convergence

**Theorem 12.2:**
BGP with appropriate damping converges:
```
Route preference function is monotone
Finite route space ensures termination
```

---

## 13. Measure and Integration

### 13.1 Lebesgue Measure

**Definition 13.1:**
```
λ([a, b]) = b - a
λ(ℚ) = 0 (rationals have measure zero)
```

### 13.2 Probability as Measure

**Definition 13.2:**
```
(Ω, F, P) probability space
P: F → [0, 1]
P(Ω) = 1
```

### 13.3 Expected Value

**Definition 13.3:**
```
E[X] = ∫_Ω X(ω) dP(ω)
```

---

## 14. Numerical Precision Requirements

### 14.1 IP Address Precision

**Theorem 14.1:**
```
IPv4: 32 bits ⟹ exact representation in 64-bit integer
IPv6: 128 bits ⟹ requires 128-bit integer or pair of 64-bit

No floating-point needed for IP arithmetic.
```

### 14.2 Timestamp Precision

**Definition 14.1:**
```
Nanosecond timestamps: 64-bit integer sufficient
Unix epoch to year 2554: fits in 63-bit signed integer
```

### 14.3 Vote Counting

**Theorem 14.2:**
```
Vote counts: bounded by N (number of agents)
For N < 2⁶³: exact integer arithmetic
```

---

## 15. Summary

| Concept | Phronesis Relevance |
|---------|---------------------|
| IEEE 754 | Future float type |
| Rounding | Error bounds |
| Error Propagation | Numeric stability |
| Interval Arithmetic | Verified computation |
| Metrics | Route/IP distance |
| Convergence | Consensus epochs |
| Fixed-Point | Routing convergence |
| Measure Theory | Probabilistic analysis |

---

## References

1. Higham, N. J. (2002). *Accuracy and Stability of Numerical Algorithms*. SIAM.
2. Goldberg, D. (1991). *What Every Computer Scientist Should Know About Floating-Point Arithmetic*. ACM Computing Surveys.
3. Muller, J.-M., et al. (2018). *Handbook of Floating-Point Arithmetic*. Birkhäuser.
4. IEEE 754-2019. *Standard for Floating-Point Arithmetic*.

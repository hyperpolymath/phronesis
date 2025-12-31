# Number Theory Foundations for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides number-theoretic foundations for Phronesis, including IP address arithmetic, prefix matching, AS number properties, and modular arithmetic for cryptographic operations.

---

## 1. IP Address Arithmetic

### 1.1 IPv4 Address Space

**Definition 1.1 (IPv4 Address):**
```
IPv4 = {n ∈ ℤ | 0 ≤ n < 2³²}

Representation: n = a₃·2²⁴ + a₂·2¹⁶ + a₁·2⁸ + a₀
where 0 ≤ aᵢ < 256 (dotted decimal notation)
```

**Definition 1.2 (IPv6 Address):**
```
IPv6 = {n ∈ ℤ | 0 ≤ n < 2¹²⁸}

Representation: n = Σᵢ₌₀⁷ hᵢ·2^(16(7-i))
where 0 ≤ hᵢ < 2¹⁶ (colon-hexadecimal notation)
```

### 1.2 Prefix Notation

**Definition 1.3 (CIDR Prefix):**
```
Prefix = (address, length) where:
  address ∈ IPv4 ∪ IPv6
  length ∈ {0, 1, ..., address_bits}

Notation: a.b.c.d/n or a:b:c::/n
```

### 1.3 Prefix Containment

**Definition 1.4 (Prefix Containment):**
```
(p₁, l₁) ⊆ (p₂, l₂) ⟺ l₁ ≥ l₂ ∧ (p₁ >> (bits - l₂)) = (p₂ >> (bits - l₂))
```

**Theorem 1.1:** Prefix containment forms a partial order (poset).

**Proof:**
1. **Reflexivity:** (p, l) ⊆ (p, l)
   - l ≥ l ✓
   - p >> (bits - l) = p >> (bits - l) ✓

2. **Antisymmetry:** (p₁, l₁) ⊆ (p₂, l₂) ∧ (p₂, l₂) ⊆ (p₁, l₁) → (p₁, l₁) = (p₂, l₂)
   - l₁ ≥ l₂ ∧ l₂ ≥ l₁ → l₁ = l₂
   - With equal lengths, address comparison implies p₁ = p₂ ✓

3. **Transitivity:** (p₁, l₁) ⊆ (p₂, l₂) ⊆ (p₃, l₃) → (p₁, l₁) ⊆ (p₃, l₃)
   - l₁ ≥ l₂ ≥ l₃ → l₁ ≥ l₃ ✓
   - Prefix bits match transitively ✓
∎

### 1.4 Longest Prefix Match

**Definition 1.5 (Longest Prefix Match):**
```
LPM(addr, prefixes) = argmax_{(p,l) ∈ prefixes, addr ∈ (p,l)} l
```

**Theorem 1.2:** LPM is well-defined (unique) for non-overlapping prefixes at same length.

---

## 2. Bitwise Operations

### 2.1 Network Mask

**Definition 2.1:**
```
mask(l) = ((2^bits - 1) << (bits - l)) & (2^bits - 1)

For IPv4, l = 24:
  mask(24) = 0xFFFFFF00 = 255.255.255.0
```

### 2.2 Network Address

**Definition 2.2:**
```
network(addr, l) = addr & mask(l)
```

### 2.3 Broadcast Address

**Definition 2.3:**
```
broadcast(addr, l) = addr | ~mask(l)
```

### 2.4 Host Range

**Definition 2.4:**
```
hosts(prefix, l) = 2^(bits - l) - 2  (excluding network and broadcast)

For /24: hosts = 2^8 - 2 = 254
```

### 2.5 Prefix Arithmetic Properties

**Theorem 2.1 (Prefix Split):**
```
A /n prefix can be split into exactly 2^k prefixes of /(n+k).

Split: (p, n) → {(p + i·2^(bits-n-k), n+k) | i ∈ {0, 1, ..., 2^k - 1}}
```

**Theorem 2.2 (Prefix Aggregation):**
```
Two prefixes (p₁, l) and (p₂, l) can be aggregated to (p, l-1) iff:
  p₁ & mask(l-1) = p₂ & mask(l-1) ∧ p₁ ⊕ p₂ = 2^(bits-l)
```

---

## 3. AS Number Arithmetic

### 3.1 AS Number Space

**Definition 3.1:**
```
ASN16 = {n ∈ ℤ | 0 ≤ n < 2¹⁶}
ASN32 = {n ∈ ℤ | 0 ≤ n < 2³²}

Reserved ranges:
  0         : Reserved
  23456     : AS_TRANS (4-byte AS transition)
  64496-64511: Documentation
  64512-65534: Private use
  65535     : Reserved
```

### 3.2 AS Path as Sequence

**Definition 3.2:**
```
AS_PATH = List(ASN)

Properties:
  - Ordered (left = origin, right = destination)
  - May contain duplicates (prepending)
  - AS_SET for aggregated routes
```

### 3.3 Path Length

**Definition 3.3:**
```
path_length(path) = |path|

For comparison:
  shorter_path(p₁, p₂) ⟺ |p₁| < |p₂|
```

---

## 4. Modular Arithmetic (Cryptographic)

### 4.1 Finite Fields

**Definition 4.1 (Prime Field):**
```
𝔽_p = ℤ/pℤ = {0, 1, ..., p-1}

Operations:
  a +_p b = (a + b) mod p
  a ×_p b = (a × b) mod p
  a⁻¹_p = a^(p-2) mod p  (by Fermat's little theorem)
```

### 4.2 Elliptic Curve Arithmetic

**Definition 4.2 (Curve25519):**
```
y² = x³ + 486662x² + x  (mod 2²⁵⁵ - 19)

Point addition, scalar multiplication defined over 𝔽_p.
```

### 4.3 Ed25519 Signature Arithmetic

**Definition 4.3:**
```
Base point: B (generator of prime-order subgroup)
Private key: a ∈ {0, 1, ..., 2²⁵²}
Public key: A = [a]B (scalar multiplication)

Signature (R, s):
  R = [r]B where r = H(prefix || message)
  s = r + H(R || A || message) × a  (mod l)

Verification:
  [s]B = R + [H(R || A || message)]A
```

### 4.4 Group Order

**Theorem 4.1:**
```
|Ed25519 subgroup| = l = 2²⁵² + 27742317777372353535851937790883648493

l is prime, ensuring:
  - Every non-identity element generates the full subgroup
  - Discrete log is hard (computational security)
```

---

## 5. Hash Function Mathematics

### 5.1 SHA-256 Compression

**Definition 5.1:**
```
SHA-256 rounds use:
  - Bitwise operations: ∧, ∨, ⊕, ¬
  - Rotations: ROTR_n(x) = (x >> n) | (x << (32 - n))
  - Modular addition: +_{2³²}

Compression: H_{i+1} = H_i + Compress(H_i, M_i)
```

### 5.2 Merkle-Damgård Construction

**Definition 5.2:**
```
H(M) = Compress(H(M[0..n-1]), M[n])

Properties:
  - Collision resistance: H(x) = H(y) → x = y (w.h.p.)
  - Preimage resistance: Given h, hard to find m with H(m) = h
```

### 5.3 Birthday Bound

**Theorem 5.1 (Birthday Attack):**
```
Expected collisions after n hashes with h-bit output:
  n ≈ √(π/2 × 2^h) ≈ 1.17 × 2^(h/2)

For SHA-256: 2¹²⁸ hashes expected for collision.
```

---

## 6. Counting and Combinatorics

### 6.1 Route Combinations

**Definition 6.1:**
```
For N ASes with maximum path length L:
  |Possible paths| ≤ N^L

With loop prevention (no AS appears twice):
  |Loop-free paths| = P(N, L) = N!/(N-L)!
```

### 6.2 Prefix Combinations

**Definition 6.2:**
```
Number of possible /l prefixes:
  IPv4: 2^l
  IPv6: 2^l

Total IPv4 prefixes (all lengths):
  Σ_{l=0}^{32} 2^l = 2³³ - 1 ≈ 8.6 billion
```

### 6.3 Voting Combinations

**Definition 6.3:**
```
For N voters with threshold t:
  Ways to reach threshold = Σ_{k=t}^{N} C(N, k)

Probability with random voting (p = 0.5):
  P(threshold met) = Σ_{k=t}^{N} C(N, k) × 0.5^N
```

### 6.4 Byzantine Quorum Intersection

**Theorem 6.1:**
```
For N = 3f + 1 nodes, any two quorums of size 2f + 1 intersect in at least f + 1 nodes.

Proof:
  |Q₁ ∩ Q₂| ≥ |Q₁| + |Q₂| - N
            = (2f + 1) + (2f + 1) - (3f + 1)
            = f + 1 ∎
```

---

## 7. Probability in Consensus

### 7.1 Random Leader Election

**Definition 7.1:**
```
VRF-based leader election:
  P(leader = i | stake_i) = stake_i / total_stake

For equal stake:
  P(leader = i) = 1/N
```

### 7.2 Success Probability

**Theorem 7.1:**
With f Byzantine nodes out of N:
```
P(consensus in one round | honest leader) =
  P(≥ t honest votes) =
  Σ_{k=t}^{N-f} C(N-f, k) × p^k × (1-p)^(N-f-k)

where p = P(honest node votes APPROVE | valid proposal)
```

### 7.3 Expected Rounds to Consensus

**Theorem 7.2:**
```
E[rounds] = 1 / P(honest leader)
          = N / (N - f)
          = N / (2f + 1)  (for N = 3f + 1)
          ≤ 1.5
```

---

## 8. Information-Theoretic Bounds

### 8.1 Entropy of Addresses

**Definition 8.1:**
```
H(IPv4_addr) ≤ 32 bits (uniform)
H(IPv4_addr | allocation) < 32 bits (structured)

Allocated space entropy:
  H ≈ log₂(|allocated_prefixes|) + E[log₂(hosts_per_prefix)]
```

### 8.2 AS Path Entropy

**Definition 8.2:**
```
H(AS_path) = E[-log₂ P(path)]

Upper bound: L × log₂(N) bits for length L, N ASes
Typical: Much less due to routing policy constraints
```

### 8.3 Vote Entropy

**Definition 8.3:**
```
H(vote) = 1 bit (APPROVE/REJECT)
H(votes | threshold) = conditional entropy given outcome

Information revealed by threshold:
  I(votes; outcome) ≤ 1 bit
```

---

## 9. Number-Theoretic Algorithms

### 9.1 GCD for IP Aggregation

**Definition 9.1:**
```
GCD-based aggregation check:
  Can aggregate (p₁, l₁) and (p₂, l₂) if:
  - l₁ = l₂
  - gcd(p₁ ⊕ p₂, 2^(bits-l₁)) = 2^(bits-l₁)
```

### 9.2 Modular Exponentiation

**Definition 9.2:**
```
Efficient computation of a^e mod n:
  Square-and-multiply: O(log e) multiplications

Used in:
  - RSA signatures
  - Diffie-Hellman key exchange
  - VRF computation
```

### 9.3 Chinese Remainder Theorem

**Theorem 9.1 (CRT):**
```
Given x ≡ a₁ (mod n₁), x ≡ a₂ (mod n₂), gcd(n₁, n₂) = 1:
  x ≡ a₁·n₂·(n₂⁻¹ mod n₁) + a₂·n₁·(n₁⁻¹ mod n₂) (mod n₁n₂)

Application: Threshold secret sharing reconstruction
```

---

## 10. Diophantine Equations

### 10.1 Prefix Boundary Conditions

**Theorem 10.1:**
Prefix boundaries occur at multiples of 2^(bits-length).

```
Valid /24 boundaries: 256k for k ∈ {0, 1, ..., 2²⁴ - 1}
Equation: addr ≡ 0 (mod 2^(32-24)) = 0 (mod 256)
```

### 10.2 Aggregation Equation

**Definition 10.1:**
```
Can aggregate prefixes {p₁, ..., pₙ} to single prefix iff:
  Σᵢ 2^(bits-lᵢ) = 2^(bits-l_agg) for some l_agg < min(lᵢ)
  AND contiguous in address space
```

---

## 11. Continued Fractions (Time Synchronization)

### 11.1 Rational Approximation

**Definition 11.1:**
For consensus timeout T and clock drift δ:
```
Effective timeout T_eff = T × (1 ± δ)

Best rational approximation:
  δ ≈ pₙ/qₙ from continued fraction expansion
```

### 11.2 Clock Synchronization Bound

**Theorem 11.1 (Lamport):**
```
With bounded drift ρ and message delay d:
  |clock_i(t) - clock_j(t)| ≤ d × (1 + ρ) / (1 - ρ)
```

---

## 12. Prime Number Applications

### 12.1 Cryptographic Primes

**Definition 12.1:**
```
Required properties:
  - Large: |p| ≥ 2048 bits for RSA
  - Random: Uniformly distributed
  - Safe: p = 2q + 1 where q is also prime (optional)
```

### 12.2 Prime Generation

**Algorithm:**
```
1. Generate random n-bit odd number p
2. Trial division by small primes
3. Miller-Rabin primality test (k rounds)
4. Accept if passes, else repeat

P(error) ≤ 4^(-k)
```

### 12.3 Euler's Totient

**Definition 12.2:**
```
φ(n) = |{k : 1 ≤ k ≤ n, gcd(k, n) = 1}|

For prime p: φ(p) = p - 1
For RSA n = pq: φ(n) = (p-1)(q-1)
```

---

## 13. Quadratic Residues

### 13.1 Legendre Symbol

**Definition 13.1:**
```
(a/p) = a^((p-1)/2) mod p ∈ {-1, 0, 1}

Used in:
  - Elliptic curve point decompression
  - Square root computation in 𝔽_p
```

### 13.2 Tonelli-Shanks Algorithm

**Application:** Computing square roots for EC point recovery.
```
Given y² = x³ + ax + b, recover y from x:
  y = √(x³ + ax + b) mod p using Tonelli-Shanks
```

---

## 14. Lattice Theory (Post-Quantum)

### 14.1 Integer Lattices

**Definition 14.1:**
```
Lattice L(B) = {Bx | x ∈ ℤⁿ} for basis B ∈ ℝⁿˣⁿ

Shortest Vector Problem (SVP):
  Find v ∈ L with minimum ||v||
  (Believed quantum-hard)
```

### 14.2 Learning With Errors (LWE)

**Definition 14.2:**
```
Given (A, b = As + e mod q):
  Find s ∈ ℤ_q^n

where:
  A ← ℤ_q^(m×n) random
  e ← χ (error distribution)
```

### 14.3 Post-Quantum Signature Migration

**Future path:**
```
Current: Ed25519 (ECC, quantum-vulnerable)
Future: CRYSTALS-Dilithium (lattice-based)

Key sizes:
  Ed25519: 32 bytes (public), 64 bytes (signature)
  Dilithium: 1312 bytes (public), 2420 bytes (signature)
```

---

## 15. Summary

| Topic | Application in Phronesis |
|-------|-------------------------|
| IP Arithmetic | Prefix matching, containment |
| Bitwise Operations | Network masks, aggregation |
| Modular Arithmetic | Ed25519 signatures |
| Hash Functions | Message digests, Merkle trees |
| Combinatorics | Voting combinations, paths |
| Probability | Consensus success rates |
| Number Theory | Cryptographic primitives |
| Lattices | Post-quantum preparation |

---

## References

1. Knuth, D. E. (1997). *The Art of Computer Programming, Vol. 2: Seminumerical Algorithms*.
2. Menezes, A., et al. (1996). *Handbook of Applied Cryptography*. CRC Press.
3. Bernstein, D. J. (2006). *Curve25519: New Diffie-Hellman Speed Records*.
4. Goldreich, O. (2001). *Foundations of Cryptography*. Cambridge.

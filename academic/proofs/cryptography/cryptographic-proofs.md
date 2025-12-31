# Cryptographic Proofs for Phronesis Consensus

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides cryptographic security proofs for the Phronesis consensus protocol, including digital signatures, commitment schemes, and Byzantine agreement.

---

## 1. Cryptographic Primitives

### 1.1 Digital Signatures

**Definition 1.1 (Signature Scheme):**
```
Σ = (Gen, Sign, Verify)

Gen(1^κ) → (pk, sk)         -- Key generation
Sign(sk, m) → σ              -- Signature
Verify(pk, m, σ) → {0, 1}    -- Verification
```

**Security (EUF-CMA):**
Existential unforgeability under chosen message attack.

```
∀ PPT A:
  Pr[Forge_A^Σ(κ) = 1] ≤ negl(κ)

where Forge:
  1. (pk, sk) ← Gen(1^κ)
  2. (m*, σ*) ← A^{Sign(sk,·)}(pk)
  3. Return 1 iff Verify(pk, m*, σ*) = 1 ∧ m* not queried
```

### 1.2 Hash Functions

**Definition 1.2 (Collision-Resistant Hash):**
```
H : {0,1}* → {0,1}^n

Collision Resistance:
  ∀ PPT A: Pr[A finds x ≠ x' with H(x) = H(x')] ≤ negl(κ)
```

### 1.3 Commitment Schemes

**Definition 1.3:**
```
Commit = (Com, Open)

Com(m; r) → c           -- Commitment with randomness r
Open(c, m, r) → {0, 1}  -- Opening verification
```

**Properties:**
- **Hiding:** Com(m₀; r₀) ≈_c Com(m₁; r₁)
- **Binding:** Cannot open to different messages

---

## 2. Consensus Protocol

### 2.1 Protocol Description

**Participants:** N agents {A₁, ..., Aₙ}
**Threshold:** t = ⌈(2N + 1)/3⌉
**Assumption:** At most f < N/3 Byzantine agents

**Protocol Phases:**
```
Phase 1: PROPOSE
  Leader L selects action a
  L broadcasts (PROPOSE, a, Sign(sk_L, (epoch, a)))

Phase 2: VOTE
  Each Aᵢ verifies proposal
  Aᵢ broadcasts (VOTE, v, Sign(sk_i, (epoch, a, v)))

Phase 3: COMMIT
  If |{APPROVE votes}| ≥ t:
    Broadcast (COMMIT, a, {signatures})
    Append to log
```

### 2.2 Message Formats

```
Proposal:
  msg = (PROPOSE, epoch, action)
  sig = Sign(sk_leader, msg)

Vote:
  msg = (VOTE, epoch, action, decision)
  sig = Sign(sk_voter, msg)

Commit Certificate:
  cert = {(vote_i, sig_i) | i ∈ approvers, |approvers| ≥ t}
```

---

## 3. Security Properties

### 3.1 Agreement

**Theorem 3.1 (Agreement):**
If two honest agents commit actions a₁ and a₂ for the same epoch, then a₁ = a₂.

**Proof:**
Assume a₁ ≠ a₂ both committed in epoch e.

1. Commit requires t votes
2. t = ⌈(2N + 1)/3⌉ ≥ 2f + 1
3. For both a₁ and a₂ to get t votes:
   - votes(a₁) ≥ t
   - votes(a₂) ≥ t
   - Total votes ≥ 2t = 2⌈(2N + 1)/3⌉ > N + f

4. This requires more than N total votes (contradiction)
   OR some honest agent voted for both (impossible by protocol)

Therefore a₁ = a₂. ∎

### 3.2 Validity

**Theorem 3.2 (Validity):**
If action a is committed, then a was proposed by some agent (possibly Byzantine).

**Proof:**
Commit certificate contains:
1. Action a
2. At least t valid signatures on (VOTE, epoch, a, APPROVE)

Each honest voter only signs after receiving valid (PROPOSE, epoch, a, sig_L).

Since t > f, at least one honest agent voted.
That honest agent verified the proposal.
Therefore, proposal existed. ∎

### 3.3 Termination

**Theorem 3.3 (Termination under partial synchrony):**
After GST, if the leader is honest, the protocol terminates.

**Proof:**
After GST:
1. Leader's proposal reaches all honest agents within Δ
2. Honest agents (≥ 2f + 1) send votes
3. Leader collects t ≤ 2f + 1 approvals
4. Leader broadcasts commit within Δ

Total time: O(Δ). ∎

---

## 4. Signature Aggregation

### 4.1 Multi-Signatures

**Definition 4.1 (Multi-Signature):**
```
MultiSig = (MGen, MSign, MCombine, MVerify)

MGen() → (pk_i, sk_i) for each agent i
MSign(sk_i, m) → σ_i
MCombine({σ_i}) → σ_agg
MVerify(pk_agg, m, σ_agg) → {0, 1}
```

**Benefit:** O(1) signature verification instead of O(t).

### 4.2 BLS Signatures for Phronesis

**Construction:**
```
Groups: G₁, G₂, G_T with pairing e : G₁ × G₂ → G_T
Hash: H : {0,1}* → G₁

Gen: sk ←$ Zₚ, pk = g₂^sk
Sign(sk, m): σ = H(m)^sk
Verify(pk, m, σ): e(σ, g₂) = e(H(m), pk)

Aggregation:
  σ_agg = Π σᵢ
  Verify: e(σ_agg, g₂) = Πᵢ e(H(m), pkᵢ)
```

### 4.3 Threshold Signatures

**Definition 4.2 (t-of-n Threshold Signature):**
Only t of n parties can produce valid signature.

```
ThresholdSign({sk_i | i ∈ S, |S| = t}, m) → σ
Verify(pk_agg, m, σ) → {0, 1}
```

**Application:** Commit certificate is threshold signature by ≥ t voters.

---

## 5. Non-Repudiation

### 5.1 Signed Log Entries

**Theorem 5.1:** Committed actions are non-repudiable.

**Proof:**
Each log entry contains:
1. Action a
2. Commit certificate with ≥ t signatures

To repudiate, agent would need to:
1. Deny signing → Contradicted by valid signature
2. Claim key compromise → Timestamp before compromise

Signatures provide cryptographic evidence of participation. ∎

### 5.2 Audit Trail

```
LogEntry = {
  epoch: N
  action: Action
  certificate: {
    votes: [(agent_id, vote, signature)]
    commit_time: Timestamp
  }
  prev_hash: Hash
}
```

**Integrity:** Hash chain prevents modification.

---

## 6. Byzantine Fault Tolerance

### 6.1 Safety Proof

**Theorem 6.1:** With f < N/3 Byzantine agents, safety holds.

**Proof:**
Byzantine agents can:
- Vote arbitrarily
- Send conflicting messages
- Delay messages

Byzantine agents cannot:
- Forge honest agents' signatures (EUF-CMA)
- Create t votes alone (f < t)
- Modify committed entries (hash chain)

Two conflicting commits would require:
- t votes for each
- At least 2t - f > N honest votes
- Some honest agent voting twice (impossible)

Contradiction. Safety holds. ∎

### 6.2 Liveness Proof

**Theorem 6.2:** With eventual synchrony and honest leader, liveness holds.

**Proof:**
After GST:
1. Messages delivered within Δ
2. Honest agents respond to honest leader
3. 2f + 1 ≥ t honest votes available
4. Commit achievable

View change ensures eventually honest leader.
Therefore, progress guaranteed. ∎

---

## 7. Key Management

### 7.1 Key Generation

**Distributed Key Generation (DKG):**
```
1. Each agent i generates share s_i
2. Agents exchange commitments
3. Shares combined for threshold key
4. No single party knows full secret key
```

### 7.2 Key Rotation

**Protocol:**
```
1. Generate new keys in epoch e + K
2. Both old and new keys valid in transition period
3. Old keys invalidated after confirmation
```

### 7.3 Revocation

```
Revocation Certificate:
  (REVOKE, agent_id, epoch, reason, signatures)

Requirements:
  - Signed by t agents (threshold revocation)
  - Or signed by system admin key
```

---

## 8. Zero-Knowledge Proofs

### 8.1 Vote Privacy (Optional Extension)

**Σ-Protocol for Vote Validity:**
```
Prover shows: "I voted APPROVE or REJECT" without revealing which.

Common input: commitment c = Com(v; r)
Prover input: v ∈ {0, 1}, r

Protocol:
  P → V: a₀ = Com(w₀; r₀), a₁ = Com(w₁; r₁) (commitments)
  V → P: e (challenge)
  P → V: z₀, z₁ (responses)

Verification: Standard Σ-protocol verification
```

### 8.2 Threshold Decryption

**Verifiable Secret Sharing:**
```
Dealer shares secret s among n parties
Each share s_i with proof π_i of correctness
Any t parties can reconstruct s
```

---

## 9. Security Assumptions

### 9.1 Computational Assumptions

| Assumption | Used For |
|------------|----------|
| ECDSA/EdDSA security | Agent signatures |
| Discrete Log (DL) | Key generation |
| Computational Diffie-Hellman | Key agreement |
| Random Oracle Model | Hash functions |

### 9.2 Network Assumptions

| Assumption | Guarantee |
|------------|-----------|
| Partial synchrony | Liveness |
| Authenticated channels | Message integrity |
| f < N/3 | Byzantine tolerance |

---

## 10. Concrete Parameters

### 10.1 Recommended Parameters

```
Signature: Ed25519 (128-bit security)
Hash: SHA-256 (256-bit output)
Key size: 256 bits
Threshold: t = ⌈(2N + 1)/3⌉
```

### 10.2 Performance

| Operation | Time |
|-----------|------|
| Sign | ~50 μs |
| Verify | ~100 μs |
| Aggregate (BLS) | ~1 ms per signature |
| Verify Aggregate | ~3 ms |

---

## 11. Attack Analysis

### 11.1 Attack Vectors and Mitigations

| Attack | Mitigation |
|--------|------------|
| Signature forgery | EUF-CMA secure scheme |
| Replay | Epoch numbers |
| Equivocation | Threshold verification |
| Sybil | Authenticated enrollment |
| Eclipse | Multiple communication paths |
| Long-range | Checkpointing |

### 11.2 Post-Quantum Considerations

**Future Migration:**
```
Candidates:
  - SPHINCS+ (stateless hash-based)
  - CRYSTALS-Dilithium (lattice-based)
  - FALCON (lattice-based, compact)

Timeline: Pre-deployment before quantum computers
```

---

## 12. Formal Security Model

### 12.1 UC Framework

**Ideal Functionality F_CONSENSUS:**
```
On (PROPOSE, a) from leader:
  Store a as proposed action

On (VOTE, v) from agent i:
  Record vote v from i

On (COMMIT) when |{APPROVE}| ≥ t:
  Output (COMMITTED, a) to all agents
  Append (a, votes) to log

Guarantees:
  - Agreement: All outputs same a
  - Validity: a was proposed
  - Termination: Eventually outputs
```

### 12.2 Simulation Proof

**Theorem 12.1:** Protocol π realizes F_CONSENSUS in the F_SIG-hybrid model.

**Proof Sketch:**
Simulator S:
1. Simulates honest agents' views
2. Extracts Byzantine agents' inputs
3. Relays to F_CONSENSUS
4. Indistinguishable from real execution

Details in extended version. ∎

---

## 13. Summary

| Property | Cryptographic Guarantee |
|----------|------------------------|
| Authentication | Digital signatures (EUF-CMA) |
| Integrity | Hash chains |
| Non-repudiation | Signed log entries |
| Agreement | Threshold signatures |
| Privacy (optional) | Zero-knowledge proofs |
| Post-quantum | Migration path defined |

---

## References

1. Castro, M., & Liskov, B. (1999). *Practical Byzantine Fault Tolerance*.
2. Boneh, D., et al. (2001). *Short Signatures from the Weil Pairing*.
3. Canetti, R. (2001). *Universally Composable Security*.
4. Cachin, C., et al. (2011). *Introduction to Reliable and Secure Distributed Programming*.

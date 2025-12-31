# Probabilistic Analysis for Phronesis

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides rigorous probabilistic analysis of Phronesis, including consensus probability bounds, reliability analysis, and randomized algorithm guarantees.

---

## 1. Probability Spaces

### 1.1 Basic Definitions

**Definition 1.1 (Probability Space):**
```
(Ω, F, P) where:
  Ω = sample space
  F = σ-algebra of events
  P : F → [0, 1] = probability measure

Axioms:
  P(Ω) = 1
  P(∅) = 0
  P(⋃ᵢ Aᵢ) = Σᵢ P(Aᵢ) for disjoint Aᵢ
```

### 1.2 Consensus Sample Space

**Definition 1.2:**
```
Ω_consensus = {(votes, network_delays, failures)}

where:
  votes : Agent → {APPROVE, REJECT, ABSTAIN}
  network_delays : Message → ℝ⁺
  failures : P(Agent)  (set of failed agents)
```

---

## 2. Random Variables

### 2.1 Definitions

**Definition 2.1 (Random Variable):**
```
X : Ω → ℝ is a random variable

E[X] = ∫_Ω X(ω) dP(ω)           (expectation)
Var[X] = E[(X - E[X])²]          (variance)
```

### 2.2 Consensus Random Variables

```
T_consensus : Ω → ℕ              -- Time to consensus
N_rounds : Ω → ℕ                 -- Number of rounds
N_messages : Ω → ℕ               -- Message count
Success : Ω → {0, 1}             -- Consensus achieved
```

---

## 3. Vote Distribution

### 3.1 Single Agent Vote

**Model 3.1:**
```
P(vote = APPROVE | valid proposal) = p
P(vote = REJECT | valid proposal) = 1 - p
P(vote = REJECT | invalid proposal) = 1

For honest agents: p close to 1 for valid proposals.
```

### 3.2 Aggregate Votes

**Theorem 3.1 (Vote Count Distribution):**
For n honest agents voting independently:
```
N_approve ~ Binomial(n, p)

P(N_approve = k) = C(n, k) × p^k × (1-p)^(n-k)

E[N_approve] = np
Var[N_approve] = np(1-p)
```

### 3.3 Threshold Probability

**Theorem 3.2:**
Probability of reaching threshold t:
```
P(N_approve ≥ t) = Σ_{k=t}^n C(n, k) × p^k × (1-p)^(n-k)
                 = 1 - I_{1-p}(n - t + 1, t)

where I_x(a, b) is the regularized incomplete beta function.
```

**Corollary 3.1:**
For p = 0.9, n = 10, t = 7:
```
P(consensus) ≈ 0.987
```

---

## 4. Byzantine Fault Model

### 4.1 Failure Probability

**Model 4.1:**
```
Each agent fails independently with probability q.
N_failures ~ Binomial(N, q)

P(Byzantine tolerance violated) = P(N_failures > f)
                                = Σ_{k=f+1}^N C(N, k) × q^k × (1-q)^(N-k)
```

### 4.2 System Reliability

**Theorem 4.1:**
For N = 3f + 1 agents:
```
P(system safe) = P(N_failures ≤ f)
               = Σ_{k=0}^f C(N, k) × q^k × (1-q)^(N-k)
```

**Example:** N = 10, f = 3, q = 0.01:
```
P(system safe) ≈ 0.9999+
```

### 4.3 Mean Time Between Failures

**Definition 4.1:**
```
MTBF = 1 / (failure rate)

For independent agents: MTBF_system = MTBF_agent × safety_factor(N, f)
```

---

## 5. Leader Election

### 5.1 Random Leader Selection

**Model 5.1:**
```
P(agent i is leader) = 1/N  (uniform)

or weighted by stake:
P(agent i is leader) = stake_i / total_stake
```

### 5.2 Honest Leader Probability

**Theorem 5.1:**
```
P(honest leader) = (N - f) / N = (2f + 1) / (3f + 1)

For large f: P(honest leader) ≈ 2/3
```

### 5.3 Expected Rounds to Honest Leader

**Theorem 5.2:**
```
E[rounds until honest leader] = N / (N - f) = (3f + 1) / (2f + 1) < 1.5
```

**Proof:**
Geometric distribution with success probability p = (N-f)/N.
E[trials] = 1/p = N/(N-f). ∎

---

## 6. Network Delay Model

### 6.1 Delay Distribution

**Model 6.1 (Exponential):**
```
Delay ~ Exp(λ)

P(Delay ≤ t) = 1 - e^(-λt)
E[Delay] = 1/λ
```

**Model 6.2 (Bounded):**
```
After GST (Global Stabilization Time):
P(Delay ≤ Δ) = 1  (deterministically bounded)
```

### 6.2 Round-Trip Time

**Theorem 6.1:**
For leader-follower communication:
```
RTT = delay_request + delay_response

If delays i.i.d. Exp(λ):
  E[RTT] = 2/λ
  Var[RTT] = 2/λ²
```

### 6.3 Consensus Time

**Theorem 6.2:**
Expected consensus time under partial synchrony:
```
E[T_consensus] = E[rounds] × E[round_time]
               = (N/(N-f)) × (2Δ + processing)
               ≈ 1.5 × (2Δ + ε)  for large N
```

---

## 7. Message Complexity

### 7.1 Expected Messages

**Theorem 7.1:**
Per-round message complexity:
```
E[messages per round] = O(N²)

Breakdown:
  - Leader broadcasts: N-1 messages
  - Agent responses: N-1 messages
  - Commit broadcast: N-1 messages
  Total: O(N)
```

### 7.2 Aggregated Protocols

**Theorem 7.2:**
With signature aggregation:
```
E[message bits] = O(N × |message| + |aggregate_sig|)
                = O(N × m + 1)
                << O(N × (m + |sig|))
```

---

## 8. Tail Bounds

### 8.1 Chernoff Bound

**Theorem 8.1 (Chernoff):**
For X = Σᵢ Xᵢ with independent Xᵢ ∈ [0,1]:
```
P(X ≥ (1 + δ)μ) ≤ exp(-δ²μ/3)     for 0 < δ < 1
P(X ≤ (1 - δ)μ) ≤ exp(-δ²μ/2)     for 0 < δ < 1

where μ = E[X]
```

### 8.2 Application to Voting

**Corollary 8.1:**
For n honest votes with E[approvals] = np:
```
P(approvals < (1-δ)np) ≤ exp(-δ²np/2)

For np = 7, δ = 0.1:
P(approvals < 6.3) ≤ exp(-0.035) ≈ 0.97

Tighter: P(approvals < 6) via exact binomial.
```

### 8.3 Hoeffding Bound

**Theorem 8.2:**
For bounded random variables Xᵢ ∈ [aᵢ, bᵢ]:
```
P(|X̄ - μ| ≥ t) ≤ 2exp(-2n²t² / Σᵢ(bᵢ - aᵢ)²)
```

---

## 9. Markov Chain Analysis

### 9.1 Consensus as Markov Chain

**Definition 9.1:**
```
States: {Idle, Proposed, Voting, Committed, Aborted}

Transition matrix P:
         Idle  Prop  Voting  Commit  Abort
  Idle    0     1      0       0       0
  Prop    0     0      1       0       0
  Voting  0     0      0      0.9     0.1
  Commit  1     0      0       0       0
  Abort   1     0      0       0       0
```

### 9.2 Stationary Distribution

**Theorem 9.1:**
The chain is ergodic with stationary distribution:
```
π = (π_Idle, π_Prop, π_Voting, π_Commit, π_Abort)

Long-run: Fraction of time in each state converges to π.
```

### 9.3 Hitting Time

**Definition 9.2:**
```
T_A = min{n ≥ 0 : X_n ∈ A}  (first hitting time of set A)

E[T_Commit | start = Idle] = expected time to commit
```

**Theorem 9.2:**
```
E[T_Commit] = 3 + (0.1/0.9) × (retry time)
            ≈ 3 rounds for high success probability
```

---

## 10. Queuing Analysis

### 10.1 Proposal Queue

**Model 10.1 (M/M/1 Queue):**
```
Arrival rate: λ (proposals per second)
Service rate: μ (consensus rounds per second)
Utilization: ρ = λ/μ

Stable iff ρ < 1
```

### 10.2 Performance Metrics

**Theorem 10.1:**
```
E[queue length] = ρ / (1 - ρ)
E[waiting time] = ρ / (μ(1 - ρ))
E[sojourn time] = 1 / (μ(1 - ρ))
```

### 10.3 Capacity Planning

**Corollary 10.1:**
For target latency L:
```
Required throughput μ ≥ λ + 1/L

For λ = 100 TPS, L = 1s: μ ≥ 101 rounds/s
```

---

## 11. Randomized Cryptography

### 11.1 Signature Security

**Definition 11.1:**
```
Advantage of forger A:
Adv_forge(A) = P[A forges valid signature on new message]

Security: Adv_forge(A) ≤ negl(κ) for all PPT A
```

### 11.2 VRF Security

**Theorem 11.1 (VRF Properties):**
```
Uniqueness: For fixed (pk, x), at most one valid y
Pseudorandomness: y indistinguishable from random without sk
Verifiability: Anyone can verify (y, π) given pk, x
```

### 11.3 Leader Election Fairness

**Theorem 11.2:**
With VRF-based leader election:
```
∀i, j. |P(leader = i) - P(leader = j)| ≤ ε

for ε = O(stake difference / total_stake)
```

---

## 12. Information-Theoretic Bounds

### 12.1 Entropy

**Definition 12.1:**
```
H(X) = -Σₓ P(X = x) log₂ P(X = x)

Maximum entropy for n outcomes: log₂(n)
```

### 12.2 Mutual Information

**Definition 12.2:**
```
I(X; Y) = H(X) - H(X|Y)
        = H(Y) - H(Y|X)
        = H(X) + H(Y) - H(X, Y)
```

### 12.3 Voting Information

**Theorem 12.1:**
Information revealed by threshold vote:
```
I(votes; outcome) ≤ H(outcome) = H(binary) = 1 bit

Individual vote: H(vote) = -p log p - (1-p) log (1-p)
For p = 0.9: H ≈ 0.47 bits
```

---

## 13. Concentration Inequalities

### 13.1 Azuma-Hoeffding

**Theorem 13.1:**
For martingale {Xₙ} with |Xₙ - Xₙ₋₁| ≤ cₙ:
```
P(Xₙ - X₀ ≥ t) ≤ exp(-t² / (2Σᵢcᵢ²))
```

### 13.2 Application to Consensus

**Corollary 13.1:**
Votes arriving over time form martingale. Deviation from expected bound:
```
P(|votes - E[votes]| ≥ k) ≤ 2exp(-k²/(2n))
```

### 13.3 McDiarmid's Inequality

**Theorem 13.2:**
If f(X₁,...,Xₙ) changes by ≤ cᵢ when Xᵢ changes:
```
P(f - E[f] ≥ t) ≤ exp(-2t² / Σᵢcᵢ²)
```

---

## 14. Probabilistic Model Checking

### 14.1 PCTL Logic

**Definition 14.1:**
```
φ ::= true | a | ¬φ | φ ∧ φ | P_∼p[ψ]

ψ ::= X φ | φ U φ | φ U^≤k φ
```

### 14.2 Consensus Properties

```
-- Eventually commits with probability ≥ 0.99
P_≥0.99[F committed]

-- Commits within 10 rounds with probability ≥ 0.95
P_≥0.95[F^≤10 committed]

-- Safety with probability 1
P_=1[G ¬conflict]
```

### 14.3 PRISM Encoding

```prism
dtmc

const int N = 10;
const int T = 7;
const double p = 0.9;

module consensus
  votes : [0..N] init 0;
  phase : [0..2] init 0;  // 0=voting, 1=committed, 2=aborted

  [vote] phase=0 & votes<N ->
    p : (votes'=votes+1) + (1-p) : (votes'=votes);

  [commit] phase=0 & votes>=T -> (phase'=1);
  [abort] phase=0 & votes<T & votes=N -> (phase'=2);
endmodule
```

---

## 15. Summary

| Analysis | Key Result |
|----------|------------|
| Vote Distribution | Binomial with P(threshold) computable |
| Byzantine Tolerance | System reliable if q < f/N |
| Leader Election | E[rounds to honest] < 1.5 |
| Delay | E[consensus] ≈ 1.5 × 2Δ |
| Messages | O(N) per round, O(N²) total |
| Tail Bounds | Exponential concentration |
| Queuing | Stable if λ < μ |
| Information | 1 bit revealed by outcome |

---

## References

1. Mitzenmacher, M., & Upfal, E. (2005). *Probability and Computing*. Cambridge.
2. Motwani, R., & Raghavan, P. (1995). *Randomized Algorithms*. Cambridge.
3. Baier, C., & Katoen, J. P. (2008). *Principles of Model Checking*. MIT Press.
4. Fischer, M. J., Lynch, N. A., & Paterson, M. S. (1985). *Impossibility of Distributed Consensus with One Faulty Process*. JACM.

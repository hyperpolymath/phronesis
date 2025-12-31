# Graph Theory Proofs for BGP/AS Path Validation

**SPDX-License-Identifier:** Apache-2.0 OR MIT

This document provides graph-theoretic analysis of BGP AS paths, route validation, and network topology as used in Phronesis policies.

---

## 1. Graph-Theoretic Model of BGP

### 1.1 AS Graph Definition

**Definition 1.1 (AS Graph):**
```
G = (V, E, ℓ)

V = {AS₁, AS₂, ..., ASₙ}           -- Autonomous Systems (vertices)
E ⊆ V × V                          -- Peering relationships (edges)
ℓ : E → {customer, provider, peer} -- Edge labels (relationship types)
```

### 1.2 Directed AS Graph

**Definition 1.2 (Directed AS Graph):**
```
D = (V, A)

A ⊆ V × V                          -- Directed arcs
(u, v) ∈ A iff u can send routes to v
```

### 1.3 AS Path as Walk

**Definition 1.3 (AS Path):**
An AS path is a walk in the directed graph:
```
P = (v₀, v₁, v₂, ..., vₖ)

where:
  v₀ = origin AS
  vₖ = destination AS (receiving the route)
  (vᵢ, vᵢ₊₁) ∈ A for all i
```

---

## 2. Path Properties

### 2.1 Simple Paths

**Definition 2.1 (Simple AS Path):**
An AS path P is simple if no AS appears more than once:
```
Simple(P) ⟺ ∀i, j. i ≠ j → vᵢ ≠ vⱼ
```

**Theorem 2.1:** Valid BGP paths should be simple (no AS loops).

**Proof:**
AS loop indicates routing misconfiguration:
1. If AS appears twice, traffic may loop indefinitely
2. BGP loop detection removes paths with duplicate ASes
3. Valid paths in converged network are simple ∎

**Phronesis Implementation:**
```phronesis
POLICY reject_as_loops:
    Std.BGP.has_loop(route.as_path)
    THEN REJECT("AS path contains loop")
    PRIORITY: 200
```

### 2.2 Path Length

**Definition 2.2:**
```
length(P) = |P| - 1 = number of AS hops
```

**Theorem 2.2:** For simple paths, length ≤ |V| - 1.

**Proof:** A simple path visits each vertex at most once. ∎

### 2.3 Shortest Paths

**Definition 2.3 (Shortest AS Path):**
```
SP(u, v) = argmin_{P: u→v} length(P)
```

**Theorem 2.3:** BGP doesn't guarantee shortest paths.

**Proof:** BGP uses policy-based routing, not shortest path. AS relationships, local preferences, and other policies override path length. ∎

---

## 3. Valley-Free Routing

### 3.1 Gao-Rexford Model

**Definition 3.1 (Relationship Types):**
```
customer(u, v): u pays v for transit
provider(u, v): v pays u for transit (inverse of customer)
peer(u, v): u and v exchange traffic freely
```

### 3.2 Valley-Free Property

**Definition 3.2 (Valley-Free Path):**
A path P = (v₀, v₁, ..., vₖ) is valley-free if it follows the pattern:
```
customer* → peer? → provider*
```

Formally:
```
∃i, j. 0 ≤ i ≤ j ≤ k ∧
  (∀m < i. ℓ(vₘ, vₘ₊₁) = customer) ∧
  (i = j ∨ ℓ(vᵢ, vᵢ₊₁) = peer) ∧
  (∀m ≥ j. m < k → ℓ(vₘ, vₘ₊₁) = provider)
```

### 3.3 Valley-Free Theorem

**Theorem 3.1:** In a rational economy, all BGP paths are valley-free.

**Proof:**
1. Customers don't transit for non-customers (not paid)
2. Peers don't transit for other peers (no incentive)
3. Only valid patterns: customer→peer→provider

Violating path implies irrational economic behavior. ∎

**Phronesis Implementation:**
```phronesis
POLICY enforce_valley_free:
    NOT Std.BGP.is_valley_free(route.as_path)
    THEN REJECT("Non-valley-free path detected")
    PRIORITY: 150
```

---

## 4. RPKI and Graph Properties

### 4.1 ROA Graph

**Definition 4.1 (ROA Authorization Graph):**
```
R = (Prefixes, ASes, auth)

auth ⊆ Prefixes × ASes
(p, as) ∈ auth iff as is authorized to originate p
```

### 4.2 Prefix Hijack Detection

**Definition 4.2 (Prefix Hijack):**
```
Hijack(p, as) ⟺ announces(as, p) ∧ (p, as) ∉ auth
```

**Theorem 4.1:** RPKI-invalid origins indicate potential hijacks.

**Phronesis Implementation:**
```phronesis
POLICY reject_rpki_invalid:
    Std.RPKI.validate(route) == "invalid"
    THEN REJECT("RPKI validation failed")
    PRIORITY: 300
```

### 4.3 More Specific Hijack

**Definition 4.3:**
```
MoreSpecificHijack(p', as) ⟺
    ∃p ∈ Prefixes. p' ⊂ p ∧ announces(as, p') ∧ (p', as) ∉ auth
```

**Theorem 4.2:** More specific prefixes override less specific.

**Proof:** Longest prefix match routing ensures more specific routes are preferred. ∎

---

## 5. Connectivity Analysis

### 5.1 Graph Connectivity

**Definition 5.1:**
```
connected(G) ⟺ ∀u, v ∈ V. ∃ path from u to v
```

**Definition 5.2 (k-vertex-connected):**
```
k-connected(G) ⟺ |V| > k ∧ ∀S ⊆ V. |S| < k → connected(G - S)
```

### 5.2 AS Graph Connectivity

**Theorem 5.1:** The Internet AS graph is typically 3-connected.

**Proof Sketch:** Multiple Tier-1 providers ensure redundant connectivity. Removing up to 2 ASes doesn't disconnect the graph. ∎

### 5.3 Resilience Metrics

**Definition 5.3 (Vertex Connectivity):**
```
κ(G) = min |S| such that G - S is disconnected
```

**Definition 5.4 (Edge Connectivity):**
```
λ(G) = min |F| such that G - F is disconnected (F ⊆ E)
```

**Theorem 5.2 (Whitney):** κ(G) ≤ λ(G) ≤ δ(G)

Where δ(G) = minimum degree.

---

## 6. Centrality Measures

### 6.1 Degree Centrality

**Definition 6.1:**
```
C_D(v) = deg(v) / (|V| - 1)
```

**Interpretation:** ASes with high degree are major transit providers.

### 6.2 Betweenness Centrality

**Definition 6.2:**
```
C_B(v) = Σ_{s≠v≠t} (σ_st(v) / σ_st)

where:
  σ_st = number of shortest paths from s to t
  σ_st(v) = number of those paths passing through v
```

**Interpretation:** High betweenness = critical for routing.

### 6.3 Closeness Centrality

**Definition 6.3:**
```
C_C(v) = (|V| - 1) / Σ_{u≠v} d(v, u)
```

**Interpretation:** Low average distance to other ASes.

---

## 7. Clique and Community Detection

### 7.1 Peering Cliques

**Definition 7.1 (Clique):**
```
C ⊆ V is a clique iff ∀u, v ∈ C. (u, v) ∈ E
```

**Theorem 7.1:** Internet Exchange Points (IXPs) form cliques in the peer graph.

**Proof:** IXPs provide peering fabric where all participants can peer with all others. ∎

### 7.2 Customer Cones

**Definition 7.2 (Customer Cone):**
```
CustomerCone(as) = {as} ∪ {as' | ∃ customer path from as' to as}
```

**Theorem 7.2:** Customer cone size correlates with AS importance.

### 7.3 Community Structure

**Definition 7.3 (Modularity):**
```
Q = (1/2m) Σᵢⱼ [Aᵢⱼ - kᵢkⱼ/2m] δ(cᵢ, cⱼ)

where:
  m = |E|
  A = adjacency matrix
  kᵢ = degree of i
  cᵢ = community of i
```

High modularity indicates strong community structure.

---

## 8. Flow and Routing

### 8.1 Maximum Flow

**Definition 8.1:**
```
MaxFlow(s, t) = max Σ_{v:(s,v)∈E} f(s, v)

subject to:
  ∀(u,v) ∈ E: 0 ≤ f(u,v) ≤ c(u,v)  (capacity)
  ∀v ≠ s,t: Σ f(u,v) = Σ f(v,w)    (conservation)
```

### 8.2 Min-Cut Max-Flow

**Theorem 8.1 (Ford-Fulkerson):**
```
MaxFlow(s, t) = MinCut(s, t)
```

**Application:** Vulnerability of connectivity between ASes.

### 8.3 Multi-Commodity Flow

**Definition 8.2:**
Model multiple source-destination pairs simultaneously.

**Application:** Internet-wide traffic analysis.

---

## 9. Spanning Trees and Redundancy

### 9.1 Spanning Trees

**Definition 9.1:**
T ⊆ G is a spanning tree iff T is connected, acyclic, and covers all vertices.

### 9.2 BGP and Spanning Trees

**Theorem 9.1:** Converged BGP computes a spanning forest.

**Proof:**
1. Each destination prefix has exactly one best path from each AS
2. Collection of best paths forms tree rooted at origin
3. Union over all prefixes forms spanning forest ∎

### 9.3 Redundancy Measure

**Definition 9.2:**
```
Redundancy(G) = |E| - |V| + 1 = cyclomatic complexity
```

Higher redundancy = more alternate paths.

---

## 10. Path Algebra

### 10.1 Semiring Model

**Definition 10.1 (Routing Algebra):**
```
(W, ⊕, ⊗, 0̄, 1̄)

W = path weights
⊕ = path selection (min)
⊗ = path extension (composition)
0̄ = worst path (∞)
1̄ = best path (identity)
```

### 10.2 BGP Routing Algebra

**Definition 10.2:**
```
W = (LocalPref, ASPathLen, Origin, MED, ...)
⊕ = lexicographic comparison
⊗ = attribute update
```

### 10.3 Algebraic Properties

**Theorem 10.1:** BGP algebra is not a semiring (no distributivity).

**Proof:** MED comparison is not transitive across ASes:
```
AS1 prefers path P₁ over P₂
AS2 prefers path P₂ over P₃
AS3 may prefer P₃ over P₁ (non-transitive)
```
This breaks distributivity requirements. ∎

---

## 11. Graph Coloring

### 11.1 AS Relationship Coloring

**Definition 11.1:**
Color ASes by type:
```
Color = {Tier1, Tier2, Stub, IXP}
```

### 11.2 Chromatic Number

**Theorem 11.1:** The AS graph has χ(G) = 4.

**Proof:** Four tier levels suffice. Some AS pairs require different colors (provider/customer). ∎

### 11.3 Edge Coloring for Relationships

**Definition 11.2:**
```
EdgeColor : E → {customer, provider, peer}
χ'(G) = 3 (three relationship types)
```

---

## 12. Hypergraph Model

### 12.1 Prefix-AS Hypergraph

**Definition 12.1:**
```
H = (V, E_H)

V = ASes ∪ Prefixes
E_H = {e ⊆ V | e = {prefix, as₁, ..., asₖ} for some announcement}
```

Hyperedges represent prefix announcements with AS path.

### 12.2 Hypergraph Properties

**Theorem 12.1:** Each prefix hyperedge has unique origin but multiple paths.

---

## 13. Temporal Graph Dynamics

### 13.1 Time-Varying AS Graph

**Definition 13.1:**
```
G(t) = (V(t), E(t))

V(t) = ASes active at time t
E(t) = peerings active at time t
```

### 13.2 Route Stability

**Definition 13.2:**
```
Stability(p) = Pr[path to p unchanged over time window]
```

### 13.3 Convergence Time

**Theorem 13.1:** BGP converges in O(|V|) time in stable networks.

**Proof:** Each AS updates at most once per convergence cycle. With proper timers, updates propagate in O(diameter) rounds. ∎

---

## 14. Algorithms for Phronesis

### 14.1 Path Validation Algorithm

```
Algorithm ValidatePath(path):
  1. Check for loops: O(n) where n = |path|
  2. Check valley-free: O(n)
  3. Check AS existence: O(n) lookups
  4. Check RPKI: O(1) for origin

  Total: O(n)
```

### 14.2 Bogon Detection

```
Algorithm IsBogon(prefix):
  1. Check against RFC 1918: O(1)
  2. Check against reserved ranges: O(log m) for m ranges
  3. Return result

  Total: O(log m)
```

### 14.3 Shortest Path in AS Graph

```
Algorithm ShortestASPath(src, dst, G):
  Use BFS since edges are unweighted
  Time: O(|V| + |E|)
```

---

## 15. Phronesis Graph Operations

### 15.1 Std.BGP Module Graph Functions

```phronesis
# Path length
Std.BGP.path_length(route.as_path)  # Returns integer

# Origin AS
Std.BGP.get_origin(route)  # Returns last AS in path

# Path check
Std.BGP.has_loop(route.as_path)  # Returns boolean

# AS membership
Std.BGP.contains_as(route.as_path, 65000)  # Returns boolean
```

### 15.2 Graph-Based Policies

```phronesis
POLICY reject_long_paths:
    Std.BGP.path_length(route.as_path) > 10
    THEN REJECT("Path too long")
    PRIORITY: 50

POLICY require_direct_peer:
    NOT Std.BGP.is_direct_peer(route.as_path[1])
    THEN REJECT("Route not from direct peer")
    PRIORITY: 100
```

---

## 16. Summary

**Key Graph-Theoretic Properties for BGP:**

| Property | Definition | Phronesis Check |
|----------|------------|-----------------|
| Simple Path | No repeated vertices | `has_loop` |
| Valley-Free | customer*→peer?→provider* | `is_valley_free` |
| Connected | Path exists | Network property |
| RPKI Valid | (prefix, origin) ∈ auth | `Std.RPKI.validate` |
| Short Path | length ≤ threshold | `path_length` |

---

## References

1. Gao, L. (2001). *On Inferring Autonomous System Relationships in the Internet*.
2. Gill, P., Schapira, M., & Goldberg, S. (2013). *A Survey of Interdomain Routing Policies*.
3. Caesar, M., & Rexford, J. (2005). *BGP Routing Policies in ISP Networks*.
4. West, D. B. (2001). *Introduction to Graph Theory*. Prentice Hall.

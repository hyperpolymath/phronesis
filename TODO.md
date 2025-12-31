# SPDX-License-Identifier: Apache-2.0 OR MIT
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

# Phronesis TODO

## Cross-Repository Integration

### Echidna Integration

- [ ] Generate Echidna proof tasks from Phronesis property-based tests
- [ ] Export Coq/Lean4/Agda proofs from `academic/formal-verification/` for Echidna verification
- [ ] Add Alloy model extraction for bounded model checking (see echidna/TODO.md)
- [ ] Create formal specification test harness linking Phronesis runtime to Echidna provers

### Echidnabot CI/CD

- [ ] Configure echidnabot webhook for Phronesis repository
- [ ] Set up proof caching for consensus protocol properties
- [ ] Add formal verification step to PR merge requirements

---

## Code Quality

### Recently Fixed (2025-12-31)

- [x] **lib/phronesis/stdlib/rpki.ex** - Unsafe `String.split` patterns
  - Now uses `String.split(x, "/", parts: 2)` with `with` validation
  - Prevents crash on malformed CIDR prefixes like "10.0.0.0" (no slash)

- [x] **lib/phronesis/stdlib/consensus.ex** - Atom exhaustion vulnerability
  - `String.to_atom/1` on untrusted input could exhaust atom table
  - Now whitelists allowed option keys: `threshold`, `timeout`, `agents`, `use_raft`

- [x] **lib/phronesis/consensus/raft.ex** - Raft reply notification bug
  - Range `commit_index..last_applied` was backwards (empty when commit > applied)
  - Fixed to `(last_applied + 1)..commit_index`

### Outstanding Issues

- [ ] **O(n) list operations in hot paths** - Consider ETS tables or :array module
- [ ] **Missing rate limiting** - Add GenServer-level rate limiting for RPC handlers
- [ ] **Incomplete IPv6 support** - `ip_to_integer/1` only handles IPv4

---

## Academic Documentation

### Formal Verification Coverage

| Property | Coq | Lean4 | Agda | Alloy | TLA+ |
|----------|-----|-------|------|-------|------|
| Type Safety | ✓ | ✓ | ✓ | - | - |
| Termination | ✓ | ✓ | ✓ | - | - |
| Consensus Safety | - | - | - | Planned | ✓ |
| Authentication | - | - | - | - | ProVerif |

See `academic/theorem-index.md` for complete theorem cross-reference.

---

## Architecture Notes

### Language Stack

- **Elixir/OTP** - Core runtime, consensus, policy evaluation
- **BEAM VM** - Distribution, fault tolerance, hot code loading
- **Formal specs** - Coq, Lean 4, Agda for type theory proofs
- **Model checking** - TLA+ for temporal properties, planned Alloy integration

### Related Repositories

- **hyperpolymath/echidna** - Neurosymbolic theorem proving (12+ provers)
- **hyperpolymath/echidnabot** - Proof-aware CI bot (GitHub/GitLab/Bitbucket)

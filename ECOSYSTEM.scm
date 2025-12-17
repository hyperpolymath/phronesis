;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; ECOSYSTEM.scm — phronesis

(ecosystem
  (version "1.0.0")
  (name "phronesis")
  (type "language")
  (purpose "Consensus-gated policy language for network configuration")

  (position-in-ecosystem
    "Core language project in the hyperpolymath ecosystem. Follows RSR guidelines.")

  (related-projects
    (project (name "rhodium-standard-repositories")
             (url "https://github.com/hyperpolymath/rhodium-standard-repositories")
             (relationship "standard"))
    (project (name "maaf")
             (url "https://gitlab.com/hyperpolymath/maaf")
             (relationship "parent-organization")))

  (what-this-is
    "A consensus-gated policy language for network configuration with:
     - EBNF grammar specification
     - Formal operational semantics
     - Raft consensus for distributed execution
     - RPKI integration for route validation")
  (what-this-is-not
    "- NOT a general-purpose programming language
     - NOT exempt from RSR compliance
     - NOT a replacement for existing routing protocols"))

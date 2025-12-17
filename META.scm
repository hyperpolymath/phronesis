;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; META.scm — phronesis

(define-module (phronesis meta)
  #:export (architecture-decisions development-practices design-rationale))

(define architecture-decisions
  '((adr-001
     (title . "RSR Compliance")
     (status . "accepted")
     (date . "2025-12-15")
     (context . "Phronesis is a core project in the hyperpolymath ecosystem")
     (decision . "Follow Rhodium Standard Repository guidelines")
     (consequences . ("RSR Gold target" "SHA-pinned actions" "SPDX headers" "Multi-platform CI")))
    (adr-002
     (title . "Consensus Protocol")
     (status . "accepted")
     (date . "2025-12-15")
     (context . "Policy changes require distributed agreement")
     (decision . "Use Raft consensus for policy coordination")
     (consequences . ("Leader election" "Log replication" "Fault tolerance")))
    (adr-003
     (title . "Security Model")
     (status . "accepted")
     (date . "2025-12-17")
     (context . "Network policy changes are security-critical")
     (decision . "Capability-based module system with RPKI validation")
     (consequences . ("Module isolation" "RPKI integration" "Audit logging")))))

(define development-practices
  '((code-style
      (languages . ("elixir" "rust" "scheme"))
      (formatter . "mix format, cargo fmt")
      (linter . "mix credo, cargo clippy"))
    (security
      (sast . "CodeQL")
      (dependency-scanning . "Dependabot")
      (credentials . "env vars only")
      (signing . "GPG signed commits recommended"))
    (testing
      (coverage-minimum . 70)
      (frameworks . ("ExUnit" "cargo test")))
    (versioning (scheme . "SemVer 2.0.0"))))

(define design-rationale
  '((why-rsr "RSR ensures consistency, security, and maintainability.")
    (why-consensus "Network policies require agreement across multiple parties to prevent misconfigurations.")
    (why-formal-semantics "Formal operational semantics enable verification and predictable behavior.")
    (why-capability-based "Capability-based modules prevent unauthorized access to sensitive operations.")))
;; ============================================================================
;; CROSS-PLATFORM STATUS (Added 2025-12-17)
;; ============================================================================
;; This repo exists on multiple platforms. GitHub is the primary/source of truth.

(cross-platform-status
  (generated "2025-12-17")
  (primary-platform "github")
  (gitlab-mirror
    (path "hyperpolymath/maaf/4a-languages/phronesis")
    (url "https://gitlab.com/hyperpolymath/maaf/4a-languages/phronesis")
    (last-gitlab-activity "2025-11-13")
    (sync-status "gh-primary")
    (notes "GitHub newer. Safe to sync GH→GL."))
  
  (reconciliation-instructions
    ";; To fetch and compare GitLab content:"
    ";; git remote add gitlab https://gitlab.com/hyperpolymath/maaf/4a-languages/phronesis.git"
    ";; git fetch gitlab"
    ";; git log gitlab/main --oneline"
    ";; git diff main gitlab/main"
    ";;"
    ";; To merge if GitLab has unique content:"
    ";; git merge gitlab/main --allow-unrelated-histories"
    ";;"
    ";; After reconciliation, GitHub mirrors to GitLab automatically.")
  
  (action-required "gh-primary"))


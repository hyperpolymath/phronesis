;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; META.scm — template-repo

(define-module (template-repo meta)
  #:export (architecture-decisions development-practices design-rationale))

(define architecture-decisions
  '((adr-001
     (title . "RSR Compliance")
     (status . "accepted")
     (date . "2025-12-15")
     (context . "Project in the hyperpolymath ecosystem")
     (decision . "Follow Rhodium Standard Repository guidelines")
     (consequences . ("RSR Gold target" "SHA-pinned actions" "SPDX headers" "Multi-platform CI")))))

(define development-practices
  '((code-style (languages . ("unknown")) (formatter . "auto-detect") (linter . "auto-detect"))
    (security (sast . "CodeQL") (credentials . "env vars only"))
    (testing (coverage-minimum . 70))
    (versioning (scheme . "SemVer 2.0.0"))))

(define design-rationale
  '((why-rsr "RSR ensures consistency, security, and maintainability.")))
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


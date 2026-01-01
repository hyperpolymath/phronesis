;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2026 Hyperpolymath
;;
;; Playground Specification
;; Repository: hyperpolymath/oblibeny-playground
;; Purpose: Verification workflow contract, threat model, and demo corpus layout

(define spec-playground
  '((version . "1.0.0")
    (applies-to . "hyperpolymath/oblibeny-playground")

    ;;=========================================================================
    ;; VERIFICATION WORKFLOW CONTRACT
    ;;=========================================================================
    (verification-workflow
      . ((name . "Oblíbený Playground Verification")
         (description . "Demonstrates verifiable artifact creation and validation for security-critical embedded workflows")

         ;; Input specification
         (inputs
           . ((source-artifacts
                . ((type . "file")
                   (formats . ("*.obl" "*.constraints" "*.proof-stub"))
                   (location . "./examples/")
                   (validation . "SPDX header required, UTF-8 encoding")))
              (verification-config
                . ((type . "file")
                   (format . "verify.scm")
                   (location . "./config/")
                   (optional . #t)))))

         ;; Output specification
         (outputs
           . ((verification-report
                . ((type . "structured-output")
                   (format . "text/plain or application/json")
                   (contents . ("pass/fail status"
                               "artifact hash (SHA-256)"
                               "verification timestamp"
                               "error details if failed"))))
              (signed-artifact
                . ((type . "file")
                   (format . "*.verified")
                   (location . "./build/")
                   (optional . #t)))))

         ;; Workflow steps
         (steps
           . ((step-1-parse
                . ((name . "Parse Input")
                   (action . "Read and validate source artifact")
                   (failure-mode . "Reject with parse error")))
              (step-2-verify
                . ((name . "Run Verification")
                   (action . "Check constraints and proof obligations")
                   (failure-mode . "Report constraint violation")))
              (step-3-hash
                . ((name . "Generate Hash")
                   (action . "SHA-256 hash of verified artifact")
                   (failure-mode . "N/A - always succeeds if step-2 passes")))
              (step-4-report
                . ((name . "Emit Report")
                   (action . "Output verification result")
                   (failure-mode . "N/A - always succeeds")))))))

    ;;=========================================================================
    ;; THREAT MODEL POINTER
    ;;=========================================================================
    (threat-model
      . ((reference . "hyperpolymath/oblibeny:SECURITY.md")
         (scope . "playground-specific threats only")

         ;; Threats in scope for playground
         (in-scope-threats
           . ((t1-malformed-input
                . ((description . "Malformed or malicious input artifacts")
                   (mitigation . "Strict parsing with fail-fast behavior")
                   (test-coverage . "./corpus/invalid/")))
              (t2-hash-collision
                . ((description . "Preimage attacks on artifact hashes")
                   (mitigation . "SHA-256 only, no MD5/SHA1")
                   (test-coverage . "Hash algorithm verification in tests")))
              (t3-path-traversal
                . ((description . "File path manipulation in inputs")
                   (mitigation . "Sandbox to examples/ and build/ only")
                   (test-coverage . "./corpus/invalid/path-traversal.obl")))))

         ;; Threats deferred to upstream
         (deferred-threats
           . ("Compiler vulnerabilities (upstream oblibeny)"
              "Runtime memory safety (upstream oblibeny)"
              "Cryptographic primitive correctness (upstream oblibeny)"))))

    ;;=========================================================================
    ;; DEMO CORPUS LAYOUT
    ;;=========================================================================
    (demo-corpus
      . ((root . "./corpus/")
         (structure
           . ((valid-examples
                . ((path . "./corpus/valid/")
                   (purpose . "Examples that must pass verification")
                   (minimum-count . 2)
                   (files
                     . ("hello-world.obl        ;; Minimal valid program"
                        "simple-constraint.obl  ;; Basic constraint satisfaction"))))
              (invalid-examples
                . ((path . "./corpus/invalid/")
                   (purpose . "Examples that must fail with stable errors")
                   (minimum-count . 2)
                   (files
                     . ("missing-header.obl     ;; Fails: no SPDX header"
                        "bad-constraint.obl     ;; Fails: unsatisfiable constraint"
                        "path-traversal.obl     ;; Fails: forbidden path pattern"
                        "syntax-error.obl       ;; Fails: parse error"))))))

         ;; Error message stability contract
         (error-stability
           . ((policy . "Error messages must be stable across minor versions")
              (format . "ERROR [code]: description")
              (codes
                . ((E001 . "Parse error")
                   (E002 . "Missing SPDX header")
                   (E003 . "Constraint violation")
                   (E004 . "Path traversal attempt")
                   (E005 . "Hash verification failed")))))))

    ;;=========================================================================
    ;; COMPLIANCE REQUIREMENTS
    ;;=========================================================================
    (compliance
      . ((spdx . "All source files require SPDX-License-Identifier header")
         (offline . "All demos must work without network access")
         (reproducibility . "Same input must produce same output hash")
         (no-secrets . "No hardcoded credentials or API keys")))))

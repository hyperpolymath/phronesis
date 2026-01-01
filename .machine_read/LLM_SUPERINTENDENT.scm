;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2026 Hyperpolymath
;;
;; LLM Superintendent Instructions
;; Repository: hyperpolymath/oblibeny-playground
;; Purpose: Machine-readable governance for AI agents working in this repository

(define llm-superintendent
  '((version . "1.0.0")
    (applies-to . "hyperpolymath/oblibeny-playground")

    ;; Core identity enforcement
    (identity-constraints
      . ((must-preserve
           . ("Security-critical embedded systems focus"
              "Verifiable workflow demonstrations"
              "Downstream relationship to hyperpolymath/oblibeny"))
         (must-not-drift-to
           . ("General-purpose programming playground"
              "Privacy-preserving oblivious computation (unless upstream authorizes)"
              "Production compiler development"))))

    ;; Scope boundaries for AI agents
    (scope-boundaries
      . ((in-scope
           . ("Creating verification workflow examples"
              "Building demo artifacts that verify offline"
              "Writing documentation for playground usage"
              "Implementing test cases for invalid inputs"
              "Shell scripts using Just for automation"))
         (out-of-scope
           . ("Compiler modifications (upstream concern)"
              "Language semantics changes (upstream concern)"
              "Network-dependent demonstrations"
              "Pulling arbitrary external toolchains at runtime"))))

    ;; Quality gates for contributions
    (quality-gates
      . ((pre-commit
           . ("All demos must work offline"
              "Invalid test cases must produce stable error messages"
              "No hardcoded secrets or credentials"))
         (pre-merge
           . ("`just demo` passes"
              "`just test` passes"
              "SPDX headers present on all source files"))))

    ;; Communication protocol
    (communication
      . ((when-uncertain . "Defer to upstream hyperpolymath/oblibeny semantics")
         (when-scope-creep-detected . "Flag and refuse; suggest upstream issue instead")
         (when-security-concern . "Halt and require human review")))

    ;; RSR tier compliance
    (rsr-compliance
      . ((current-tier . "bronze")
         (bronze-requirements
           . ("Offline demos work"
              "At least 2 invalid test cases"
              "Basic SPDX compliance"))
         (silver-path
           . ("Pinned Guix channel for reproducible builds"
              "Verification harness with formal checks"
              "CI pipeline integration"))))))

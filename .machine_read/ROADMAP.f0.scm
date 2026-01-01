;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2026 Hyperpolymath
;;
;; Roadmap Phase 0 (Foundation)
;; Repository: hyperpolymath/oblibeny-playground
;; Purpose: Machine-readable first-phase milestones

(define roadmap-f0
  '((version . "f0")
    (phase-name . "Foundation")
    (applies-to . "hyperpolymath/oblibeny-playground")
    (rsr-target . "bronze")

    ;; Phase objectives
    (objectives
      . ((primary
           . ("Establish verifiable workflow demonstration"
              "Create minimal offline demo artifact"
              "Define example corpus with valid/invalid cases"))
         (secondary
           . ("Document playground usage patterns"
              "Prepare upgrade path to silver tier"))))

    ;; Concrete milestones
    (milestones
      . ((m1-scaffold
           . ((name . "Repository Scaffold")
              (status . "in-progress")
              (deliverables
                . (".machine_read/ directory with anchor schema"
                   "Justfile with list/demo/test targets"
                   "Basic README with honest guix story"))))

         (m2-demo-artifact
           . ((name . "Minimal Demo Artifact")
              (status . "pending")
              (deliverables
                . ("At least one verifiable artifact (proof stub, constraints file, or signed blob)"
                   "Verification script that checks artifact offline"
                   "Clear success/failure output"))))

         (m3-test-corpus
           . ((name . "Example Corpus")
              (status . "pending")
              (deliverables
                . ("At least 2 valid example inputs"
                   "At least 2 invalid example inputs"
                   "Stable error messages for invalid cases"
                   "Documentation of expected behavior"))))

         (m4-bronze-gate
           . ((name . "Bronze RSR Compliance")
              (status . "pending")
              (deliverables
                . ("SPDX headers on all source files"
                   "`just demo` passes consistently"
                   "`just test` validates corpus"
                   "No network dependencies in demo path"))))))

    ;; Dependencies
    (dependencies
      . ((upstream . "hyperpolymath/oblibeny")
         (tooling . ("just" "guile" "sha256sum"))
         (optional . ("guix" "nix"))))

    ;; Success criteria for phase completion
    (completion-criteria
      . ("All m1-m4 milestones delivered"
         "Bronze RSR tier achieved"
         "Upgrade path to silver documented"
         "No scope drift detected by superintendent"))))

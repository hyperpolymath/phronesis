;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2026 Hyperpolymath
;;
;; Anchor Schema: hyperpolymath.anchor/1
;; Repository: hyperpolymath/oblibeny-playground
;; Purpose: Machine-readable project identity and scope definition

(define anchor
  '((schema . "hyperpolymath.anchor/1")
    (repo . "hyperpolymath/oblibeny-playground")
    (date . "2026-01-01")
    (authority . "repo-superintendent")
    (purpose
      . ("Scope arrest: security-critical embedded language playground, focused on verifiable workflows."
         "Stop name/meaning drift: keep the 'secure embedded + verification' identity consistent with upstream Oblíbený."
         "Make one offline demo: build/verify a tiny artifact, even if stubbed."))

    (identity
      . ((project . "Oblíbený Playground")
         (kind . "playground")
         (one-sentence . "Playground for Oblíbený: security-critical embedded systems language.")
         (upstream . "hyperpolymath/oblibeny")))

    (semantic-anchor
      . ((policy . "downstream")
         (upstream-authority
           . ("Oblíbený semantics + verification story live upstream."
              "This repo demonstrates a verifiable workflow and examples only."))))

    (implementation-policy
      . ((allowed . ("Scheme" "Shell" "Just" "Markdown" "AsciiDoc"))
         (quarantined . ("Any production compiler work (belongs upstream)"))
         (forbidden
           . ("Reframing as 'privacy-preserving oblivious computation' unless upstream explicitly says so"
              "Network-required demo"
              "Unsafe build scripts that pull arbitrary toolchains at runtime"))))

    (golden-path
      . ((smoke-test-command
           . ("just --list"
              "just demo"
              "just test"))
         (success-criteria
           . ("`just demo` verifies something concrete: e.g., checks a proof stub, checks a constraints file, or validates a signed artifact."
              "There is a tiny example corpus; at least 2 invalid cases fail with stable errors."))))

    (mandatory-files
      . ("./.machine_read/LLM_SUPERINTENDENT.scm"
         "./.machine_read/ROADMAP.f0.scm"
         "./.machine_read/SPEC.playground.scm"))

    (first-pass-directives
      . ("Define SPEC.playground.scm: verification workflow contract (inputs/outputs), threat model pointer, and demo corpus layout."
         "Make the README's 'guix install' story either real (pinned channel) or explicitly illustrative; never pretend it works."))

    (rsr . ((target-tier . "bronze-now")
            (upgrade-path . "silver-after-f1 (pinned toolchain + verification harness + CI)")))))

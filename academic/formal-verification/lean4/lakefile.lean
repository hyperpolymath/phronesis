-- SPDX-License-Identifier: MPL-2.0
-- SPDX-License-Identifier: MPL-2.0
-- Minimal Lake build for the Phronesis Lean 4 metatheory.
-- No external dependencies (no Mathlib): builds on core Lean only, so CI
-- needs nothing but the toolchain pinned in `lean-toolchain`.
import Lake
open Lake DSL

package phronesis where

@[default_target]
lean_lib Phronesis where

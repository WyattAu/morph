/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.DialectProjection.Spec

/-!
# DialectProjection: consolidated with the validated translation

Research loop 17. Target: `Morph/Specs/DialectProjection/`.

**What was there.** Thirteen theorems, all `rfl` facts about `List.length`,
`List.append` and `Option` — nothing about dialect projection. The module's real
content was delivered separately, in `Morph/Specs/DialectSemantics/` (research
loop 7), which gives dialect translation a *validated* semantics: every accepted
translation preserves the denotation, and what the target may not perform is
refused.

**This file records the difference.** The old pass-through `lower` accepts a
translation into a dialect that may not perform the operation; the validated
translation in `Morph/Specs/DialectSemantics/` (research loop 7) refuses it.
The two operate on different term languages — `lower` on the list-shaped
`DialectExpr`, the validated one on the binary core — so the comparison is
recorded here as a finding about `lower` rather than as an equation between
them.
-/

namespace Morph.Specs.DialectProjection

/-- **The old pass-through retags without checking.** `lower` into `core` turns a
program that performs `raw-ptr` into a program *in `core`* that performs
`raw-ptr` — a dialect that does not permit it. The old module had no notion of
this; its `isValid` predicate was a hard-coded table of dialect pairs. -/
theorem lower_accepts_what_core_forbids :
    lower { source := .«unsafe», target := .core, name := "p" }
      (.op "raw-ptr" [.val ⟨.«unsafe», 0⟩])
      = .op "raw-ptr" [.val ⟨.core, 0⟩] := by simp [lower]

/-! ## Depth re-audit (loop 91): capability, validity, and lowering facts -/

/-- `core` permits no side effects. -/
theorem core_no_side_effects :
    (dialectCapabilities .core).supportsSideEffects = false := rfl

/-- `core` permits no unsafe operations. -/
theorem core_no_unsafe_ops :
    (dialectCapabilities .core).supportsUnsafeOps = false := rfl

/-- `core` is higher-order (the pipeline lowers, it does not first-order). -/
theorem core_higher_order :
    (dialectCapabilities .core).supportsHigherOrder = true := rfl

/-- `unsafe` adds side effects, unsafe ops, and mutation to `core`. -/
theorem unsafe_extends_core : unsafeCapabilities = { coreCapabilities with supportsSideEffects := true, supportsUnsafeOps := true, supportsMutation := true } := rfl

/-- `ffi` adds foreign calls and side effects to `core`. -/
theorem ffi_extends_core : ffiCapabilities = { coreCapabilities with supportsForeignCalls := true, supportsSideEffects := true } := rfl

/-- The hard-coded validity table, positive cases. -/
theorem isValid_core_unsafe :
    Projection.isValid { source := .core, target := .«unsafe», name := "p" } := by
  trivial

theorem isValid_core_ffi :
    Projection.isValid { source := .core, target := .ffi, name := "p" } := by
  trivial

theorem isValid_unsafe_ffi :
    Projection.isValid { source := .«unsafe», target := .ffi, name := "p" } := by
  trivial

/-- Self-projection is never in the table (the table lists strict lowerings). -/
theorem isValid_core_core_false :
    ¬ Projection.isValid { source := .core, target := .core, name := "p" } := by
  simp [Projection.isValid]

/-- `equiv` ignores the name metadata. -/
theorem equiv_name_irrelevant (s t : Dialect) :
    Projection.equiv { source := s, target := t, name := "a" }
      { source := s, target := t, name := "b" } := by
  simp [Projection.equiv]

/-- `equiv` is reflexive. -/
theorem equiv_refl (p : Projection) : Projection.equiv p p := by
  simp [Projection.equiv]

/-- `equiv` is symmetric. -/
theorem equiv_symm {p1 p2 : Projection} (h : Projection.equiv p1 p2) :
    Projection.equiv p2 p1 := by
  simp only [Projection.equiv] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

/-- `equiv` is transitive. -/
theorem equiv_trans {p1 p2 p3 : Projection} (h1 : Projection.equiv p1 p2)
    (h2 : Projection.equiv p2 p3) : Projection.equiv p1 p3 := by
  simp only [Projection.equiv] at h1 h2 ⊢
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- Lowering lands every value in the target dialect. The nested induction
mirrors `lower_identity` in the spec file. -/
theorem lower_into_target (p : Projection) (e : DialectExpr) :
    allInDialect (lower p e) p.target := by
  exact DialectExpr.rec
    (motive_1 := fun e => allInDialect (lower p e) p.target)
    (motive_2 := fun l => ∀ e ∈ l, allInDialect (lower p e) p.target)
    (val := fun v => by simp [lower, allInDialect])
    (op := fun name args ih => by
      simp only [lower, allInDialect]
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      exact ih a' ha')
    (call := fun name args ih => by
      simp only [lower, allInDialect]
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      exact ih a' ha')
    (block := fun exprs ih => by
      simp only [lower, allInDialect]
      intro e he
      simp only [List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      exact ih e' he')
    (nil := fun e he => by simp at he)
    (cons := fun head tail ih_head ih_tail e he => by
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ih_head
      · exact ih_tail e he)
    e

end Morph.Specs.DialectProjection

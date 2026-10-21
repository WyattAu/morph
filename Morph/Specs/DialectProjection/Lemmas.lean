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

end Morph.Specs.DialectProjection

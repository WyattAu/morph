/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.DialectSemantics.Lemmas

/-!
# Worked examples: translation validation, discharged

Each example *computes* the validation obligation for a concrete program: the
source denotes a value, the accepted translation denotes the same value, and the
refused translation does not exist.
-/

namespace Morph.Specs.DialectSemantics

open Morph.Specs.DialectProjection

/-- `1 + 2 * 3` written in the `core` dialect. -/
def coreArith : Term := .add (.val 1 .core) (.mul (.val 2 .core) (.val 3 .core))

/-- The same program in the `unsafe` dialect: the leaves are retagged. -/
def unsafeArith : Term := .add (.val 1 .«unsafe») (.mul (.val 2 .«unsafe») (.val 3 .«unsafe»))

/-- A program using a raw pointer, written in `unsafe`. -/
def unsafePtr : Term := .rawptr (.val 0 .«unsafe»)

example : eval .core coreArith = some 7 := rfl

example : eval .core unsafeArith = some 7 := rfl

/-- Translation into `unsafe` accepts and retags. -/
example : translate .«unsafe» coreArith = some unsafeArith := rfl

/-- **The validation obligation, discharged for this program:** source and
accepted target denote the same value. -/
example : eval .«unsafe» coreArith = eval .«unsafe» unsafeArith :=
  translate_preserves_eval rfl

/-- An accepted translation is entirely in the target dialect. -/
example : dialectOf unsafeArith = .«unsafe» := rfl

/-- A raw pointer denotes nothing in the core semantics: machine state is not
modelled. -/
example : eval .core unsafePtr = none := rfl

/-- **Refused.** It cannot be translated into `core` at all. -/
example : translate .core unsafePtr = none := translate_core_refuses_rawptr

/-- Accepted into `unsafe`, where it is permitted. -/
example : translate .«unsafe» unsafePtr = some unsafePtr := rfl

/-- **Retagging is invisible to the denotation.** A value's dialect tag does not
affect what it denotes, which is exactly why retagging is safe. -/
example : eval .core (.val 7 .«unsafe») = eval .core (.val 7 .ffi) := rfl

/-- **Refusal is total, not heuristic:** `core` rejects precisely the unsafe
terms, and accepts precisely the safe ones. -/
example : ¬ safe unsafePtr := by simp [safe, unsafePtr]

example : safe coreArith := by simp [safe, coreArith]

example : ¬ (∃ e', translate .core unsafePtr = some e') := by
  rintro ⟨e', he'⟩
  have := translate_core_refuses_rawptr
  rw [show unsafePtr = .rawptr (.val 0 .«unsafe») from rfl, this] at he'
  cases he'

/-- The old pass-through produced exactly the accepted-but-illegal term that
`translate` refuses. -/
example :
    lower { source := .«unsafe», target := .core, name := "bad" }
      (.op "raw-ptr" [.val ⟨.«unsafe», 0⟩])
      = .op "raw-ptr" [.val ⟨.core, 0⟩] := by simp [lower]

end Morph.Specs.DialectSemantics

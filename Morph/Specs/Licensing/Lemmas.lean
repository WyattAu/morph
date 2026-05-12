/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.Licensing

inductive License where
  | apache2 : License
  | mit : License
  | gpl3 : License
  | bsd3 : License
  | none : License
  deriving Repr, BEq, DecidableEq

def License.id : License → String
  | .apache2 => "Apache-2.0"
  | .mit => "MIT"
  | .gpl3 => "GPL-3.0"
  | .bsd3 => "BSD-3-Clause"
  | .none => "NONE"

theorem License.apache2_id : License.apache2.id = "Apache-2.0" := rfl

theorem License.mit_id : License.mit.id = "MIT" := rfl

theorem License.id_length_pos (l : License) : l.id.length > 0 := by
  cases l <;> simp [License.id] <;> decide

theorem apache2_ne_mit : License.apache2 ≠ License.mit := by decide

theorem apache2_ne_gpl3 : License.apache2 ≠ License.gpl3 := by decide

theorem mit_ne_gpl3 : License.mit ≠ License.gpl3 := by decide

def licenseIsOsiApproved : License → Bool
  | .apache2 => true
  | .mit => true
  | .gpl3 => true
  | .bsd3 => true
  | .none => false

theorem apache2_osi : licenseIsOsiApproved License.apache2 = true := rfl

theorem none_not_osi : licenseIsOsiApproved License.none = false := rfl

end Morph.Specs.Licensing

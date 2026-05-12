/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ArcAffineIntegration.Spec

namespace Morph.Specs.ArcAffineIntegration

open Morph.Specs.CommonTypes

/-!
## Examples

Concrete examples demonstrating the ArcAffineIntegration specification.
-/

def obj0 : ObjectId := { id := 0 }

def obj1 : ObjectId := { id := 1 }

example : transition Capability.iso Capability.val = true := rfl

example : transition Capability.val Capability.ref = true := rfl

example : transition Capability.ref Capability.weak = true := rfl

example : transition Capability.iso Capability.weak = false := rfl

example : transition Capability.weak Capability.iso = false := rfl

example : isIso Capability.iso := rfl

example : ¬isIso Capability.val := by simp [isIso]

example : strongReferences obj0 defaultReferenceGraph = [] := by
  unfold strongReferences defaultReferenceGraph; simp

end Morph.Specs.ArcAffineIntegration

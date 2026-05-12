/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AbiDataRefinement.Spec

namespace Morph.Specs.AbiDataRefinement

/-!
## Examples

Concrete examples demonstrating the AbiDataRefinement specification.
-/

def int32Type : AbiType := { name := "int32", size := 4, align := 4 }

def float64Type : AbiType := { name := "float64", size := 8, align := 8 }

def validLayout : MemoryLayout := {
  abiType := int32Type,
  size := 4,
  align := 4,
  offsets := [4]
}

def emptyOffsetsLayout : MemoryLayout := {
  abiType := int32Type,
  size := 4,
  align := 4,
  offsets := []
}

example : int32Type.size = 4 := rfl

example : int32Type.align = 4 := rfl

example : float64Type.size = 8 := rfl

example : emptyOffsetsLayout.offsets = [] := rfl

end Morph.Specs.AbiDataRefinement

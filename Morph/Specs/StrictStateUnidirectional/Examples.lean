/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.StrictStateUnidirectional

/-!
## Examples

Concrete examples for the StrictStateUnidirectional specification.
-/

example : !!true = true := by simp

example : !!false = false := by simp

example : true && true = true := rfl

example : true && false = false := rfl

example : false || true = true := rfl

example : false || false = false := rfl

end Morph.Specs.StrictStateUnidirectional

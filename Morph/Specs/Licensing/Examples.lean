/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.Licensing

/-!
## Examples

Concrete examples for the Licensing specification.
-/

def apache2 : String := "Apache-2.0"

def mit : String := "MIT"

def gpl3 : String := "GPL-3.0"

example : apache2.length > 0 := by decide

example : mit ≠ gpl3 := by decide

example : (["Apache-2.0", "MIT"] : List String).length = 2 := rfl

example : "Apache-2.0" ∈ (["Apache-2.0", "MIT"] : List String) := by simp

end Morph.Specs.Licensing

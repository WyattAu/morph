/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.Maths.Spec

namespace Morph.Specs.Maths

/-!
## Examples

Concrete examples for the Maths specification.
-/

example : 5 + 0 = 5 := rfl

example : 0 + 5 = 5 := rfl

example : 2 + 3 = 5 := rfl

example : 3 + 2 = 5 := rfl

example : (1 : Nat) + 1 = 2 := rfl

example : 10 + 20 + 30 = 60 := rfl

/-- `gcd` is total (well-founded on its second argument); these are its
Euclidean values. -/
example : gcd 12 18 = 6 := by native_decide

example : gcd 0 5 = 5 := by native_decide

example : gcd 17 5 = 1 := by native_decide

example : coprime 9 28 = true := by native_decide

example : coprime 9 27 = false := by native_decide

end Morph.Specs.Maths

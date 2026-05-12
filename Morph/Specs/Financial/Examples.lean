/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.Financial

/-!
## Examples

Concrete examples for the Financial specification.
-/

example : 100 + 200 = 300 := rfl

example : 3 * 50 = 150 := rfl

example : 1000 - 250 = 750 := rfl

example : 100 * 0 = 0 := rfl

example : 0 * 999 = 0 := rfl

example : 100 - 100 = 0 := rfl

end Morph.Specs.Financial

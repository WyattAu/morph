/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.ExecutionModel

/-!
## Examples

Concrete examples for the ExecutionModel specification.
-/

example : 2 + 3 = 5 := rfl

example : 2 * 3 = 6 := rfl

example : (2 + 3) * 4 = 20 := rfl

example : 10 - 3 = 7 := rfl

example : 10 / 3 = 3 := rfl

example : 10 % 3 = 1 := rfl

end Morph.Specs.ExecutionModel

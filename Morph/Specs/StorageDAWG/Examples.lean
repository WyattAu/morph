/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.StorageDAWG

/-!
## Examples

Concrete examples for the StorageDAWG specification.
-/

example : "".length = 0 := rfl

example : "abc".length = 3 := by decide

example : "hello" ++ "world" = "helloworld" := rfl

example : "abc" = "abc" := rfl

example : "abc" ≠ "abd" := by decide

end Morph.Specs.StorageDAWG

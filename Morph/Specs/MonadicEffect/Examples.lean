/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.MonadicEffect

/-!
## Examples

Concrete examples for the MonadicEffect specification.
-/

example : Option.bind (some 3) (fun n => some (n + 1)) = some 4 := rfl

example : Option.bind (none : Option Nat) (fun n => some (n + 1)) = none := rfl

example : (some 1).bind (fun n => some (n * 2)) = some 2 := rfl

end Morph.Specs.MonadicEffect

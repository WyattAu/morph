/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.OperatorNullCoalescing

/-!
## Examples

Concrete examples for the OperatorNullCoalescing specification.
-/

example : (some 42).getD 0 = 42 := rfl

example : (none : Option Nat).getD 0 = 0 := rfl

example : (some "hello").getD "default" = "hello" := rfl

example : (none : Option String).getD "default" = "default" := rfl

example : (some 1).orElse (fun () => some 2) = some 1 := rfl

example : (none : Option Nat).orElse (fun () => some 2) = some 2 := rfl

end Morph.Specs.OperatorNullCoalescing

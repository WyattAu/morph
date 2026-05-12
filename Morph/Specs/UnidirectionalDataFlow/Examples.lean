/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.UnidirectionalDataFlow.Spec

namespace Morph.Specs.UnidirectionalDataFlow

/-!
## Examples

Concrete examples for the Unidirectional Data Flow specification.
-/

example : ([] : List Nat).reverse = [] := rfl

example : ([1, 2, 3] : List Nat).reverse = [3, 2, 1] := rfl

example : ([1, 2, 3] : List Nat).reverse.reverse = [1, 2, 3] := rfl

example : ([1, 2, 3] : List Nat).reverse.length = 3 := rfl

end Morph.Specs.UnidirectionalDataFlow

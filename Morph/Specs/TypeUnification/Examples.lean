/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.TypeUnification.Lemmas

/-! Pins for the unification core (loop 101). -/

namespace Morph.Specs.TypeUnification

/-- Identical variables unify with the identity substitution. -/
example : unifyF 5 (.v 0) (.v 0) = some Subst.id := rfl

/-- Distinct variables unify by binding the left one. -/
example : unifyF 5 (.v 0) (.v 1) = some (update Subst.id 0 (.v 1)) := rfl

/-- Base types unify exactly. -/
example : unifyF 5 (.c "i32") (.c "i32") = some Subst.id := rfl
example : unifyF 5 (.c "i32") (.c "u8") = none := rfl

/-- The occurs check: `v 0` occurs in `arrow (v 0) (c "x")`, so the
unification `v 0 ≐ arrow (v 0) (c "x")` fails — no substitution can make a
variable equal a term containing it (Robinson 1965). -/
example : occurs 0 (.arrow (.v 0) (.c "x")) = true := rfl
example : unifyF 5 (.v 0) (.arrow (.v 0) (.c "x")) = none := rfl

/-- Arrows unify pointwise: `v 0 → c "u8" ≐ c "i32" → c "u8"` binds `v 0 ↦ c "i32"`. -/
example : unifyF 5 (.arrow (.v 0) (.c "u8")) (.arrow (.c "i32") (.c "u8")) =
    some (comp Subst.id (update Subst.id 0 (.c "i32"))) := rfl

/-- Occurs-check soundness, computed: substituting `c "i32"` for `v 1` in
`arrow (v 1) (c "u8")` changes nothing outside `v 1`. -/
example : apply (update Subst.id 1 (.c "i32")) (.arrow (.v 1) (.c "u8")) =
    .arrow (.c "i32") (.c "u8") := rfl

end Morph.Specs.TypeUnification

/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MonadicEffect.Spec
import Morph.Specs.EffectAlgebra.Spec

/-!
# MonadicEffect: consolidated with the effect algebra

Research loop 17. Target: `Morph/Specs/MonadicEffect/`.

**What was there.** Two theorems, both `rfl` facts about `Option.bind` — nothing
about effects. The module's real content was delivered separately, in
`Morph/Specs/EffectAlgebra/` (research loop 6), which gives Morph's effect set
`{IO, Net, Time, System}` an algebraic-theory semantics: the free-model monad,
and a homomorphism property.

**This file records why the old module could not.** Its `effectNames` is
documented as "shallow, one level" and traverses no continuation — so it
reports **none** of the effects a real computation performs. That is not a
missing theorem; it is a missing traversal.
-/

namespace Morph.Specs.MonadicEffect

open Morph.Specs.EffectAlgebra

/-- **The old effect collection was shallow.** `effectNames` on a `seq` reports
only the effects of the *first* computation: everything under the continuation
is invisible. A computation that performs effects only in its continuation
therefore reports none. -/
theorem effectNames_ignores_the_continuation :
    EffectfulComputation.effectNames
      (.seq (.pure "x") (fun _ => .perform (.read "secret"))) = [] := rfl

/-- **The new effect algebra is complete.** The effect classes of a computation
include the ones performed under its continuation — the property the old
collection could not even state. -/
theorem effect_algebra_traverses_continuations :
    (Eff.classes
      (.op (.read "secret") (fun _ => .op (.now "utc") (fun _ => .pure "x"))))
      = [.io, .time] := rfl

end Morph.Specs.MonadicEffect

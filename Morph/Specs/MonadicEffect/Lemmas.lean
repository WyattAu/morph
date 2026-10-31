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

/-! ## Depth re-audit (loop 91): the spec definitions' own facts -/

/-- `effectName` projects each operation's name. -/
theorem effectName_read (n : String) : (EffectOp.read n).effectName = n := rfl

theorem effectName_write (n v : String) : (EffectOp.write n v).effectName = n := rfl

theorem effectName_ask (n : String) : (EffectOp.ask n).effectName = n := rfl

theorem effectName_raise (n : String) : (EffectOp.raise n).effectName = n := rfl

/-- A handler handles what it lists. -/
theorem canHandle_listed :
    Handler.canHandle ⟨"h", ["fs", "net"]⟩ (.read "fs") = true := rfl

/-- A handler refuses what it does not list. -/
theorem canHandle_unlisted :
    Handler.canHandle ⟨"h", ["fs"]⟩ (.raise "boom") = false := rfl

/-- Shallow collection: `pure` and `fail` report nothing. -/
theorem effectNames_pure (v : String) :
    EffectfulComputation.effectNames (.pure v) = [] := rfl

theorem effectNames_fail (m : String) :
    EffectfulComputation.effectNames (.fail m) = [] := rfl

/-- Shallow collection: `perform` reports exactly its operation's name. -/
theorem effectNames_perform (op : EffectOp) :
    EffectfulComputation.effectNames (.perform op) = [op.effectName] := rfl

/-- `contains` is list membership. -/
theorem contains_hit : EffectSet.contains ["a", "b"] "b" = true := rfl

theorem contains_miss : EffectSet.contains ["a", "b"] "z" = false := rfl

/-- The empty stack handles nothing. -/
theorem findHandler_empty (op : EffectOp) :
    HandlerStack.findHandler [] op = none := rfl

/-- Pushing a capable handler makes it the one found. -/
theorem findHandler_push_hit :
    HandlerStack.findHandler [⟨"h", ["fs"]⟩] (.read "fs") =
      some ⟨"h", ["fs"]⟩ := rfl

/-- An incapable top handler is skipped for the one below. -/
theorem findHandler_skips_top :
    HandlerStack.findHandler [⟨"top", []⟩, ⟨"low", ["fs"]⟩] (.read "fs") =
      some ⟨"low", ["fs"]⟩ := rfl

/-- No capable handler means `none`. -/
theorem findHandler_miss :
    HandlerStack.findHandler [⟨"h", ["other"]⟩] (.read "fs") = none := rfl

end Morph.Specs.MonadicEffect

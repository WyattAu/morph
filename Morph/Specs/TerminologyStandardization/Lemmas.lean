/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TerminologyStandardization.Spec

namespace Morph.Specs.TerminologyStandardization

/-!
# TerminologyStandardization: five claims, and three refutations

Research loop 30. Target: `Morph/Specs/TerminologyStandardization/`.

**What was there.** Five `Prop := True` claims, and `spec_pure_function`
conjoined three bare `True`s. The naming claims (`spec_type_naming`,
`spec_function_naming`, `spec_variable_naming`) were real propositions but
**false**: `isTypeName`/`isFunctionName`/`isVariableName` only ask for an
uppercase letter, which neither forces Pascal case nor camel case.

**What is here.**
* `spec_signal_vs_stream` — sampling a signal at rate `r` yields `r` events.
* `spec_reducer_vs_transducer` — transducer composition is associative.
* `noSideEffects`, `noMutation`, `isDeterministicFn` — all three are
  referential transparency (`x₁ = x₂ → f x₁ = f x₂`), proved universally.
* `spec_pure_function` — the real conjunction of the four, proved.
* `spec_type_naming_false`, `spec_function_naming_false`,
  `spec_variable_naming_false` — witnesses (`"aB"`, `"A"`) refuting the three
  naming implications as stated. The predicates would need a first-letter
  constraint to be true; that is a spec repair, not a proof obligation.
-/

/-! ### Canonical Mapping -/

theorem canonicalMapping_id (t : Term) : canonicalMapping t = t := rfl

theorem isDeprecated_canonical (t : Term) : canonicalMapping t = t → ¬isDeprecated t := by
  unfold isDeprecated; simp

/-! ### Naming Conventions -/

theorem isPascalCase_empty : ¬isPascalCase "" := by
  unfold isPascalCase; simp

theorem isCamelCase_empty : ¬isCamelCase "" := by
  unfold isCamelCase; simp

theorem isSnakeCase_empty : isSnakeCase "" = true := by
  unfold isSnakeCase; simp

/-! ### Referential Transparency -/

theorem referentialTransparency_id {A B : Type} (f : PureFunction A B) (x : A) :
  f.apply x = f.apply x := rfl

theorem referentialTransparency_eq {A B : Type} (f : PureFunction A B) (x y : A)
    (h : x = y) : f.apply x = f.apply y := by
  subst h; rfl

/-! ### Consistency Invariant -/

theorem consistencyInvariant_empty :
    consistencyInvariant ([] : List Term) := by
  unfold consistencyInvariant; simp

/-! ### The formerly-vacuous claims, proved -/

theorem spec_signal_vs_stream_holds : spec_signal_vs_stream := by
  intro T signal rate
  unfold signalToStream
  simp

theorem spec_reducer_vs_transducer_holds : spec_reducer_vs_transducer := by
  intro G t1 t2 t3 g
  rfl

theorem noSideEffects_holds {A B : Type} (f : PureFunction A B) :
    noSideEffects f := by
  intro x1 x2 h
  rw [h]

theorem noMutation_holds {A B : Type} (f : PureFunction A B) :
    noMutation f := by
  intro x1 x2 h
  rw [h]

theorem isDeterministicFn_holds {A B : Type} (f : PureFunction A B) :
    isDeterministicFn f := by
  intro x1 x2 h
  rw [h]

theorem spec_pure_function_holds {A B : Type} (f : PureFunction A B) :
    spec_pure_function f := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro x1 x2 h; rw [h])

/-! ### The naming claims are false as stated -/

/-- `isTypeName` only asks for some uppercase letter, so `"aB"` is a type name
but is not Pascal case. The implication in `spec_type_naming` is therefore
false. -/
theorem spec_type_naming_false : ¬ spec_type_naming := by
  intro h
  exact (by decide : ¬ isPascalCase "aB") (h "aB" (by decide))

/-- Baseline `"A"` satisfies `isFunctionName` but is not camel case. -/
theorem spec_function_naming_false : ¬ spec_function_naming := by
  intro h
  exact (by decide : ¬ isCamelCase "A") (h "A" (by decide))

/-- Baseline `"A"` satisfies `isVariableName` but is not camel case. -/
theorem spec_variable_naming_false : ¬ spec_variable_naming := by
  intro h
  exact (by decide : ¬ isCamelCase "A") (h "A" (by decide))

end Morph.Specs.TerminologyStandardization

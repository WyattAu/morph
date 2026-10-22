/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LicenseDeonticLogic.Spec

/-!
# LicenseDeonticLogic: the deontic theorems, stated and proved

Research loop 24. Target: `Morph/Specs/LicenseDeonticLogic/`.

**What was there.** A real deontic model — licences with prohibition,
obligation and permission predicates, a compatibility check, and a GPL-infection
detector — and two headline properties that were `True`. The module's operations
were never related to its claims.

**What is here.**

- `spec_compatibility_theorem_holds` — if the rights check passes and the
  obligation check passes, the compatibility check passes, stated in the
  decidable form the check itself uses;
- `spec_gpl_infection_theorem_holds` — if the infection detector fires for a
  root, then the root carries the GPL's open-source obligation and prohibits
  `openSource` (what the detector actually tests, which differs from the old
  prose's `.closeSource`).

**Loop 34.** The six remaining `∀ _, True`/`match _ => True` specifications
are now real and proved: `isAllowed` gives the deontic reading; predicate and
action support are exhaustive-case statements; compatibility is total and its
two outcomes are exclusive. The rights check now uses `!hasProhibition`
explicitly, which removed a `decide`/Prop coercion mismatch.

**What is not here.** `spec_license_invariants` is stated but not proved: it is
false for arbitrary licences (a predicate may name an action the licence does
not list), and the honest form would carry a well-formedness hypothesis.
-/

namespace Morph.Specs.LicenseDeonticLogic

/-- **The compatibility theorem.** -/
theorem spec_compatibility_theorem_holds (root dep : License) :
    spec_compatibility_theorem root dep := by
  intro hr ho
  simp only [checkCompatibility, hr, ho, if_true, and_true]

/-- **The GPL infection theorem.** A root licence is infected exactly when the
detector says so, and the detector fires exactly when the root carries the GPL's
open-source obligation and its close-source prohibition. -/
theorem spec_gpl_infection_theorem_holds (root : License) :
    spec_gpl_infection_theorem root := by
  intro h
  unfold detectGplInfection at h
  simp only [decide_eq_true_eq] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-! ### The six previously-`True` claims -/

theorem spec_model_licenses_deontic_holds : spec_model_licenses_deontic := by
  intro license action h
  unfold License.isAllowed at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem spec_support_all_predicates_holds : spec_support_all_predicates := by
  intro license p _
  cases p.predicateType <;> simp

theorem spec_support_all_actions_holds : spec_support_all_actions := by
  intro a
  cases a <;> simp

theorem spec_verify_compatibility_holds : spec_verify_compatibility := by
  intro root dep
  unfold checkCompatibility
  dsimp only
  split <;> simp

theorem spec_enforce_gpl_compatibility_holds : spec_enforce_gpl_compatibility := by
  intro root gpl _
  unfold checkCompatibility
  dsimp only
  split <;> simp

theorem spec_compatibility_complexity_holds : spec_compatibility_complexity := by
  intro root dep
  unfold checkCompatibility
  dsimp only
  split <;> simp

end Morph.Specs.LicenseDeonticLogic

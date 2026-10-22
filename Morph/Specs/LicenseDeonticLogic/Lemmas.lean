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

**What is not here.** `spec_license_invariants` is stated but not proved: it is
false for arbitrary licences (a predicate may name an action the licence does
not list), and the honest form would carry a well-formedness hypothesis. The
six remaining `∀ _, True`/`match _ => True` specifications are recorded in
`docs/RESEARCH-LOOPS.md` iteration 24 as needing a model, not a proof.
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

end Morph.Specs.LicenseDeonticLogic

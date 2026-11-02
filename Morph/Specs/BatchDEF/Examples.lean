/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchDEF.Lemmas

/-!
# Frontier Kernels — examples (E-38–E-47)

Status: first cycle complete (loop 107).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchDEF

/-! ## E-38: feasible routes and obstruction certificates -/

/-- Both loads fit their caps. -/
example : loadsOK [3, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] = true := by decide

/-- The first load breaks its cap. -/
example : loadsOK [7, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] = false := by decide

/-- The conflict is named. -/
example : firstBad [7, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] = some (7, ⟨"a", 4⟩) :=
  by decide

/-- A clean instance solves feasible. -/
example : solve [3, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] = .ok := by decide

/-- A broken instance carries its fraction: 1 of 2 pairs satisfied. -/
example : solve [7, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] = .blocked ⟨7, "a", 1, 2⟩ :=
  by decide

/-- The solver agrees with the checker. -/
example : solve [3, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] = .ok :=
  (solve_ok _ _).mpr (by decide)

/-! ## E-39: slicing an expression tree -/

/-- Evaluation is the sum. -/
example : eval (.add (.const 3) (.const (-2))) = 1 := rfl

/-- The dead branch is sliced away. -/
example : prune (.add (.const 0) (.const 5)) = .const 5 := rfl

/-- The trivial cut is listed. -/
example : ((.add (.const 1) (.const 2)), .const 0) ∈
    cuts (.add (.const 1) (.const 2)) := by decide

/-- Slicing preserves the value. -/
example : eval (prune (.add (.const 0) (.const 5))) =
    eval (.add (.const 0) (.const 5)) :=
  eval_prune _

/-! ## E-40: two polarizations, one spectrum -/

/-- Registers alternate q, p. -/
example : lowerReg [(1, 2), (3, 4)] = [1, 2, 3, 4] := rfl

/-- The stack pushes qs, then ps. -/
example : lowerStack [(1, 2), (3, 4)] = [1, 3, 2, 4] := rfl

/-- Both polarizations agree on the spectrum. -/
example : evalCells (lowerReg [(1, 2), (3, 4)]) =
    evalCells (lowerStack [(1, 2), (3, 4)]) := rfl

/-! ## E-41: a Borromean triple -/

def triMod : List (Nat × Nat) := [(0, 1), (1, 2), (2, 0)]

/-- The directed 3-cycle with no back-edges fires. -/
example : massey3 0 1 2 triMod = true := by decide

/-- A back-edge kills it. -/
example : massey3 0 1 2 (triMod ++ [(1, 0)]) = false := by decide

/-- No pairwise cycle here. -/
example : hasTwoCycle triMod = false := by decide

/-- The triple still deadlocks globally. -/
example : hasCycle triMod = true := by decide

/-! ## E-42: packing two fields -/

/-- First-fit offsets. -/
example : pack [4, 8, 2] = [0, 4, 12] := rfl

/-- Field extents. -/
example : extents [4, 8] = [(0, 4), (4, 8)] := rfl

/-- The packed fields are disjoint. -/
example : disjointCheck (extents [4, 8]) = true := by decide

/-- Greedy packing is always certified. -/
example : disjointCheck (extents [4, 8]) = true := pack_cert _

/-! ## E-43: rerouting around a glitch -/

def dprEdges : List (Nat × Nat) := [(0, 1), (1, 2), (0, 2)]

/-- The direct path is admissible when nothing is anomalous. -/
example : checkPath [0, 1, 2] [(0, 1), (1, 2)] [] = true := by decide

/-- The anomaly breaks admission. -/
example : checkPath [0, 1, 2] dprEdges [1] = false := by decide

/-- Good paths are left alone. -/
example : deform [0, 1, 2] [(0, 1), (1, 2)] [] = some [0, 1, 2] := by decide

/-- The reroute skips the glitch. -/
example : deform [0, 1, 2] dprEdges [1] = some [0, 2] := by decide

/-- Deformation only returns admissible paths. -/
example : checkPath [0, 1, 2] [(0, 1), (1, 2)] [] = true :=
  deform_sound [0, 1, 2] [(0, 1), (1, 2)] [] [0, 1, 2] (by decide)

/-! ## E-44: failover keeps the newest -/

/-- A newer version replaces the incumbent. -/
example : upsert ⟨1, 2, 5⟩ [⟨1, 1, 3⟩] = [⟨1, 2, 5⟩] := rfl

/-- An older version keeps the incumbent. -/
example : upsert ⟨1, 1, 9⟩ [⟨1, 5, 3⟩] = [⟨1, 5, 3⟩] := rfl

/-- Lookup finds the key. -/
example : findK 2 [⟨1, 2, 5⟩, ⟨2, 1, 7⟩] = some ⟨2, 1, 7⟩ := rfl

/-- Reconciliation unions both sides. -/
example : reconcile [⟨1, 2, 5⟩] [⟨2, 1, 7⟩] = [⟨1, 2, 5⟩, ⟨2, 1, 7⟩] := rfl

/-- Failover reads the max version. -/
example : findK 1 (reconcile [⟨1, 2, 5⟩] [⟨2, 1, 7⟩]) = some ⟨1, 2, 5⟩ :=
  by decide

/-- Repeating an upsert is stable. -/
example : upsert ⟨1, 2, 5⟩ (upsert ⟨1, 2, 5⟩ [⟨1, 1, 3⟩]) =
    upsert ⟨1, 2, 5⟩ [⟨1, 1, 3⟩] :=
  upsert_idem _ _

/-! ## E-45: scattering a two-sample signal -/

/-- The big sample binds, the small one radiates. -/
example : scatter [5, -1] 3 = ([true, false], [5], [-1]) := rfl

/-- The mask merge inverts the split. -/
example : reconstruct [true, false] [5] [-1] = [5, -1] := rfl

/-- Energy is 9 + 16. -/
example : sumsq [3, -4] = 25 := rfl

/-- Roundtrip on a fresh signal. -/
example : reconstruct ([5, -1].map (isBound 3))
    ([5, -1].filter (isBound 3))
    ([5, -1].filter fun x => !(isBound 3 x)) = [5, -1] :=
  recon_roundtrip _ _

/-! ## E-46: the truncated product on three ops -/

/-- The bracket is the difference. -/
example : bracket 3 5 = -2 := rfl

/-- Ordered-pair corrections over [1, 2, 3]. -/
example : corr [1, 2, 3] = -4 := by decide

/-- Classical sum 6 plus correction −4. -/
example : star [1, 2, 3] = 2 := by decide

/-- Swapping windows negates the correction. -/
example : cross [1] [2] = -cross [2] [1] := cross_sym _ _

/-! ## E-47: three verdicts -/

/-- Negative discriminant: spacelike. -/
example : disc ⟨0, 1, -1, 0⟩ = -4 := rfl

/-- Large positive discriminant: timelike. -/
example : classify ⟨1, 2, 3, 4⟩ 5 = .time := by decide

/-- Degenerate spectrum: lightlike. -/
example : classify ⟨0, 0, 0, 0⟩ 5 = .light := by decide

/-- Spacelike skips the fence. -/
example : needsFence (classify ⟨0, 1, -1, 0⟩ 5) = false := by decide

/-- The degenerate case is classified lightlike by the smallness rule. -/
example : classify ⟨0, 0, 0, 0⟩ 5 = .light :=
  light_of_small _ _ (by decide) (by decide)

end Morph.Specs.BatchDEF

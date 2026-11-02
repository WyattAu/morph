/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchFGH.Lemmas

/-!
# Frontier Kernels — examples (E-48–E-57)

Status: first cycle complete (loop 108).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchFGH

/-! ## E-48: a two-book mutation -/

/-- Mutation fires on exact division. -/
example : mut0 ⟨3, 5⟩ 6 2 = ⟨2, 5⟩ := by decide

/-- Mutation refuses an inexact quotient. -/
example : mut0 ⟨3, 5⟩ 7 2 = ⟨3, 5⟩ := by decide

/-- The seed is positive. -/
example : seedPosB ⟨3, 5⟩ = true := by decide

/-- Positivity agrees with the proposition. -/
example : seedPosB ⟨3, 5⟩ = true ↔ seedPos ⟨3, 5⟩ := seedPosB_eq _

/-! ## E-49: staying outside the cone -/

/-- A distant reader at late time is safe. -/
example : safeR 2 0 10 3 = true := by decide

/-- A close reader is inside the cone. -/
example : safeR 2 8 10 3 = false := by decide

/-- A placement safe against two mutators. -/
example : placeAll 2 [0, 3] 10 3 = true := by decide

/-! ## E-50: pushing two pointers apart -/

/-- The gap is the difference. -/
example : gap ⟨1, 4⟩ = 3 := rfl

/-- One step moves both pointers out. -/
example : repel ⟨1, 4⟩ = ⟨0, 5⟩ := rfl

/-- A step grows the gap by two. -/
example : gap (repel ⟨1, 4⟩) = gap ⟨1, 4⟩ + 2 := repel_gap _ (by decide)

/-! ## E-51: shrinking a macro -/

/-- Zero-unit elimination fires. -/
example : stepM (.add (.const 0) (.const 5)) = some (.const 5) := rfl

/-- Constants are normal. -/
example : isNormal (.const 3) = true := by decide

/-- The measure counts nodes. -/
example : msize (.add (.const 1) (.const 2)) = 3 := rfl

/-- Fuel covering the measure normalizes. -/
example : isNormal (normM 5 (.add (.const 0) (.const 5))) = true :=
  normM_normal _ _ (by decide)

/-! ## E-52: pushing a boundary forward -/

/-- The boundary of `c0` is `c1`. -/
example : (bdyC .c0).map cmap = [.d1] := rfl

/-- The chain-map square commutes on `c0`. -/
example : (bdyC .c0).map cmap = bdyD (cmap .c0) := cmap_chain _

/-- Cycles push forward to cycles. -/
example : isCycleD (cmap .c1) = true := cmap_cycle _ (by decide)

/-! ## E-53: rerouting around a dead link -/

def meshE : List (Nat × Nat) := [(0, 1), (1, 2)]

/-- A live hop is admitted. -/
example : alive meshE [] 1 2 = true := by decide

/-- A dead hop is refused. -/
example : alive meshE [(0, 1)] 0 1 = false := by decide

/-- The direct route is taken when live. -/
example : route2 meshE 0 1 [] = some [0, 1] := by decide

/-- The dead direct edge is re-derived through the midpoint. -/
example : route2 meshE 0 2 [(0, 2)] = some [0, 1, 2] := by decide

/-- No route through a fully dead mesh. -/
example : route2 meshE 0 2 [(0, 1), (1, 2)] = none := by decide

/-! ## E-54: localizing a tiny locus -/

/-- Integer sums evaluate. -/
example : isum [1, -2, 3] = 2 := rfl

/-- The total over a mixed locus. -/
example : total (fun n => (n : Int)) ⟨[1, 2], [(3, 4)]⟩ = 10 := by decide

/-- Two samples clear the threshold. -/
example : countGt [1, 5, 3] 2 = 2 := by decide

/-! ## E-55: admitting a descriptor -/

/-- An in-bounds aligned flagged descriptor is admitted. -/
example : admit 64 ⟨8, 16, true⟩ = true := by decide

/-- An over-long descriptor is rejected as bounds. -/
example : rejectReason 16 ⟨8, 16, true⟩ = some "bounds" := by decide

/-- An unaligned descriptor is rejected as alignment. -/
example : rejectReason 64 ⟨7, 8, true⟩ = some "align" := by decide

/-- Admission agrees with no-rejection. -/
example : rejectReason 64 ⟨8, 16, true⟩ = none ↔
    admit 64 ⟨8, 16, true⟩ = true :=
  reject_iff _ _

/-! ## E-56: translating a tiny program -/

/-- Increment then add-three runs to four. -/
example : xrun [.inc, .add 3] 0 = 4 := rfl

/-- Translation is the identity table here. -/
example : transpL [.inc, .add 3] = [.inc, .add 3] := rfl

/-- One opcode commutes with evaluation. -/
example : aeval (transp (.add 3)) 0 = xeval (.add 3) 0 := transp_correct _ _

/-! ## E-57: minimizing a toggle -/

/-- A two-state toggle: 0 –true→ 1. -/
def toggle : DFA := ⟨[0, 1], 0, [1], fun s _ => 1 - s⟩

/-- The word `true` is accepted. -/
example : accepts toggle [true] = true := by decide

/-- The word `true, false` is rejected. -/
example : accepts toggle [true, false] = false := by decide

/-- Minimization keeps the accepted word. -/
example : accepts (minimize toggle) [true] = true := by decide

/-- Minimization never adds states. -/
example : (minimize toggle).states.length ≤ toggle.states.length :=
  minimize_le _

end Morph.Specs.BatchFGH

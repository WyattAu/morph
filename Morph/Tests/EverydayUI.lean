/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.EverydayUI.Examples

/-!
# Everyday UI kernel — validation (E-1351–E-1360)

Status: In Progress (loop 103).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(translation, composition, resumption, single evaluation) are exercised where
a single example could pass by accident.

Run: `lake build Morph.Tests.EverydayUI`.
-/

namespace Morph.Tests.EverydayUI

open Morph.Specs.EverydayUI

/-! ## E-1351: coverage is stable under translation -/

example : Covered (rowBoxes [12, 8, 5] 40) 45 :=
  ⟨(40, 12), by decide, by decide, by decide⟩

example : Covered (rowBoxes [12, 8, 5] 40) 55 :=
  ⟨(52, 8), by decide, by decide, by decide⟩

/-- Translation invariance, then coverage at the translated origin: the two
theorems agree on a concrete row. -/
example : Covered (rowBoxes [12, 8, 5] (10 + 30)) (10 + 43) := by
  rw [rowBoxes_translate]
  exact ⟨(22 + 30, 8), by decide, by decide, by decide⟩

/-! ## E-1354: tiling invariants on a fresh row -/

example : (rowBoxes [4, 6, 9] 0).map Prod.snd = [4, 6, 9] :=
  rowBoxes_widths [4, 6, 9] 0

example : (rowBoxes [4, 6, 9] 0).length = 3 := rowBoxes_length [4, 6, 9] 0

example : Confined (rowBoxes [4, 6, 9] 7) 7 19 :=
  rowBoxes_confined [4, 6, 9] 7

example : (rowBoxes [4, 6, 9] 0).Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  decide

example : (rowRects [4, 6, 9] 0 2 8).Pairwise Rect.disjoint :=
  rowRects_disjoint [4, 6, 9] 0 2 8

example : (rowRects [4, 6, 9] 0 2 8).length = 3 := by decide

/-! ## Shared geometry laws -/

example : (⟨1, 2, 3, 4⟩ : Rect).contains ⟨1, 2, 3, 4⟩ := Rect.contains_refl _

example : (⟨0, 0, 9, 9⟩ : Rect).contains ⟨3, 3, 3, 3⟩ :=
  Rect.contains_trans (a := ⟨0, 0, 9, 9⟩) (b := ⟨1, 1, 5, 5⟩) (c := ⟨3, 3, 3, 3⟩)
    (by unfold Rect.contains Rect.right Rect.bottom; decide)
    (by unfold Rect.contains Rect.right Rect.bottom; decide)

example : (⟨10, 0, 5, 5⟩ : Rect).disjoint ⟨0, 0, 10, 5⟩ :=
  Rect.disjoint_symm (by unfold Rect.disjoint Rect.right Rect.bottom; decide)

/-! ## E-1352: a pass that is already fixed -/

/-- Height-zero pass: the lattice has a single element. -/
def zeroPass : UpdatePass where
  step _ := 0
  height := 0
  mono := by intro a b _; exact Nat.le_refl 0
  extensive := by intro a ha; omega
  bounded := by intro a _; exact Nat.zero_le 0

example : zeroPass.step (iterate zeroPass.step zeroPass.height) =
    iterate zeroPass.step zeroPass.height :=
  zeroPass.stabilizes

example : cappedPass.step (iterate cappedPass.step 0) = 1 := by decide

example : cappedPass.step (iterate cappedPass.step 1) = 2 := by decide

example : cappedPass.step (iterate cappedPass.step 2) = 3 := by decide

/-! ## E-1353: laws hold for the composed lens -/

example : deepLens.get (deepLens.put ((3, 4), 5) 8) = 8 :=
  deepLens_lawful.putGet ((3, 4), 5) 8

example : deepLens.put ((3, 4), 5) (deepLens.get ((3, 4), 5)) = ((3, 4), 5) :=
  deepLens_lawful.getPut ((3, 4), 5)

example : deepLens.put (deepLens.put ((3, 4), 5) 8) 9 =
    deepLens.put ((3, 4), 5) 9 :=
  deepLens_lawful.putPut ((3, 4), 5) 8 9

/-! ## E-1355: routing at every position, and a miss -/

def wideTree : BTree :=
  .node 0 (.node 1 (.leaf 3) (.leaf 4)) (.node 2 (.leaf 5) .empty)

example : wideTree.route 0 = some wideTree :=
  BTree.route_self wideTree (by decide)

example : wideTree.route 3 = some (.leaf 3) := by decide

example : wideTree.route 5 = some (.leaf 5) := by decide

example : wideTree.route 6 = none := by decide

example : 5 ∈ (BTree.leaf 5).ids :=
  BTree.route_sound wideTree 5 (.leaf 5) (by decide)

/-! ## E-1356: nested resumption leaves deeper stacks intact -/

/-- `(1 + 2) * (3 + 4)`. -/
def nestedExpr : Expr :=
  .mul (.add (.lit 1) (.lit 2)) (.add (.lit 3) (.lit 4))

example : nestedExpr.eval = 21 := by decide

example : run nestedExpr.compile [] = some [21] := by decide

example : run nestedExpr.compile [100, 200] = some [21, 100, 200] := by decide

/-- Resumption is compositional on an arbitrary split. -/
example : run (Expr.add (.lit 1) (.lit 2)).compile [9] = some [3, 9] :=
  run_compile (.add (.lit 1) (.lit 2)) [9]

/-! ## E-1357: interpolation endpoints -/

example : lerp 0 100 0 = 0 := lerp_zero 0 100

example : lerp 0 100 100 = 100 := lerp_hundred 0 100

example : lerp 13 29 100 = 29 := lerp_hundred 13 29

example : lerp 13 13 0 = 13 := lerp_const 13 0 (by decide)

example : lerp 4 12 50 = lerp 12 4 50 := lerp_reverse 4 12 50 (by decide)

/-! ## E-1358: triple use is rejected -/

example : ¬ (Usage.seq (Usage.seq (.use 2) (.pure 0)) (.use 2)).Linear := by
  intro h
  have hc := h 2
  simp [Usage.handles] at hc

/-! ## E-1359: substitution preserves the interface -/

def unaryOp : Op := ⟨"neg", [0], 0⟩

def binaryOp : Op := ⟨"pair", [0, 0], 0⟩

example : (unaryOp.composeAt 0 binaryOp).inputs = [0, 0] := by decide

example : (unaryOp.composeAt 0 binaryOp).inputs.length = 1 - 1 + 2 :=
  Op.composeAt_inputs_length unaryOp 0 binaryOp (by decide)

example : (binaryOp.composeAt 1 unaryOp).inputs.length = 2 - 1 + 1 :=
  Op.composeAt_inputs_length binaryOp 1 unaryOp (by decide)

/-! ## E-1360: single evaluation, edge cases -/

example : evalDag [] = [] := rfl

example : evalDag [⟨7, []⟩] = [(7, 0)] := by decide

example : (evalDag [⟨7, []⟩]).length = 1 := evalDag_length [⟨7, []⟩]

example : (evalDag sampleDag).map Prod.fst = sampleDag.map DagNode.id :=
  evalDag_ids sampleDag

end Morph.Tests.EverydayUI

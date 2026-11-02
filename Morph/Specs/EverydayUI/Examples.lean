/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.EverydayUI.Lemmas

/-!
# Everyday UI Kernel — examples (E-1351–E-1360)

Status: In Progress (loop 103).

Concrete instances that exercise every core and every theorem in the module.
These are the "does the model say the right thing" cases; the register rows'
external baselines are exercised separately in `Morph/Tests/EverydayUI.lean`.
-/

namespace Morph.Specs.EverydayUI

/-! ## Geometry -/

example : (⟨0, 0, 10, 10⟩ : Rect).contains ⟨2, 2, 3, 3⟩ := by
  unfold Rect.contains Rect.right Rect.bottom
  decide

example : Rect.disjoint ⟨0, 0, 10, 10⟩ ⟨10, 0, 10, 10⟩ := by
  unfold Rect.disjoint Rect.right Rect.bottom
  decide

example : ¬ Rect.disjoint ⟨0, 0, 10, 10⟩ ⟨5, 0, 10, 10⟩ := by
  unfold Rect.disjoint Rect.right Rect.bottom
  decide

/-! ## E-1351 / E-1354: row layout -/

example : rowBoxes [30, 20, 50] 0 = [(0, 30), (30, 20), (50, 50)] := by decide

example : rowBoxes [30, 20] 5 = [(5, 30), (35, 20)] := by decide

example : (rowBoxes [30, 20, 50] 0).map Prod.snd = [30, 20, 50] :=
  rowBoxes_widths [30, 20, 50] 0

example : Covered (rowBoxes [30, 20, 50] 0) 45 :=
  ⟨(30, 20), by decide, by decide, by decide⟩

example : Confined (rowBoxes [10, 20] 5) 5 30 := rowBoxes_confined [10, 20] 5

example : (rowBoxes [10, 20] 0).Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  decide

/-! ## E-1352: Kleene iteration -/

/-- A three-step update pass: advance to three, then stop. -/
def cappedPass : UpdatePass where
  step n := if n < 3 then n + 1 else 3
  height := 3
  mono := by
    intro a b h
    split <;> split <;> omega
  extensive := by
    intro a ha
    split <;> omega
  bounded := by
    intro a ha
    split <;> omega

example : iterate cappedPass.step 3 = 3 := by decide

example : cappedPass.step (iterate cappedPass.step cappedPass.height) =
    iterate cappedPass.step cappedPass.height :=
  cappedPass.stabilizes

/-! ## E-1353: lenses -/

/-- Focus on the first component. -/
def fstLens : Lens (Nat × Nat) Nat where
  get p := p.1
  put p a := (a, p.2)

/-- Focus on the second component. -/
def sndLens : Lens (Nat × Nat) Nat where
  get p := p.2
  put p b := (p.1, b)

theorem fstLens_lawful : Lawful fstLens where
  putGet := by intro s a; rfl
  getPut := by intro s; cases s; rfl
  putPut := by intro s a b; rfl

theorem sndLens_lawful : Lawful sndLens where
  putGet := by intro s a; rfl
  getPut := by intro s; cases s; rfl
  putPut := by intro s a b; rfl

/-- Focus through a nested pair: `((a, b), c) ↦ a`. -/
def outerLens : Lens ((Nat × Nat) × Nat) (Nat × Nat) where
  get p := p.1
  put p a := (a, p.2)

def deepLens : Lens ((Nat × Nat) × Nat) Nat := outerLens.comp fstLens

theorem deepLens_lawful : Lawful deepLens :=
  Lens.lawful_comp outerLens fstLens ⟨by intro s a; rfl, by intro s; cases s; rfl,
    by intro s a b; rfl⟩ fstLens_lawful

example : deepLens.get ((1, 2), 3) = 1 := rfl

example : deepLens.put ((1, 2), 3) 9 = ((9, 2), 3) := rfl

example : fstLens.get (sndLens.put (4, 5) 6) = 4 := rfl

/-! ## E-1355: routing -/

/-- `1 → {2 → {4, 5}, 3}`. -/
def sampleTree : BTree := .node 1 (.node 2 (.leaf 4) (.leaf 5)) (.leaf 3)

example : sampleTree.route 4 = some (.leaf 4) := by decide

example : sampleTree.route 1 = some sampleTree := by decide

example : sampleTree.route 9 = none := by decide

example : 4 ∈ (BTree.leaf 4).ids :=
  BTree.route_sound sampleTree 4 (.leaf 4) (by decide)

example : (BTree.node 2 (.leaf 4) (.leaf 5)).route 5 = some (.leaf 5) := by
  exact BTree.route_self _ (by decide)

/-! ## E-1356: compiled continuations -/

/-- `2 + 3 * 4`. -/
def sampleExpr : Expr := .add (.lit 2) (.mul (.lit 3) (.lit 4))

example : sampleExpr.eval = 14 := by decide

example : run sampleExpr.compile [] = some [14] := by decide

example : run sampleExpr.compile [7] = some [14, 7] := by decide

example : run (Expr.lit 5).compile [1, 2] = some [5, 1, 2] :=
  run_compile (.lit 5) [1, 2]

/-! ## E-1357: interpolation -/

example : lerp 0 100 25 = 25 := by decide

example : lerp 10 20 50 = 15 := by decide

example : lerp 7 7 63 = 7 := lerp_const 7 63 (by decide)

example : lerp 10 20 25 = lerp 20 10 75 := lerp_reverse 10 20 25 (by decide)

/-! ## E-1358: affine usage -/

example : (Usage.use 3).Linear := Usage.linear_use 3

example : (Usage.pure 0).Linear := Usage.linear_pure 0

example : ((Usage.use 1).seq (.pure 2)).Linear := by
  intro h
  simp only [Usage.handles, List.count_append, List.count_cons, List.count_nil]
  split <;> omega

example : ¬ (Usage.seq (.use 1) (.use 1)).Linear := double_use_rejected 1

/-! ## E-1359: operadic substitution -/

def arithAdd : Op := ⟨"add", [0, 1], 1⟩

def arithInc : Op := ⟨"inc", [0], 1⟩

example : (arithAdd.composeAt 1 arithInc).inputs = [0, 0] := by decide

example : (arithAdd.composeAt 1 arithInc).output = 1 :=
  Op.composeAt_output arithAdd 1 arithInc

example : (arithAdd.composeAt 1 arithInc).inputs.length =
    arithAdd.inputs.length - 1 + arithInc.inputs.length :=
  Op.composeAt_inputs_length arithAdd 1 arithInc (by decide)

/-! ## E-1360: single-pass DAG -/

/-- `0; 1 ← 0; 2 ← 0, 1`. -/
def sampleDag : List DagNode := [⟨0, []⟩, ⟨1, [0]⟩, ⟨2, [0, 1]⟩]

example : evalDag sampleDag = [(0, 0), (1, 0), (2, 0)] := by decide

example : (evalDag sampleDag).map Prod.fst = [0, 1, 2] := by decide

example : (evalDag sampleDag).length = 3 := evalDag_length sampleDag

end Morph.Specs.EverydayUI

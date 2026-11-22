/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal

/-!
# Proof crate `Assembly` (L0 leaf): block-assembly nodup and membership

Estate-style leaf: depends on `Core`/`Total` only, never on
`Morph.HIRToMIRBranch` or another leaf. `Morph.HIRToMIRBranch` imports this
module back; the tree stays green between cuts.

Provenance (statements unchanged, proofs verbatim): `nodup_concat`,
`findBlock_of_nodup_mem`, `if_assembly_nodup`, `while_assembly_nodup`
(extracted from `Morph/HIRToMIRBranch.lean` § "C3 infrastructure"), and the
`if_asm_mem_*` arrival-label lifts (extracted from beside
`lowerStmtsCFG_branchArm_rho`).

Pure list reasoning about lowered block assemblies: the six-part `if`
assembly and the five-part `while` assembly have duplicate-free ids, and
every member/lift maps into the whole assembly. No lowering, execution, or
environment facts involved.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Appending duplicate-free id lists with no shared id keeps duplicate-free
ids. The workhorse for the six-part `if` assembly. -/
theorem nodup_concat {l₁ l₂ : List Nat} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a as ih =>
      rw [List.cons_append, List.nodup_cons] at ⊢
      rw [List.nodup_cons] at h₁
      obtain ⟨hnotin, hnod⟩ := h₁
      refine ⟨?_, ih hnod (fun x hx y hy => hd x (List.mem_cons_of_mem _ hx) y hy)⟩
      intro hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hnotin h
      · exact hd _ (List.mem_cons_self ..) _ h rfl

/-- A block list with duplicate-free ids answers `find?` by membership: the
first match is the block itself, because no other block shares its id. -/
theorem findBlock_of_nodup_mem {l : List Block} {b : Block}
    (hnod : (l.map Block.id).Nodup) (hmem : b ∈ l) :
    l.find? (fun b' => b'.id == b.id) = some b := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnod
      obtain ⟨hnotin, hnodtl⟩ := hnod
      cases hb : (hd.id == b.id) with
      | true =>
          have hid : hd.id = b.id := by simpa using hb
          have hnotmem : b ∉ tl := fun h => hnotin (List.mem_map.mpr ⟨b, h, hid.symm⟩)
          have heq : hd = b := by
            rcases List.mem_cons.mp hmem with h | h
            · exact h.symm
            · exact absurd h hnotmem
          subst heq
          simp only [List.find?, hb]
      | false =>
          have hmemtl : b ∈ tl := by
            rcases List.mem_cons.mp hmem with h | h
            · exfalso
              have ht := beq_self_eq_true (b.id)
              rw [← h] at hb
              rw [hb] at ht
              exact Bool.false_ne_true ht
            · exact h
          simp only [List.find?, hb]
          exact ih hnodtl hmemtl

private theorem ne_of_lt_nat' {a b : Nat} (h : a < b) : a ≠ b :=
  Nat.ne_of_lt h

private theorem ne_of_gt_nat' {a b : Nat} (h : a > b) : a ≠ b :=
  (Nat.ne_of_lt h).symm

/-- The six block groups of a lowered `if` have pairwise-disjoint id ranges
— arms below their joins, joins below the next call's ids — so the whole
assembly is duplicate-free. Stated on id lists, so the caller never has to
reassociate the block concatenation: the conclusion is definitionally the
pushed-through map. -/
theorem if_assembly_nodup {nextB ltNext leNext lrNext : Nat}
    {A B C : List Block} {thenB elseB joinB : Block}
    (hmnt : nextB + 3 ≤ ltNext) (hmne : ltNext ≤ leNext) (_hmnr : leNext ≤ lrNext)
    (hbndA : ∀ b ∈ A, nextB + 3 ≤ b.id ∧ b.id < ltNext)
    (hbndB : ∀ b ∈ B, ltNext ≤ b.id ∧ b.id < leNext)
    (hbndC : ∀ b ∈ C, leNext ≤ b.id ∧ b.id < lrNext)
    (hthen : thenB.id = nextB) (helse : elseB.id = nextB + 1)
    (hjoin : joinB.id = nextB + 2)
    (hnodA : (A.map Block.id).Nodup) (hnodB : (B.map Block.id).Nodup)
    (hnodC : (C.map Block.id).Nodup) :
    ((A ++ [thenB] ++ B ++ [elseB] ++ [joinB] ++ C).map Block.id).Nodup := by
  have hbA : ∀ x ∈ A.map Block.id, nextB + 3 ≤ x ∧ x < ltNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndA b hb
  have hbB : ∀ x ∈ B.map Block.id, ltNext ≤ x ∧ x < leNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndB b hb
  have hbC : ∀ x ∈ C.map Block.id, leNext ≤ x ∧ x < lrNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndC b hb
  have e1 : ([nextB + 2] ++ C.map Block.id).Nodup :=
    nodup_concat (by simp) hnodC (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨hloC, -⟩ := hbC y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
        (Nat.le_trans (Nat.le_trans hmnt hmne) hloC)))
  have e2 : ([nextB + 1] ++ ([nextB + 2] ++ C.map Block.id)).Nodup :=
    nodup_concat (by simp) e1 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with rfl | hy
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 1 < 2 from by decide) nextB)
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
          (Nat.le_trans (Nat.le_trans hmnt hmne) hloC)))
  have e3 : (B.map Block.id ++
      ([nextB + 1] ++ ([nextB + 2] ++ C.map Block.id))).Nodup :=
    nodup_concat hnodB e2 (by
      intro x hx y hy
      obtain ⟨hloB, hhiB⟩ := hbB x hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with rfl | rfl | hy
      · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
          (Nat.le_trans hmnt hloB))
      · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
          (Nat.le_trans hmnt hloB))
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiB hloC))
  have e4 : ([nextB] ++ (B.map Block.id ++
      ([nextB + 1] ++ ([nextB + 2] ++ C.map Block.id)))).Nodup :=
    nodup_concat (by simp) e3 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl | rfl | hy
      · obtain ⟨hloB, -⟩ := hbB y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 0 < 3 from by decide) x)
          (Nat.le_trans hmnt hloB))
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 0 < 1 from by decide) x)
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 0 < 2 from by decide) x)
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 0 < 3 from by decide) x)
          (Nat.le_trans (Nat.le_trans hmnt hmne) hloC)))
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    hthen, helse, hjoin]
  exact nodup_concat hnodA e4 (by
    intro x hx y hy
    obtain ⟨hloA, hhiA⟩ := hbA x hx
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with rfl | hy | rfl | rfl | hy
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 0 < 3 from by decide) y)
        hloA)
    · obtain ⟨hloB, -⟩ := hbB y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiA hloB)
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
        hloA)
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
        hloA)
    · obtain ⟨hloC, -⟩ := hbC y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiA (Nat.le_trans hmne hloC)))
/-- The five block groups of a lowered `while`: the body below its own join,
the body-entry/header/exit singletons in id order below the body, the rest
below everything. Same concat technique as `if_assembly_nodup`. -/
theorem while_assembly_nodup {nextB lbNext lrNext : Nat}
    {A C : List Block} {bodyB headerB exitB : Block}
    (hmn : nextB + 3 ≤ lbNext) (_hmnr : lbNext ≤ lrNext)
    (hbndA : ∀ b ∈ A, nextB + 3 ≤ b.id ∧ b.id < lbNext)
    (hbndC : ∀ b ∈ C, lbNext ≤ b.id ∧ b.id < lrNext)
    (hbody : bodyB.id = nextB + 2) (hheader : headerB.id = nextB)
    (hexit : exitB.id = nextB + 1)
    (hnodA : (A.map Block.id).Nodup) (hnodC : (C.map Block.id).Nodup) :
    ((A ++ [bodyB] ++ [headerB] ++ [exitB] ++ C).map Block.id).Nodup := by
  have hbA : ∀ x ∈ A.map Block.id, nextB + 3 ≤ x ∧ x < lbNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndA b hb
  have hbC : ∀ x ∈ C.map Block.id, lbNext ≤ x ∧ x < lrNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndC b hb
  have e1 : ([nextB + 1] ++ C.map Block.id).Nodup :=
    nodup_concat (by simp) hnodC (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst x
      obtain ⟨hloC, -⟩ := hbC y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
        (Nat.le_trans hmn hloC)))
  have e2 : ([nextB] ++ ([nextB + 1] ++ C.map Block.id)).Nodup :=
    nodup_concat (by simp) e1 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst x
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with rfl | hy
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 0 < 1 from by decide) nextB)
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 0 < 3 from by decide) nextB)
          (Nat.le_trans hmn hloC)))
  have e3 : ([nextB + 2] ++
      ([nextB] ++ ([nextB + 1] ++ C.map Block.id))).Nodup :=
    nodup_concat (by simp) e2 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      simp only [List.mem_append, List.mem_singleton] at hy
      -- Name the edge equations instead of substituting them: `rfl`/`subst`
      -- eliminate one side, and when both sides are variables (`y = nextB`)
      -- that can be `nextB` itself. `omega` reads the equations in place.
      rcases hy with hy1 | hy1 | hy
      · omega
      · omega
      · obtain ⟨hloC, -⟩ := hbC y hy
        omega)
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    hbody, hheader, hexit]
  exact nodup_concat hnodA e3 (by
    intro x hx y hy
    obtain ⟨hloA, hhiA⟩ := hbA x hx
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy1 | hy1 | hy1 | hy
    · omega
    · omega
    · omega
    · obtain ⟨hloC, -⟩ := hbC y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiA hloC))

/-- Membership in the six-part `if` assembly, by part. The worker feeds these
to `hsub`/`findBlock_of_nodup_mem` without re-counting the append nesting at
every call site. -/
theorem if_asm_mem_of_lt {lt le lr : List Block} {T E J : Block} {b : Block}
    (h : b ∈ lt) : b ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ h))))

theorem if_asm_mem_then {lt le lr : List Block} {T E J : Block} :
    T ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (by simp)))))

theorem if_asm_mem_of_le {lt le lr : List Block} {T E J : Block} {b : Block}
    (h : b ∈ le) : b ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h)))

theorem if_asm_mem_else {lt le lr : List Block} {T E J : Block} :
    E ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (by simp)))

theorem if_asm_mem_join {lt le lr : List Block} {T E J : Block} :
    J ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem if_asm_mem_of_lr {lt le lr : List Block} {T E J : Block} {b : Block}
    (h : b ∈ lr) : b ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_right _ h

/-- Arrival-label lifts for the six-part `if` assembly: a predecessor that is
the join id or lives in the rest maps into the whole assembly (and likewise
for the then/else entries and arm sub-blocks). Used to transport the new
arrival-membership disjunct through `arm_continued`'s `if` arm. -/
theorem if_asm_mem_of_rest' {lt le lr : List Block} {T E J : Block}
    {x : MIR.BlockId}
    (h : x = J.id ∨ x ∈ lr.map Block.id) :
    x ∈ (lt ++ [T] ++ le ++ [E] ++ [J] ++ lr).map Block.id := by
  rcases h with heq | hm
  · exact List.mem_map.mpr ⟨J, if_asm_mem_join, heq.symm⟩
  · obtain ⟨b, hb, hid⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨b, if_asm_mem_of_lr hb, hid⟩

theorem if_asm_mem_of_then' {lt le lr : List Block} {T E J : Block}
    {x : MIR.BlockId}
    (h : x = T.id ∨ x ∈ lt.map Block.id) :
    x ∈ (lt ++ [T] ++ le ++ [E] ++ [J] ++ lr).map Block.id := by
  rcases h with heq | hm
  · exact List.mem_map.mpr ⟨T, if_asm_mem_then, heq.symm⟩
  · obtain ⟨b, hb, hid⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨b, if_asm_mem_of_lt hb, hid⟩

theorem if_asm_mem_of_else' {lt le lr : List Block} {T E J : Block}
    {x : MIR.BlockId}
    (h : x = E.id ∨ x ∈ le.map Block.id) :
    x ∈ (lt ++ [T] ++ le ++ [E] ++ [J] ++ lr).map Block.id := by
  rcases h with heq | hm
  · exact List.mem_map.mpr ⟨E, if_asm_mem_else, heq.symm⟩
  · obtain ⟨b, hb, hid⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨b, if_asm_mem_of_le hb, hid⟩

end Morph.HIRToMIRCorrect

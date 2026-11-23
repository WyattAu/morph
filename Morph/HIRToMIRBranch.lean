/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal
import Morph.Proofs.Branch.Merge
import Morph.Proofs.Branch.Fragments
import Morph.Proofs.Branch.Fuel
import Morph.Proofs.Branch.LoopAlloc
import Morph.Proofs.Branch.Assembly
import Morph.Proofs.Branch.Equations
import Morph.HIRToMIRLower
import Morph.Proofs.Branch.Infra
import Morph.Proofs.Branch.ArmTotal
import Morph.Proofs.Branch.ArmBroke
import Morph.Proofs.Branch.ArmContinued
import Morph.Proofs.Branch.LoopBodyRun
import Morph.Proofs.Branch.Oracle
import Morph.Proofs.Branch.BindArm
import Morph.Proofs.Branch.LoopLookup
import Morph.Proofs.Branch.Spine
import Morph.Proofs.Branch.WhileLoop
import Morph.Proofs.Branch.Total
import Morph.Proofs.Branch.IfTotal

/-!
# Stage C: the `if` fragment and its CFG lowering

`docs/STAGEC-SCOPE.md` items C2a/C2b. Two pieces:

**The fragment** (`BranchStmts`, `BranchStep`, `ArmStmts`). Stage A's
`StraightStmts` (`Morph/HIRToMIRCore.lean`) is the hypothesis of
`compile_total`, so adding an `ifStmt` constructor to it would make that
theorem's `if`-case an unproved obligation the moment the constructor exists —
the tree would stop being green between C2 and C3. This file instead defines the
Stage C fragment as a *new* predicate that strictly contains the straight-line
one (`straightStmts_to_branch`). `compile_total` keeps its exact statement and
its exact proof; C3's theorem takes `BranchStmts`, and its `if`-free instances
are recovered through the embedding.

Three deliberate shape choices:

- **Statement steps are a separate relation.** `BranchStep` holds the
  per-statement conditions; `BranchStmts` holds the list structure. `ifStmt` is
  then an extra *side* condition instead of a new arm inside an existing
  induction, which is what keeps the existing `StraightStmts` inductions
  untouched.
- **`returnStmt` is terminal here too.** `runStmts` stops at a `return` and
  `lowerStmts` never lowers the tail, so `BranchStmts` does not constrain that
  tail either. This is exactly why `returnStmt` is a `BranchStmts` constructor
  rather than a `BranchStep`: a terminal shape is not a step.
- **Arms have their own grammar** (`ArmStmts`): an arm may evaluate expressions,
  nest `if`s, and `return`, but it may **not** declare or assign
  (`varDecl`/`assign`). An arm that rebinds changes the register file, and the
  join point would then need one phi *per merged binding*, not just the value
  phi. That is C2c; until it exists the lowering must refuse such arms, and this
  grammar is where it refuses them (`lowerStmtsCFG` returns `none` inside an
  arm, exactly like `lowerExpr` does outside the expression fragment).

**The lowering** (`lowerStmtsCFG`, `lowerProgramCFG`). Blocks are produced by a
worker that fills one caller-owned block and returns the rest:

    entry:  <condition instructions>   branch vc, then, else
    then:   <arm>                      goto join        (or `return`, if the arm returned)
    else:   <arm>                      goto join
    join:   phi vm then v_then
            phi vm else v_else
            <rest of the statement list, in the join block>
            return vm

`cont` decides what a completed statement list does: `none` returns the
accumulated value (the program body), `some b` jumps to the join block (an arm,
or the rest of a body after a nested `if`). `arm` is the flag that makes an arm
refuse to bind. One supply counter is threaded through both arms, so the two
sides cannot allocate the same register.

Nothing here proves anything about the lowering; C3 is that theorem. What this
file does provide, at compile time, is that the lowering produces the shapes the
proof will be written against, and that the executor runs them.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-! ## The statement grammars: now in `Morph.Proofs.Branch.Fragments` -/

/- The fragment leaf holds `VarFree`, `ArmStmts`, `BindArmStmts`
(Phase A), `ArmStmts_to_BindArmStmts`, `ArmNoBreak`,
`HFlow_replace_ne_broke`, `ArmNoBreak_run`, the
`BranchStep`/`BranchStmts` mutual block, `LoopStmts`,
`straightStmts_to_branch`, and `LoopStmts_to_BranchStmts`
(L0 proof crate: `Core`/`Total` only). This module imports it back. -/

/-! ## Fuel: now in `Morph.Proofs.Branch.Fuel` -/

/- The fuel leaf holds `armBlockBound`, `blockBound`, and the `eq_def`
rewrite lemmas plus the cons/elim helpers (L0 proof crate: `Core`/`Total`
only). This module imports it back. -/

/-! ## Loop helpers (C7a): now in `Morph.Proofs.Branch.LoopAlloc` -/

/- The loop-allocation leaf holds `assignedIds`, `dedupIds`, `LoopInfo`,
`carryCopies`, `mkCarried` plus growth proofs, and `mkHeaderPhis`
(L0 proof crate: `Core`/`Total` only). This module imports it back. -/

/-! ## Arm-merge helpers (C2c groundwork): now in `Morph.Proofs.Branch.Merge` -/

/- The merge leaf holds `mergeIds`, `rhoLookup_some_of_mem`,
`mergeIds_mem_lookup`, `mkMergePhis`, `mkMergePhis_le`,
`mkMergePhis_growth_fresh`, and `boundIds` (L0 proof crate: `Core`/`Total`
only). This module imports it back; Phase B cites the leaf. -/

/- `mkHeaderPhis` lives in `Morph.Proofs.Branch.LoopAlloc`. -/

/-! ## The lowering: now in `Morph.HIRToMIRLower` -/

/- `Lowered`, `lowerStmtsCFG`, and `lowerProgramCFG` live in
`Morph.HIRToMIRLower` (moved verbatim so the `Equations` leaf can cite the
definitions without importing this proof monolith). This module imports it
back; everything below cites the same names in the same namespace. -/

/-! ## C3 infrastructure: now in `Morph.Proofs.Branch.Infra` -/

/- The growth/freshness/`_inv` families, `BranchStep`/`BranchStmts`/`ArmStmts`
inversions, `execBlockFromIn`/`execInstrsFullFromIn` equations, merge/join
executors, and assembly helpers live in the Infra leaf (moved verbatim).
This module imports it back; the workers below cite those names. -/


/-! ## Arm worker: now in `Morph.Proofs.Branch.ArmTotal` -/

/- The fallthrough arm worker (`lowerStmtsCFG_arm_total`) plus the
carried-register / header-phi executor groundwork live in the ArmTotal leaf
(moved verbatim). This module imports it back; the `broke`/`continued`/
loop-body workers below cite those names. -/


/-! ## Arm execution on `break`: now in `Morph.Proofs.Branch.ArmBroke` -/

/- The arm-`break` worker lives in the ArmBroke leaf (moved verbatim).
This module imports it back; the `continued`/loop-body workers below
cite it for breaking arms. -/



/-! ## Arm execution on `continue`: now in `Morph.Proofs.Branch.ArmContinued` -/

/- The arm-`continue` worker lives in the ArmContinued leaf (moved verbatim).
This module imports it back; the loop-body worker below cites it for
continuing arms. -/


/-! ## Loop-body execution: now in `Morph.Proofs.Branch.LoopBodyRun` -/

/- The C7 spine worker (`lowerStmtsCFG_loopBody_run`) lives in the
LoopBodyRun leaf (moved verbatim). This module imports it back;
everything downstream cites it. -/


/-! ## Oracle facts: now in `Morph.Proofs.Branch.Oracle` -/

/- The interpreter-side facts (`runHIRWhile_*` cases, lookup preservation,
eval literals, bind-arm HIR facts) live in the Oracle leaf (moved verbatim).
This module imports it back; the bind-arm workers below cite those names. -/


/-! ## Binding arms: now in `Morph.Proofs.Branch.BindArm` -/

/- The C2c binding-arm family (`bindArm_rho_agree`, `_inv`, `_fresh`, the
join executors, `bindArm_grows`, `bindArm_total`) lives in the BindArm leaf
(moved verbatim). This module imports it back; everything downstream cites
those names. -/


/-! ## Loop-body lookup preservation: now in `Morph.Proofs.Branch.LoopLookup` -/

/- The `LoopBodyLookupAux` section and its followers live in the LoopLookup
leaf (moved verbatim). This module imports it back; the spine lemmas below
cite those names. -/


/-! ## Spine: now in `Morph.Proofs.Branch.Spine` -/

/- `spine_P` through `header_loop_correct` live in the Spine leaf (moved
verbatim). This module imports it back; `whileLoop_correct` cites those
names. -/


/-! ## Loop execution core: now in `Morph.Proofs.Branch.WhileLoop` -/

/- `whileLoop_correct` (with its design NOTE) lives in the WhileLoop leaf
(moved verbatim). This module imports it back; `lowerStmtsCFG_total`'s
`whileStmt` case cites exactly that interface. -/


/-! ## The body worker: now in `Morph.Proofs.Branch.Total` -/

/- `lowerStmtsCFG_total` lives in the Total leaf (moved verbatim). This
module imports it back; the binding-arm `if` worker below cites it for
the merged-env tail. -/


/-! ## The binding-arm `if` worker: now in `Morph.Proofs.Branch.IfTotal` -/

/- `lowerStmtsCFG_bindArm_if_total` lives in the IfTotal leaf (moved
verbatim). This module imports it back; the closed top-level wrapper
below discharges its worker contracts via `bindArm_total`. -/


/-- Closed top-level binding-arm `if` (C2c integration): `bindArm_if_total`
with both worker contracts discharged by `bindArm_total`. The then-arm rides
the cond's supply step; the else-arm's freshness is part of its contract. -/
theorem lowerStmtsCFG_bindArm_if_closed (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (c : HIR.Expr) (th el rest : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none
        (.ifStmt c th el :: rest) = some L →
      IsStraight c → SLWeight c < budget →
      BindArmStmts budget th → BindArmStmts budget el →
      BranchStmts budget rest →
      FreshAbove ρ supply → lastVal < supply → bId < nextB →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      accH = .unit →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv (.ifStmt c th el :: rest) (.value (.lit accH)) =
        (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId)
        (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB : Nat), F ≥ blockBound fuelB (.ifStmt c th el :: rest) →
        fuelH ≤ fuelB →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_e) := by
  intro bId ρ supply nextB lastVal hasVal c th el rest L h hstr hlt hTh hEl
    hrs hfresh hlast hltB accH henv fenv hrel hacc haccU fuelH henv' out hrun
    prog f prev F hsub hnodf fuelB hg hfb u
  refine lowerStmtsCFG_bindArm_if_total budget bId ρ supply nextB lastVal
    hasVal c th el rest L h hstr hlt hTh hEl hrs hfresh hlast hltB accH henv
    fenv hrel hacc haccU fuelH henv' out hrun prog f prev F hsub hnodf fuelB
    hg hfb ?_ ?_ u
  · intro s1 lt exitT ht' hexit joinBlock hfindJb fenvC F1 C hrelC hg1 fh
      henvArm outArm hrunT hs1T hsubT hregT
    have hf1 : FreshAbove ρ s1 :=
      FreshAbove.mono ρ supply s1 hs1T hfresh
    have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1T
    have hT := lowerStmtsCFG_bindArm_total budget nextB (nextB + 2) ρ s1
      (nextB + 3) lastVal false th lt ht' hTh hf1 hlast1 .unit henv fenvC
      hrelC (fun _ => rfl) hregT fh henvArm outArm hrunT prog f (some bId)
      joinBlock F1 hsubT hnodf hfindJb fuelB C hg1
    refine ⟨fun uArm hout => ?_, fun e hout2 => (hT e).2 e hout2⟩
    obtain ⟨w, hu, F', fenvT, hle, hge, heq, hrelA, hval⟩ := (hT uArm).1 hout
    rw [hexit] at heq
    exact ⟨w, fenvT, F', hu, hle, hge, heq, hrelA, hval⟩
  · intro s1t ltE s1e le exitE he'T he'E hexitE joinBlock hfindJb fenvC F1 C hrelC
      hg1 fh henvArm outArm hrunE hsubE hfE hlE hregE
    have hE := lowerStmtsCFG_bindArm_total budget (nextB + 1) (nextB + 2) ρ
      s1e ltE.next lastVal false el le he'E hEl hfE hlE .unit henv fenvC hrelC
      (fun _ => rfl) hregE fh henvArm outArm hrunE prog f (some bId) joinBlock
      F1 hsubE hnodf hfindJb fuelB C hg1
    refine ⟨fun uArm hout => ?_, fun e hout2 => (hE e).2 e hout2⟩
    obtain ⟨w, hu, F', fenvT, hle, hge, heq, hrelA, hval⟩ := (hE uArm).1 hout
    rw [hexitE] at heq
    exact ⟨w, fenvT, F', hu, hle, hge, heq, hrelA, hval⟩

/-! ## §4.4: the fuel bound, and closed programs

Loop 180. The worker leaves `F` and `fuelB` free; the bridge only needs one
instantiation: `F := blockBound fuelH ss` with `fuelB := fuelH`, closed by
`Nat.le_refl`. C7 cites this corollary, never the worker. -/
theorem lowerStmtsCFG_total_bound (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none ss = some L →
      BranchStmts budget ss →
      FreshAbove ρ supply → lastVal < supply → bId < nextB →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog (blockBound fuelH ss) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog (blockBound fuelH ss) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_e) := by
  intro bId ρ supply nextB lastVal hasVal ss L h hss hfresh hlast hltB
    accH henv fenv hrel hacc fuelH henv' out hrun prog f prev hsub hnodf u
  exact lowerStmtsCFG_total budget bId ρ supply nextB lastVal hasVal ss L
    h hss hfresh hlast hltB accH henv fenv hrel hacc fuelH henv' out hrun prog f
    prev (blockBound fuelH ss) hsub hnodf fuelH
    (Nat.le_refl (blockBound fuelH ss)) (Nat.le_refl fuelH) u

/-- Binding `if` fuel closure (§4.4, C2c): `bindArm_if_closed` at
`F := blockBound fuelH` with `fuelB := fuelH`. C7 cites this, never the worker. -/
theorem lowerStmtsCFG_bindArm_if_closed_bound (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (c : HIR.Expr) (th el rest : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none
        (.ifStmt c th el :: rest) = some L →
      IsStraight c → SLWeight c < budget →
      BindArmStmts budget th → BindArmStmts budget el →
      BranchStmts budget rest →
      FreshAbove ρ supply → lastVal < supply → bId < nextB →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      accH = .unit →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv (.ifStmt c th el :: rest) (.value (.lit accH)) =
        (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog (blockBound fuelH (.ifStmt c th el :: rest)) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog (blockBound fuelH (.ifStmt c th el :: rest)) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_e) := by
  intro bId ρ supply nextB lastVal hasVal c th el rest L h hstr hlt hTh hEl
    hrs hfresh hlast hltB accH henv fenv hrel hacc haccU fuelH henv' out hrun
    prog f prev hsub hnodf u
  exact lowerStmtsCFG_bindArm_if_closed budget bId ρ supply nextB lastVal
    hasVal c th el rest L h hstr hlt hTh hEl hrs hfresh hlast hltB accH henv
    fenv hrel hacc haccU fuelH henv' out hrun prog f prev
    (blockBound fuelH (.ifStmt c th el :: rest)) hsub hnodf fuelH
    (Nat.le_refl (blockBound fuelH (.ifStmt c th el :: rest)))
    (Nat.le_refl fuelH) u

/-- Static invariant for a top-level binding-arm `if` (C2c): the `bindArm_inv`
conclusion for the `.ifStmt c th el :: rest` shape at top level
(`cont = none`, `arm = false`). Arms ride `bindArm_inv`; the tail rides
`branch_inv` (empty merge) or `branch_inv` under the merged env (merge path,
supply via `mkMergePhis_le`). Block assembly is identical on both paths, so
bounds/nodup mirror `bindArm_inv`'s `if` case. The program-level binding-arm
corollary cites this for `hnodf`/`hbnd`. -/
theorem lowerStmtsCFG_bindArm_if_top_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (c : HIR.Expr) (th el rest : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none
        (.ifStmt c th el :: rest) = some L →
      BindArmStmts budget th → BindArmStmts budget el →
      BranchStmts budget rest →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId ρ supply nextB lastVal hasVal c th el rest L h hTh hEl hrs
  simp only [lowerStmtsCFG] at h
  cases heC : lowerExpr ρ supply c with
  | none => rw [heC] at h; simp at h
  | some p =>
      obtain ⟨vc, ic, s1⟩ := p
      rw [heC] at h
      simp only [] at h
      cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
          (nextB + 3) lastVal false none th with
      | none => rw [ht] at h; simp at h
      | some lt =>
          rw [ht] at h
          simp only [] at h
          cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
              lt.supply lt.next lastVal false none el with
          | none => rw [he] at h; simp at h
          | some le =>
              rw [he] at h
              simp only [] at h
              obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ ht hTh
              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ he hEl
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
              cases hm : mergeIds ρ lt.ρ le.ρ with
              | nil =>
                  rw [hm] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) none false ρ
                      (le.supply + 1) le.next le.supply true none rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      dsimp only at ⊢
                      obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                        lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _ _ _
                          _ hr hrs
                      refine ⟨by omega, by omega, ?_, ?_⟩
                      · intro b hb
                        simp only [List.mem_append, List.mem_singleton] at hb
                        rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                        · obtain ⟨hlo, hhi⟩ := hbndt b hb
                          exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                              (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                        · exact ⟨Nat.le_refl _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · obtain ⟨hlo, hhi⟩ := hbnde b hb
                          exact ⟨Nat.le_trans (Nat.le_trans
                              (Nat.le_add_right _ _) hmnt) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                              (Nat.le_succ _))⟩
                        · exact ⟨Nat.le_succ _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_trans (Nat.le_succ _)
                                  (Nat.le_succ _)) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · exact ⟨Nat.le_add_right _ _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_succ _) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · obtain ⟨hlo, hhi⟩ := hbndr b hb
                          exact ⟨Nat.le_trans (Nat.le_trans
                              (Nat.le_trans (Nat.le_add_right _ _)
                                hmnt) hmne) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                      · exact if_assembly_nodup (A := lt.blocks)
                          (B := le.blocks) (C := lr.blocks)
                          (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                          (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                          (joinB := ⟨nextB + 2,
                            [Instr.phi le.supply ((lt.blocks.getLast?.map
                              (fun b => b.id)).getD nextB) lt.val,
                             Instr.phi le.supply ((le.blocks.getLast?.map
                              (fun b => b.id)).getD (nextB + 1)) le.val] ++
                              lr.instrs,
                            lr.term⟩)
                          hmnt hmne hmnr hbndt hbnde hbndr
                          rfl rfl rfl hnodt hnode hnodr
              | cons hd tl =>
                  rw [hm] at h
                  simp only [] at h
                  cases hmk : mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                      ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                      ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                      (hd :: tl) with
                  | none => rw [hmk] at h; simp at h
                  | some q =>
                      obtain ⟨mphis, s2, ρm⟩ := q
                      rw [hmk] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) none false ρm
                          s2 le.next le.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          have hle2 : le.supply + 1 ≤ s2 :=
                            mkMergePhis_le hmk
                          obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                            lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _ _ _
                              _ hr hrs
                          refine ⟨by omega, by omega, ?_, ?_⟩
                          · intro b hb
                            simp only [List.mem_append, List.mem_singleton] at hb
                            rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                            · obtain ⟨hlo, hhi⟩ := hbndt b hb
                              exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                                  (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                            · exact ⟨Nat.le_refl _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · obtain ⟨hlo, hhi⟩ := hbnde b hb
                              exact ⟨Nat.le_trans (Nat.le_trans
                                  (Nat.le_add_right _ _) hmnt) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                                  (Nat.le_succ _))⟩
                            · exact ⟨Nat.le_succ _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_trans (Nat.le_succ _)
                                      (Nat.le_succ _)) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · exact ⟨Nat.le_add_right _ _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_succ _) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · obtain ⟨hlo, hhi⟩ := hbndr b hb
                              exact ⟨Nat.le_trans (Nat.le_trans
                                  (Nat.le_trans (Nat.le_add_right _ _)
                                    hmnt) hmne) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                          · exact if_assembly_nodup (A := lt.blocks)
                              (B := le.blocks) (C := lr.blocks)
                              (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                              (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                              (joinB := ⟨nextB + 2,
                                [Instr.phi le.supply ((lt.blocks.getLast?.map
                                  (fun b => b.id)).getD nextB) lt.val,
                                 Instr.phi le.supply ((le.blocks.getLast?.map
                                  (fun b => b.id)).getD (nextB + 1)) le.val] ++
                                  mphis ++ lr.instrs,
                                lr.term⟩)
                              hmnt hmne hmnr hbndt hbnde hbndr
                              rfl rfl rfl hnodt hnode hnodr

/-- Top corollary (C3 exit): a closed lowered program runs the oracle's value.
C7 cites this: HIR success (`runHIRProgram = value`) is MIR success
(`execFuncFrom = some`), with executor fuel `blockBound 1024`. The entry
block's `const 0 unit` prologue peels first (supply starts at 1, so register
0 is free); the worker then runs from `L.instrs`. Succeed-direction only:
C7 must not contrapose this for failure. -/
theorem lowerProgramCFG_correct (budget : Nat) (prog : HIR.Program)
    (f : Func) (progM : Program) (hlower : lowerProgramCFG prog = some f)
    (hss : BranchStmts budget prog.stmts) (w : Value)
    (hrun : runHIRProgram prog = .value (.lit w)) :
    execFuncFrom (blockBound 1024 prog.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some w := by
  unfold lowerProgramCFG at hlower
  cases hc : lowerStmtsCFG 0 none false [] 1 1 0 false none prog.stmts with
  | none =>
      simp [hc] at hlower
  | some L =>
      simp [hc] at hlower
      obtain rfl := hlower
      obtain ⟨hmn, hms, hbnd, hnodr⟩ :=
        lowerStmtsCFG_branch_inv budget 0 none [] 1 1 0 false none prog.stmts
          L hc hss
      have hsub : ∀ b ∈ L.blocks, b ∈ (⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks := by
        intro b hb
        exact List.Mem.tail _ (List.mem_reverse.mpr hb)
      have hrev : ∀ (l : List Block), (l.map Block.id).Nodup →
          (l.reverse.map Block.id).Nodup := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons b rest ih =>
            intro h
            rw [List.map_cons, List.nodup_cons] at h
            obtain ⟨hnotin, hnod⟩ := h
            have ihr := ih hnod
            rw [List.reverse_cons, List.map_append, List.map_singleton,
              List.nodup_append]
            refine ⟨ihr, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
            intro a ha x hx
            simp only [List.mem_singleton] at hx
            subst hx
            intro hcon
            have ha' : a ∈ rest.map Block.id := by
              obtain ⟨c, hc_mem, hc_id⟩ := List.mem_map.mp ha
              exact List.mem_map.mpr
                ⟨c, List.mem_reverse.mp hc_mem, hc_id⟩
            exact hnotin (hcon ▸ ha')
      have hmap0 : (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id) =
          0 :: L.blocks.reverse.map Block.id := rfl
      have hnodf : (((⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks).map
          Block.id).Nodup := by
        show (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id).Nodup
        rw [hmap0]
        refine List.nodup_cons.mpr ⟨?_, hrev _ hnodr⟩
        intro hm
        obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hm
        obtain ⟨hlo, -⟩ := hbnd b (List.mem_reverse.mp hb)
        rw [hbid] at hlo
        exact absurd hlo (by decide)
      have hmem_entry : (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ∈
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse :=
        List.Mem.head _
      have hfind_entry : findBlock
          ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ 0 =
          some (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) :=
        findBlock_of_nodup_mem hnodf hmem_entry
      cases hp : runHIRStmts 1024 [] prog.stmts (.value (.lit .unit)) with
      | mk out henv' =>
          have hout : out = .value (.lit w) := by
            have h1 : (runHIRStmts 1024 [] prog.stmts
                (.value (.lit .unit))).1 = .value (.lit w) := hrun
            rw [hp] at h1
            simp only [] at h1
            exact h1
          have hfresh : FreshAbove ([] : List (HIR.Id × ValId)) 1 := by
            intro j u hmem
            exact absurd hmem (by simp)
          have hrel : RelEnv ([] : HEnv) []
              (Env.update (fun _ => none) 0 .unit) := by
            intro id u hlook
            exact absurd hlook (by simp [rhoLookup])
          have hacc : Env.update (fun _ => none : Morph.MIR.Env) 0 .unit 0 =
              some .unit := by
            simp [Env.update]
          have hexec0 : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              [.const 0 .unit] =
              some (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                Store.empty⟩ : FullEnv) := rfl
          have happ : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              ([.const 0 .unit] ++ L.instrs) =
              execInstrsFullFromIn progM none
                (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                  Store.empty⟩ : FullEnv) L.instrs := by
            rw [execInstrsFullFromIn_append, hexec0]
          cases hF : blockBound 1024 prog.stmts with
          | zero =>
              have h1 : blockBound 1024 prog.stmts ≥ 1 := by
                rw [blockBound]; omega
              omega
          | succ F' =>
              have hpeel : execBlockFromIn progM (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none
                  (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    ⟨0, L.instrs, L.term⟩
                    (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                      Store.empty⟩ : FullEnv) :=
                execBlockFromIn_instrs_prefix progM F'
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none 0
                  [.const 0 .unit] L.instrs L.term _ _ happ
              have hrunF : execFuncFrom (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                    ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ := by
                rw [execFuncFrom_eq _ _ _ _ hfind_entry,
                  ← execBlockFromIn_eq]
              obtain ⟨w_u, hu, heq⟩ :=
                (lowerStmtsCFG_total_bound budget 0 [] 1 1 0 false prog.stmts
                  L hc hss hfresh (by decide) (by decide) .unit []
                  (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                    Store.empty⟩ : FullEnv) hrel hacc 1024 henv'
                  out hp progM _ none hsub hnodf (.lit w)).1 hout
              have hw : w = w_u := HIR.Expr.lit.inj hu
              subst hw
              rw [hF] at heq
              exact hrunF.trans (hpeel.trans heq)

/-! ## The lowered CFG runs -/
/-- Top program corollary for a binding-arm `if` head (C2c): a closed lowered
program whose statements are `.ifStmt c th el :: rest` with binding arms runs
the oracle's value. Mirrors `lowerProgramCFG_correct`, citing
`bindArm_if_top_inv` for `hbnd`/`hnodf` and `bindArm_if_closed_bound` for the
run. Succeed-direction only. -/
theorem lowerProgramCFG_bindArm_if_correct (budget : Nat) (prog : HIR.Program)
    (c : HIR.Expr) (th el rest : List HIR.Stmt)
    (hshape : prog.stmts = .ifStmt c th el :: rest)
    (f : Func) (progM : Program) (hlower : lowerProgramCFG prog = some f)
    (hstr : IsStraight c) (hlt : SLWeight c < budget)
    (hTh : BindArmStmts budget th) (hEl : BindArmStmts budget el)
    (hrs : BranchStmts budget rest) (w : Value)
    (hrun : runHIRProgram prog = .value (.lit w)) :
    execFuncFrom (blockBound 1024 prog.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some w := by
  unfold lowerProgramCFG at hlower
  rw [hshape] at hlower
  cases hc : lowerStmtsCFG 0 none false [] 1 1 0 false none
      (.ifStmt c th el :: rest) with
  | none =>
      simp [hc] at hlower
  | some L =>
      simp [hc] at hlower
      obtain rfl := hlower
      obtain ⟨hmn, hms, hbnd, hnodr⟩ :=
        lowerStmtsCFG_bindArm_if_top_inv budget 0 [] 1 1 0 false c th el
          rest L hc hTh hEl hrs
      have hsub : ∀ b ∈ L.blocks, b ∈ (⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks := by
        intro b hb
        exact List.Mem.tail _ (List.mem_reverse.mpr hb)
      have hrev : ∀ (l : List Block), (l.map Block.id).Nodup →
          (l.reverse.map Block.id).Nodup := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons b rest ih =>
            intro h
            rw [List.map_cons, List.nodup_cons] at h
            obtain ⟨hnotin, hnod⟩ := h
            have ihr := ih hnod
            rw [List.reverse_cons, List.map_append, List.map_singleton,
              List.nodup_append]
            refine ⟨ihr, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
            intro a ha x hx
            simp only [List.mem_singleton] at hx
            subst hx
            intro hcon
            have ha' : a ∈ rest.map Block.id := by
              obtain ⟨c, hc_mem, hc_id⟩ := List.mem_map.mp ha
              exact List.mem_map.mpr
                ⟨c, List.mem_reverse.mp hc_mem, hc_id⟩
            exact hnotin (hcon ▸ ha')
      have hmap0 : (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id) =
          0 :: L.blocks.reverse.map Block.id := rfl
      have hnodf : (((⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks).map
          Block.id).Nodup := by
        show (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id).Nodup
        rw [hmap0]
        refine List.nodup_cons.mpr ⟨?_, hrev _ hnodr⟩
        intro hm
        obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hm
        obtain ⟨hlo, -⟩ := hbnd b (List.mem_reverse.mp hb)
        rw [hbid] at hlo
        exact absurd hlo (by decide)
      have hmem_entry : (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ∈
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse :=
        List.Mem.head _
      have hfind_entry : findBlock
          ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ 0 =
          some (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) :=
        findBlock_of_nodup_mem hnodf hmem_entry
      cases hp : runHIRStmts 1024 [] prog.stmts (.value (.lit .unit)) with
      | mk out henv' =>
          rw [hshape] at hp
          have hout : out = .value (.lit w) := by
            have h1 : (runHIRStmts 1024 [] prog.stmts
                (.value (.lit .unit))).1 = .value (.lit w) := hrun
            rw [hshape] at h1
            rw [hp] at h1
            simp only [] at h1
            exact h1
          have hfresh : FreshAbove ([] : List (HIR.Id × ValId)) 1 := by
            intro j u hmem
            exact absurd hmem (by simp)
          have hrel : RelEnv ([] : HEnv) []
              (Env.update (fun _ => none) 0 .unit) := by
            intro id u hlook
            exact absurd hlook (by simp [rhoLookup])
          have hacc : Env.update (fun _ => none : Morph.MIR.Env) 0 .unit 0 =
              some .unit := by
            simp [Env.update]
          have hexec0 : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              [.const 0 .unit] =
              some (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                Store.empty⟩ : FullEnv) := rfl
          have happ : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              ([.const 0 .unit] ++ L.instrs) =
              execInstrsFullFromIn progM none
                (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                  Store.empty⟩ : FullEnv) L.instrs := by
            rw [execInstrsFullFromIn_append, hexec0]
          cases hF : blockBound 1024 (.ifStmt c th el :: rest) with
          | zero =>
              have h1 : blockBound 1024 (.ifStmt c th el :: rest) ≥ 1 := by
                rw [blockBound]; omega
              omega
          | succ F' =>
              have hpeel : execBlockFromIn progM (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none
                  (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    ⟨0, L.instrs, L.term⟩
                    (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                      Store.empty⟩ : FullEnv) :=
                execBlockFromIn_instrs_prefix progM F'
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none 0
                  [.const 0 .unit] L.instrs L.term _ _ happ
              have hrunF : execFuncFrom (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                    ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ := by
                rw [execFuncFrom_eq _ _ _ _ hfind_entry,
                  ← execBlockFromIn_eq]
              obtain ⟨w_u, hu, heq⟩ :=
                (lowerStmtsCFG_bindArm_if_closed_bound budget 0 [] 1 1 0
                  false c th el rest L hc hstr hlt hTh hEl hrs hfresh
                  (by decide) (by decide) .unit []
                  (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                    Store.empty⟩ : FullEnv) hrel hacc rfl 1024 henv'
                  out hp progM _ none hsub hnodf (.lit w)).1 hout
              have hw : w = w_u := HIR.Expr.lit.inj hu
              subst hw
              rw [hF] at heq
              rw [hshape, hF]
              exact hrunF.trans (hpeel.trans heq)


/- These are evidence, not the theorem: the same expression in both arms would pass
even if the phi rule were wrong, so the arms deliberately differ, and the
condition appears in both truth values. -/

/-- `if true { 10 } else { 20 }`. -/
def ifProg : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool true)) [.exprStmt (.lit (.int 10))]
      [.exprStmt (.lit (.int 20))]]⟩

/-- The lowered program is a four-block CFG (entry, then, else, join) plus the
prologue register. -/
example : (lowerProgramCFG ifProg).map (fun f => f.blocks.length) = some 4 := by
  native_decide

/-- `blockBound` agrees with the CFG the lowering produced: the entry block plus
the `if`'s three. This is the arithmetic C3 will cite instead of a literal. -/
example : blockBound 8 ifProg.stmts = 4 := by
  native_decide

/-- A program with no `if` is one block, whatever its length. -/
example :
    blockBound 8 [.exprStmt (.lit (.int 1)), .exprStmt (.lit (.int 2))] = 1 := by
  native_decide

/-- The true arm's value reaches the return. -/
example :
    (lowerProgramCFG ifProg).bind (fun f => execFuncFrom 3 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 10) := by
  native_decide

/-- Flipping the condition takes the other arm — the same program, one
constructor different. -/
def ifProgFalse : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool false)) [.exprStmt (.lit (.int 10))]
      [.exprStmt (.lit (.int 20))]]⟩

example :
    (lowerProgramCFG ifProgFalse).bind
        (fun f => execFuncFrom 3 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 20) := by
  native_decide

/-- The join block really merges: the value returned comes out of the phi, so a
program that uses the `if`'s value after it (`if c { 10 } else { 20 }` then `+ 5`)
evaluates 15. -/
def ifThenAdd : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool true)) [.exprStmt (.lit (.int 10))]
      [.exprStmt (.lit (.int 20))],
    .exprStmt (.binop .add (.lit (.int 0)) (.lit (.int 5)))]⟩

/-- The second statement lowers into the join block, and `runStmts`' accumulator
rule (`acc.replace`) is what makes its value the *last* expression's: 5. The
`if`'s phi is still executed (block 3 begins with it) — the value it merges is
just not the result. -/
example :
    (lowerProgramCFG ifThenAdd).bind
        (fun f => execFuncFrom 3 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 5) := by
  native_decide
/-! ## Binding arms: the merge join (C2c evidence)

The merge path (`mergeIds` non-empty) only fires when an id bound *before*
the `if` is rebound inside an arm: the join carries one `mkMergePhis` phi
per rebound id plus the value phi. A fresh `varDecl` inside an arm is not
in the pre-branch env, so it takes the old join verbatim. These pins cover
the merge join: `x` is declared before, assigned in each arm, and read
after. -/

/-- Binding-arm `if`, true edge: `x` is 10 after the join. -/
def bindIfAssignProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .ifStmt (.lit (.bool true)) [.assign ⟨0, "x"⟩ (.lit (.int 10))]
      [.assign ⟨0, "x"⟩ (.lit (.int 20))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- Same program, false edge: `x` is 20 after the join. -/
def bindIfAssignFalseProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .ifStmt (.lit (.bool false)) [.assign ⟨0, "x"⟩ (.lit (.int 10))]
      [.assign ⟨0, "x"⟩ (.lit (.int 20))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- Four blocks, like the binding-free `if`: the merge phi lives in the join. -/
example : (lowerProgramCFG bindIfAssignProg).map (fun f => f.blocks.length) =
    some 4 := by
  native_decide

/-- The bound agrees: entry plus the `if`'s three. -/
example : blockBound 8 bindIfAssignProg.stmts = 4 := by
  native_decide

/-- The true arm's assignment reaches the trailing read. -/
example :
    (lowerProgramCFG bindIfAssignProg).bind
        (fun f => execFuncFrom 4 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 10) := by
  native_decide

/-- The false arm's assignment reaches the trailing read. -/
example :
    (lowerProgramCFG bindIfAssignFalseProg).bind
        (fun f => execFuncFrom 4 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 20) := by
  native_decide


/-! ## Nested arms: the phi's predecessor

The edge into a join comes from the block that actually jumps there. A flat arm
is one block, so that block is the arm's entry; an arm holding a nested `if`
ends in that `if`'s join instead. Naming the arm's entry unconditionally left the
outer phi unfired, so the join returned an unbound register — a lowering bug
found in loop 161 by trying to *encode* the program, not by any test that ran
the flat shape. These two are the regression tests. -/

/-- An `if` in the then-arm: the outer join takes its value from the inner
join's edge, so the outer phi must name that block. -/
def nestedThenProg : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool true))
      [.ifStmt (.lit (.bool false)) [.exprStmt (.lit (.int 7))]
        [.exprStmt (.lit (.int 8))]]
      [.exprStmt (.lit (.int 9))]]⟩

example :
    (lowerProgramCFG nestedThenProg).bind
        (fun f => execFuncFrom 6 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 8) := by
  native_decide

/-- The same shape in the else-arm, so the fix is not specific to one edge. -/
def nestedElseProg : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool false))
      [.exprStmt (.lit (.int 9))]
      [.ifStmt (.lit (.bool true)) [.exprStmt (.lit (.int 7))]
        [.exprStmt (.lit (.int 8))]]]⟩

example :
    (lowerProgramCFG nestedElseProg).bind
        (fun f => execFuncFrom 6 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 7) := by
  native_decide

/-- The bound counts the nested arm, and only the deeper of the two: 1 (entry)
+ 3 (outer `if`) + 3 (inner `if`, in the then-arm). This is the case a flat
"three per statement" bound would get wrong. -/
example : blockBound 8 nestedThenProg.stmts = 7 := by
  native_decide

/-! ## Loops: the header re-reads the carried registers

A loop body that counts (`x = x + 1` while `x < 2`) only terminates because the
header's condition reads the carried register, not the entry value — lowering
the condition in the pre-loop env froze `x` at 0 and spun until fuel ran out
(loop 181). These two pin the fix. -/

/-- Count to two: declare, loop while below two, read back. -/
def whileCountProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 2)))
      [.assign ⟨0, "x"⟩ (.binop .add (.var ⟨0, "x"⟩) (.lit (.int 1)))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- Four blocks: entry, body, header, exit (plus the prologue register). -/
example : (lowerProgramCFG whileCountProg).map (fun f => f.blocks.length) =
    some 4 := by
  native_decide

/-- The bound charges one body traversal per oracle-fuel unit: 1 (entry) +
(2 + 0) * (8 + 1) (the loop) + 0 (the trailing read). -/
example : blockBound 8 whileCountProg.stmts = 19 := by
  native_decide

/-- The counter reaches 2 — and the bound fuel suffices to run it there. -/
example :
    (lowerProgramCFG whileCountProg).bind
        (fun f => execFuncFrom 19 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 2) := by
  native_decide

/-- `break` leaves the loop: an infinite condition still returns. -/
def whileBreakProg : HIR.Program :=
  ⟨[.whileLoop (.lit (.bool true)) [.break],
    .exprStmt (.lit (.int 5))]⟩

example :
    (lowerProgramCFG whileBreakProg).bind
        (fun f => execFuncFrom 5 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 5) := by
  native_decide

/-- End-to-end loop correctness (C7): the `break` program through the program
corollary. This is the first concrete application of the C7 chain — a manual
fragment witness (the body is one `break`, so no `VarFree` obligation), the
oracle run by `rfl` (the loop breaks on its first iteration), and
`lowerProgramCFG_correct` closing it at `blockBound 1024` fuel. -/
example : ∃ f, lowerProgramCFG whileBreakProg = some f ∧
    execFuncFrom (blockBound 1024 whileBreakProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 5) := by
  have hexec : (lowerProgramCFG whileBreakProg).bind
      (fun f => execFuncFrom 5 f ⟨fun _ => none, Store.empty⟩) ==
      some (.int 5) := by
    native_decide
  have hsome : (lowerProgramCFG whileBreakProg).isSome := by
    cases h : lowerProgramCFG whileBreakProg with
    | none => simp [h] at hexec
    | some f => rfl
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileBreakProg.stmts :=
    .cons (.whileStmt _ _ (.lit _) (by simp [SLWeight]) (.breakStmt [] .nil))
      (.cons (.exprStmt _ (.lit _) (by simp [SLWeight])) .nil)
  have hrun : runHIRProgram whileBreakProg = .value (.lit (.int 5)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileBreakProg f ⟨[]⟩ hf hfrag (.int 5) hrun

end Morph.HIRToMIRCorrect

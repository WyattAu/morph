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


/-! ## The body worker: closed bodies run to the oracle's value

Loop 179. `lowerStmtsCFG_total` is the body counterpart of the arm worker:
with `cont = none` every path ends in `return_`, so both outcomes conclude
`entry-run = some w` and no join formula is needed. Straight-line steps peel
via `lower_total.1` and the instr-prefix bridge; `if` reuses the arm worker
for both arms and the list IH for the tail; `cont` is fixed to `none`
because only closed programs reach the bridge. -/
theorem lowerStmtsCFG_total (budget : Nat) :
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
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId)
        (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB : Nat), F ≥ blockBound fuelB ss → fuelH ≤ fuelB →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_e) := by
  intro bId ρ supply nextB lastVal hasVal ss
  induction ss generalizing bId ρ supply nextB lastVal hasVal with
  | nil =>
      intro L h hss hfresh hlast _hltB
      cases hss with
      | nil =>
          intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
            hsub hnodf fuelB hg hfb
          simp only [lowerStmtsCFG] at h
          obtain rfl := Option.some.inj h
          intro u
          refine ⟨?_, ?_⟩
          · intro hout
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have hu : u = .lit accH := by
                  have h1 : (.value (.lit accH)) = out :=
                    congrArg Prod.fst hrun
                  rw [← h1] at hout
                  exact (HFlow.value.inj hout).symm
                refine ⟨accH, hu, ?_⟩
                cases F with
                | zero =>
                    have hbb : blockBound fuelB ([] : List HIR.Stmt) = 1 := by
                      simp [blockBound]
                    omega
                | succ F' =>
                    have hLHS : execBlockFromIn prog (F' + 1) f prev
                        ⟨bId, [], .return_ lastVal⟩ fenv =
                        fenv.env lastVal := rfl
                    rw [hLHS]
                    exact hacc
          · intro e_ret hout2
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout2
                exact absurd hout2 (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                rw [← h1] at hout2
                exact absurd hout2 (by simp)
  | cons s rest ih =>
      intro L h hss hfresh hlast hltB
      cases hss with
      | cons hs hrs =>
          cases hs with
          | exprStmt e hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false ρ s1 nextB v true
                      none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg hfb
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      have hbb : blockBound fuelB (.exprStmt e :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      have hf1 : FreshAbove ρ s1 :=
                        FreshAbove.mono ρ supply s1 hs1 hfresh
                      have hva : v < s1 :=
                        lower_result_lt.1 ρ supply e v ie s1 he hfresh
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.exprStmt e :: rest) (.value (.lit accH)) =
                              (match evalHIR 256 henv e with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh henv rest
                                    (.value v)) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv e with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply e v ie s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply e v ie s1 he fenv
                                  fenv1 hrel hfresh hexec1
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ie := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ie = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ie ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ie ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ie q.instrs q.term fenv fenv1
                                      happ
                                  have hww : wE = wE2 :=
                                    HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                                  intro u
                                  have hfb' : fh ≤ fuelB := by omega
                                  have hihr := ih bId ρ s1 nextB v true q hr
                                    hrs hf1 hva hltB wE henv fenv1 hrel1
                                    (hww ▸ hregE) fh henv' out hrun prog f
                                    prev (F' + 1) hsub hnodf fuelB hg' hfb' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | varDecl id τ init hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false ((id, vb) :: ρ) s1
                      nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg hfb
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      have hva : vb < s1 :=
                        lower_result_lt.1 ρ supply init vb ib s1 he hfresh
                      have hf1 : FreshAbove ((id, vb) :: ρ) s1 := by
                        intro j u hmem
                        rcases List.mem_cons.mp hmem with heq | hmem
                        · cases heq
                          exact hva
                        · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                      have hbb : blockBound fuelB (.varDecl id τ init :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv
                              (.varDecl id τ init :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.varDecl id τ init :: rest)
                              (.value (.lit accH)) =
                              (match evalHIR 256 henv init with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh ((id, v) :: henv)
                                    rest (.value (.lit accH))) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv init with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply init vb ib s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              have hww : wE = wE2 :=
                                HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply init vb ib s1 he
                                  fenv fenv1 hrel hfresh hexec1
                              have hrel2 : RelEnv ((id, .lit wE) :: henv)
                                  ((id, vb) :: ρ) fenv1.env := by
                                intro j u hlook
                                by_cases hid : id = j
                                · subst hid
                                  have hu : u = vb := by
                                    have hh : rhoLookup ((id, vb) :: ρ) id =
                                        some vb :=
                                      rhoLookup_cons_head id vb ρ
                                    rw [hh] at hlook
                                    exact (Option.some.inj hlook).symm
                                  subst hu
                                  have hhead : lookupHEnv
                                      ((id, .lit wE) :: henv) id =
                                      some (.lit wE) := by
                                    simp [lookupHEnv]
                                  exact ⟨wE, hhead, hww ▸ hregE⟩
                                · have hlook' : rhoLookup ρ j = some u := by
                                    rw [rhoLookup_cons_ne hid] at hlook
                                    exact hlook
                                  obtain ⟨w', hlookH, hreg⟩ :=
                                    hrel1 j u hlook'
                                  have hlookH' : lookupHEnv
                                      ((id, .lit wE) :: henv) j =
                                      some (.lit w') := by
                                    rw [lookupHEnv_cons_ne hid]
                                    exact hlookH
                                  exact ⟨w', hlookH', hreg⟩
                              have hacc1 : fenv1.env lastVal = some accH := by
                                rw [lower_preserv_regs ρ supply init vb ib
                                  s1 he fenv fenv1 hexec1 lastVal hlast]
                                exact hacc
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ib := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ib = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ib ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ib ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ib q.instrs q.term fenv fenv1
                                      happ
                                  intro u
                                  have hfb' : fh ≤ fuelB := by omega
                                  have hihr := ih bId ((id, vb) :: ρ) s1
                                    nextB lastVal true q hr hrs hf1 hlast1 hltB
                                    accH ((id, .lit wE) :: henv) fenv1 hrel2
                                    hacc1 fh henv' out hrun prog f prev
                                    (F' + 1) hsub hnodf fuelB hg' hfb' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | assign id e hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v0, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false (updAssoc ρ id v0)
                      s1 nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg hfb
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      have hva : v0 < s1 :=
                        lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                      have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
                        intro j u hmem
                        rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ |
                          hmem
                        · rw [hwu]
                          exact hva
                        · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                      have hbb : blockBound fuelB (.assign id e :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv (.assign id e :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.assign id e :: rest)
                              (.value (.lit accH)) =
                              (match evalHIR 256 henv e with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh
                                    (updateHEnv henv id v) rest
                                    (.value (.lit accH))) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv e with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply e v0 ie s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              have hww : wE = wE2 :=
                                HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply e v0 ie s1 he fenv
                                  fenv1 hrel hfresh hexec1
                              have hrel2 : RelEnv
                                  (updateHEnv henv id (.lit wE))
                                  (updAssoc ρ id v0) fenv1.env :=
                                RelEnv_update ρ henv fenv1.env id v0 wE
                                  hrel1 (hww ▸ hregE)
                              have hacc1 : fenv1.env lastVal = some accH := by
                                rw [lower_preserv_regs ρ supply e v0 ie s1
                                  he fenv fenv1 hexec1 lastVal hlast]
                                exact hacc
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ie := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ie = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ie ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ie ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ie q.instrs q.term fenv fenv1
                                      happ
                                  intro u
                                  have hfb' : fh ≤ fuelB := by omega
                                  have hihr := ih bId (updAssoc ρ id v0) s1
                                    nextB lastVal true q hr hrs hf1 hlast1 hltB
                                    accH (updateHEnv henv id (.lit wE))
                                    fenv1 hrel2 hacc1 fh henv' out hrun prog
                                    f prev (F' + 1) hsub hnodf fuelB hg' hfb' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | nop =>
              simp only [lowerStmtsCFG] at h
              intro accH henv fenv hrel hacc fuelH henv' out hrun prog f
                prev F hsub hnodf fuelB hg hfb
              have hbb : blockBound fuelB (Morph.HIR.Stmt.nop :: rest)
                  = blockBound fuelB rest := by
                rw [blockBound, blockBound,
                  armBlockBound_cons_not_if fuelB
                    (fun c th el h => by cases h)
                    (fun c body h => by cases h)]
              have hg' : F ≥ blockBound fuelB rest := by
                rw [← hbb]; exact hg
              cases fuelH with
              | zero =>
                  have hz : runHIRStmts 0 henv
                      (Morph.HIR.Stmt.nop :: rest)
                      (.value (.lit accH)) = (.stuck, henv) := rfl
                  rw [hz] at hrun
                  have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                  intro u
                  refine ⟨?_, ?_⟩
                  · intro hout
                    rw [hst] at hout
                    exact absurd hout (by simp)
                  · intro e_ret hout2
                    rw [hst] at hout2
                    exact absurd hout2 (by simp)
              | succ fh =>
                  have hstep : runHIRStmts (fh + 1) henv
                      (Morph.HIR.Stmt.nop :: rest) (.value (.lit accH)) =
                      runHIRStmts fh henv rest (.value (.lit accH)) := rfl
                  rw [hstep] at hrun
                  intro u
                  have hfb' : fh ≤ fuelB := by omega
                  exact ih bId ρ supply nextB lastVal hasVal L h hrs hfresh
                    hlast hltB accH henv fenv hrel hacc fh henv' out hrun prog f
                    prev F hsub hnodf fuelB hg' hfb' u
          | ifStmt c th el hstr _ hath hael =>
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
                      cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                          true ρ lt.supply lt.next lastVal false none el with
                      | none => rw [he] at h; simp at h
                      | some le =>
                          rw [he] at h
                          simp only [] at h
                          -- Phase B: binding-free arms have an empty merge set.
                          have hltρ : lt.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                          have hleρ : le.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                          have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                            rw [hltρ, hleρ]
                            exact mergeIds_self ρ
                          rw [hm] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) none false ρ
                              (le.supply + 1) le.next le.supply true none rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              intro accH henv fenv hrel hacc fuelH henv' out
                                hrun prog f prev F hsub hnodf fuelB hg hfb
                              dsimp only at hsub ⊢
                              generalize hTdef : ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD nextB) = exitT
                              generalize hEdef : ((le.blocks.getLast?.map
                                (fun b => b.id)).getD (nextB + 1)) = exitE
                              rw [hTdef, hEdef] at hsub
                              have hs1 : supply ≤ s1 :=
                                lower_mono.1 _ _ _ _ _ _ heC
                              have hf1 : FreshAbove ρ s1 :=
                                FreshAbove.mono ρ supply s1 hs1 hfresh
                              have hlast1 : lastVal < s1 :=
                                Nat.lt_of_lt_of_le hlast hs1
                              obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                                  ht hath
                              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                                  he hael
                              obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                                lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _
                                  _ _ _ hr hrs
                              have hrho_t : lt.ρ = ρ :=
                                lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _
                                  _ ht hath
                              have hrho_e : le.ρ = ρ :=
                                lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _
                                  _ he hael
                              have hbb_if : blockBound fuelB
                                  (.ifStmt c th el :: rest) =
                                  1 + (3 + max (armBlockBound fuelB th)
                                    (armBlockBound fuelB el) +
                                    armBlockBound fuelB rest) := by
                                rw [blockBound, armBlockBound_if]
                              have hB1 : blockBound fuelB
                                  (.ifStmt c th el :: rest) ≥ 1 := by
                                rw [blockBound]; omega
                              have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                  ∈ f.blocks :=
                                hsub _ if_asm_mem_then
                              have hfindT : findBlock f nextB =
                                  some ⟨nextB, lt.instrs, lt.term⟩ :=
                                findBlock_of_nodup_mem hnodf hTmem
                              have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ :
                                  Block) ∈ f.blocks :=
                                hsub _ if_asm_mem_else
                              have hfindE : findBlock f (nextB + 1) =
                                  some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                findBlock_of_nodup_mem hnodf hEmem
                              have hJmem : (⟨nextB + 2,
                                  [.phi le.supply exitT lt.val,
                                   .phi le.supply exitE le.val] ++ lr.instrs,
                                  lr.term⟩ : Block) ∈ f.blocks :=
                                hsub _ if_asm_mem_join
                              have hfindJ : findBlock f (nextB + 2) =
                                  some ⟨nextB + 2,
                                    [.phi le.supply exitT lt.val,
                                     .phi le.supply exitE le.val] ++ lr.instrs,
                                    lr.term⟩ :=
                                findBlock_of_nodup_mem hnodf hJmem
                              have hne_pe : exitE ≠ exitT := by
                                have hexitT : exitT = nextB ∨
                                    ∃ b ∈ lt.blocks, exitT = b.id := by
                                  cases hgl : lt.blocks.getLast? with
                                  | none =>
                                      exact Or.inl (by simp [← hTdef, hgl])
                                  | some b =>
                                      have hm : b ∈ lt.blocks :=
                                        getLast?_mem hgl
                                      exact Or.inr ⟨b, hm, by simp [← hTdef, hgl]⟩
                                have hexitE : exitE = nextB + 1 ∨
                                    ∃ b ∈ le.blocks, exitE = b.id := by
                                  cases hgl : le.blocks.getLast? with
                                  | none =>
                                      exact Or.inl (by simp [← hEdef, hgl])
                                  | some b =>
                                      have hm : b ∈ le.blocks :=
                                        getLast?_mem hgl
                                      exact Or.inr ⟨b, hm, by simp [← hEdef, hgl]⟩
                                rcases hexitT with hT | ⟨bt, hbt, hT⟩
                                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                                  · simp [hT, hE]
                                  · obtain ⟨hlo, -⟩ := hbnde be hbe
                                    rw [hE, hT]
                                    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le
                                      (by omega)
                                      (Nat.le_trans hmnt hlo))
                                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                                  · obtain ⟨hlo, -⟩ := hbndt bt hbt
                                    rw [hE, hT]
                                    exact Nat.ne_of_lt (Nat.lt_of_le_of_lt
                                      (Nat.add_le_add_left (by decide) nextB)
                                      hlo)
                                  · obtain ⟨-, hhi⟩ := hbndt bt hbt
                                    obtain ⟨hlo, -⟩ := hbnde be hbe
                                    rw [hE, hT]
                                    exact Nat.ne_of_gt
                                      (Nat.lt_of_lt_of_le hhi hlo)
                              have hgF : F ≥ 1 + (3 + max (armBlockBound fuelB
                                  th) (armBlockBound fuelB el) +
                                  armBlockBound fuelB rest) := by
                                rw [← hbb_if]; exact hg
                              cases F with
                              | zero => omega
                              | succ F'' =>
                                  cases fuelH with
                                  | zero =>
                                      have hz : runHIRStmts 0 henv
                                          (.ifStmt c th el :: rest)
                                          (.value (.lit accH)) =
                                          (.stuck, henv) := rfl
                                      rw [hz] at hrun
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | succ fh =>
                                      have hstep : runHIRStmts (fh + 1) henv
                                          (.ifStmt c th el :: rest)
                                          (.value (.lit accH)) =
                                          (match evalHIR 256 henv c with
                                            | some (.lit (.bool true)) =>
                                              match runHIRStmts fh henv th
                                                  (HFlow.value (.lit .unit)) with
                                              | (HFlow.value u, env') =>
                                                  runHIRStmts fh env' rest
                                                    ((HFlow.value
                                                      (.lit accH)).replace u)
                                              | (f, env') => (f, env')
                                            | some (.lit (.bool false)) =>
                                              match runHIRStmts fh henv el
                                                  (HFlow.value (.lit .unit)) with
                                              | (HFlow.value u, env') =>
                                                  runHIRStmts fh env' rest
                                                    ((HFlow.value
                                                      (.lit accH)).replace u)
                                              | (f, env') => (f, env')
                                            | _ => (.stuck, henv)) := rfl
                                      rw [hstep] at hrun
                                      cases hevC : evalHIR 256 henv c with
                                      | none =>
                                          rw [hevC] at hrun
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          intro u
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hst] at hout
                                          · intro e hout
                                            simp [hst] at hout
                                      | some r =>
                                          rw [hevC] at hrun
                                          obtain ⟨⟨w, hrw⟩, fenvC, hexecC,
                                              hstoreC, wC, hrC, hregC⟩ :=
                                            lower_total.1 ρ supply c vc ic s1
                                              heC hstr hfresh henv fenv hrel
                                              256 r hevC
                                          subst hrw
                                          have hnp_ic : ∀ dst pred src,
                                              .phi dst pred src ∉ ic := by
                                            intro d p s hm
                                            exact IsPure_not_phi
                                              (lower_isPure.1 _ _ _ _ _ _ heC
                                                _ hm) d p s rfl
                                          have hexec_ic : execInstrsFullFromIn
                                              prog prev fenv ic =
                                              some fenvC := by
                                            rw [execInstrsFullFromIn_of_noPhi
                                              prog prev fenv _ hnp_ic]
                                            exact hexecC
                                          have hrelC : RelEnv henv ρ
                                              fenvC.env :=
                                            RelEnv_exec henv ρ supply c vc ic
                                              s1 heC fenv fenvC hrel hfresh
                                              hexecC
                                          cases w with
                                          | bool b =>
                                              cases b with
                                              | true =>
                                                  simp only [] at hrun
                                                  cases har : runHIRStmts fh
                                                      henv th (HFlow.value
                                                        (.lit .unit)) with
                                                  | mk out_arm env_arm =>
                                                      rw [har] at hrun
                                                      cases out_arm with
                                                      | value u_arm =>
                                                          simp only [] at hrun
                                                          have hregCb :
                                                              fenvC.env vc =
                                                              some
                                                              (.bool true) := by
                                                            have hww :
                                                                (.bool true) =
                                                                wC :=
                                                              HIR.Expr.lit.inj
                                                                hrC
                                                            rw [hww]
                                                            exact hregC
                                                          have hbool :
                                                              fenvC.boolOf vc =
                                                              some true :=
                                                            boolOf_of_lit fenvC
                                                              vc true hregCb
                                                          have hentry :
                                                              execBlockFromIn
                                                              prog (F'' + 1) f
                                                              prev ⟨bId, ic,
                                                              .branch vc nextB
                                                              (nextB + 1)⟩
                                                              fenv =
                                                              execBlockFromIn
                                                              prog F'' f
                                                              (some bId)
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ fenvC :=
                                                            execBlockFromIn_branch_true
                                                              prog F'' f prev
                                                              bId ic vc nextB
                                                              (nextB + 1) fenv
                                                              fenvC
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ hexec_ic
                                                              hbool hfindT
                                                          have hsub_t : ∀ b ∈
                                                              lt.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lt
                                                              hb)
                                                          have hCtge : (2 + max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) ≥
                                                              blockBound fuelB
                                                              rest := by
                                                            have hBrest :
                                                                blockBound fuelB
                                                                rest = 1 +
                                                                armBlockBound
                                                                fuelB rest :=
                                                              rfl
                                                            omega
                                                          have hg_t : F'' ≥
                                                              blockBound fuelB
                                                              th + (2 + max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) := by
                                                            have hBth :
                                                                blockBound fuelB
                                                                th = 1 +
                                                                armBlockBound
                                                                fuelB th := rfl
                                                            omega
                                                          obtain ⟨w_arm, hu_arm,
                                                              F', fenv_arr, hle,
                                                              hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arr, _⟩ :=
                                                            ((lowerStmtsCFG_arm_total
                                                              budget nextB
                                                              (nextB + 2) ρ s1
                                                              (nextB + 3)
                                                              lastVal false none th
                                                              lt ht hath hf1
                                                              hlast1 .unit henv
                                                              fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp))
                                                              fh env_arm
                                                              (HFlow.value
                                                              u_arm) har prog f
                                                              (some bId)
                                                              ⟨nextB + 2,
                                                              [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ F''
                                                              hsub_t hnodf
                                                              hfindJ fuelB (2 +
                                                              max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) hg_t
                                                              u_arm).1 rfl)
                                                          rw [hTdef] at heq_arm
                                                          rw [hrho_t] at hrel_arm
                                                          have hrep :
                                                              ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit w_arm)) =
                                                              HFlow.value
                                                              (.lit w_arm) :=
                                                            rfl
                                                          rw [hu_arm, hrep] at hrun
                                                          have hfrL : FreshAbove
                                                              ρ le.supply :=
                                                            FreshAbove.mono ρ
                                                              supply le.supply
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              hmse)) hfresh
                                                          have hrel_m : RelEnv
                                                              env_arm ρ
                                                              (fenv_arr.env.update
                                                              le.supply
                                                              w_arm) := by
                                                            intro id u hlook
                                                            obtain ⟨w0, hlookH,
                                                              hreg0⟩ :=
                                                              hrel_arm id u
                                                              hlook
                                                            have hu : u <
                                                                le.supply :=
                                                              hfrL id u
                                                              (rhoLookup_some_mem
                                                              ρ id u hlook)
                                                            have hne : u ≠
                                                                le.supply :=
                                                              Nat.ne_of_lt hu
                                                            refine ⟨w0, hlookH,
                                                              ?_⟩
                                                            have hupd :
                                                                (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                                fenv_arr.env
                                                                u := by
                                                              simp [Env.update,
                                                                hne]
                                                            show (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                              some w0
                                                            rw [hupd]
                                                            exact hreg0
                                                          have hreg_m :
                                                              (⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :
                                                              FullEnv).env
                                                              le.supply =
                                                              some w_arm := by
                                                            simp [Env.update]
                                                          have hf_r : FreshAbove
                                                              ρ (le.supply +
                                                              1) :=
                                                            FreshAbove.mono ρ
                                                              supply
                                                              (le.supply + 1)
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              (Nat.le_trans hmse
                                                              (Nat.le_succ _))))
                                                              hfresh
                                                          have hlast_r :
                                                              le.supply <
                                                              le.supply + 1 :=
                                                            Nat.lt_succ_self _
                                                          have hsub_r : ∀ b ∈
                                                              lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lr
                                                              hb)
                                                          cases F' with
                                                          | zero =>
                                                              have hB1r :
                                                                  blockBound
                                                                  fuelB rest ≥
                                                                  1 := by
                                                                rw [blockBound]
                                                                omega
                                                              exact absurd hge
                                                                (by omega)
                                                          | succ F1 =>
                                                              have happ_J :
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitT)
                                                                  fenv_arr
                                                                  ([.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs) =
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitT)
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  lr.instrs :=
                                                                execInstrsFullFromIn_phis_hit
                                                                  prog exitT
                                                                  fenv_arr
                                                                  le.supply
                                                                  exitT exitE
                                                                  lt.val le.val
                                                                  lr.instrs
                                                                  w_arm rfl
                                                                  hne_pe
                                                                  hreg_arr
                                                              have hJeq :
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitT)
                                                                  ⟨nextB + 2,
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  fenv_arr =
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitT)
                                                                  ⟨nextB + 2,
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩ :=
                                                                execBlockFromIn_instrs_prefix
                                                                  prog F1 f
                                                                  (some exitT)
                                                                  (nextB + 2)
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val]
                                                                  lr.instrs
                                                                  lr.term
                                                                  fenv_arr
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  happ_J
                                                              have hg_r : F1 + 1 ≥
                                                                  blockBound
                                                                  fuelB rest :=
                                                                Nat.le_trans hCtge
                                                                  hge
                                                              intro u
                                                              have hfb' : fh ≤ fuelB := by omega
                                                              have hltB' : nextB + 2 < le.next := by
                                                                have h1 : nextB + 3 ≤ lt.next := hmnt
                                                                have h2 : lt.next ≤ le.next := hmne
                                                                omega
                                                              have hihr := ih
                                                                (nextB + 2) ρ
                                                                (le.supply + 1)
                                                                le.next
                                                                le.supply true
                                                                lr hr hrs hf_r
                                                                hlast_r hltB' w_arm
                                                                env_arm
                                                                ⟨fenv_arr.env.update
                                                                le.supply w_arm,
                                                                fenv_arr.store⟩
                                                                hrel_m hreg_m fh
                                                                henv' out hrun
                                                                prog f
                                                                (some exitT)
                                                                (F1 + 1) hsub_r
                                                                hnodf fuelB hg_r hfb'
                                                                u
                                                              refine ⟨?_, ?_⟩
                                                              · intro hout
                                                                obtain ⟨w_u, hu,
                                                                    heq_rest⟩ :=
                                                                  hihr.1 hout
                                                                exact ⟨w_u, hu,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                              · intro e_ret hout2
                                                                obtain ⟨w_e, hu_e,
                                                                    heq_rest⟩ :=
                                                                  hihr.2 e_ret
                                                                    hout2
                                                                exact ⟨w_e, hu_e,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                      | returned e_arm =>
                                                          simp only [] at hrun
                                                          have hout_r : out =
                                                              .returned e_arm :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_r] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            have hret_e : e_ret =
                                                                e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                hout2)).symm
                                                            have hregCb_r :
                                                                fenvC.env vc =
                                                                some
                                                                (.bool true) := by
                                                              have hww :
                                                                  (.bool true) =
                                                                  wC :=
                                                                HIR.Expr.lit.inj
                                                                  hrC
                                                              rw [hww]
                                                              exact hregC
                                                            have hbool_r :
                                                                fenvC.boolOf vc =
                                                                some true :=
                                                              boolOf_of_lit
                                                                fenvC vc true
                                                                hregCb_r
                                                            have hentry_r :
                                                                execBlockFromIn
                                                                prog (F'' + 1)
                                                                f prev ⟨bId, ic,
                                                                .branch vc
                                                                nextB
                                                                (nextB + 1)⟩
                                                                fenv =
                                                                execBlockFromIn
                                                                prog F'' f
                                                                (some bId)
                                                                ⟨nextB, lt.instrs,
                                                                lt.term⟩
                                                                fenvC :=
                                                              execBlockFromIn_branch_true
                                                                prog F'' f prev
                                                                bId ic vc nextB
                                                                (nextB + 1)
                                                                fenv fenvC
                                                                ⟨nextB,
                                                                lt.instrs,
                                                                lt.term⟩
                                                                hexec_ic
                                                                hbool_r hfindT
                                                            have hsub_tr : ∀ b ∈
                                                                lt.blocks,
                                                                b ∈ f.blocks :=
                                                              fun b hb => hsub _
                                                                (if_asm_mem_of_lt
                                                                hb)
                                                            have hCtge_r : (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) ≥
                                                                blockBound fuelB
                                                                rest := by
                                                              have hBrest :
                                                                  blockBound
                                                                  fuelB rest =
                                                                  1 +
                                                                  armBlockBound
                                                                  fuelB rest :=
                                                                rfl
                                                              omega
                                                            have hg_tr : F'' ≥
                                                                blockBound fuelB
                                                                th + (2 + max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) := by
                                                              have hBth :
                                                                  blockBound
                                                                  fuelB th = 1 +
                                                                  armBlockBound
                                                                  fuelB th :=
                                                                rfl
                                                              omega
                                                            obtain ⟨w_e, heq,
                                                                hexec_arm⟩ :=
                                                              ((lowerStmtsCFG_arm_total
                                                                budget nextB
                                                                (nextB + 2) ρ s1
                                                                (nextB + 3)
                                                                lastVal false none th
                                                                lt ht hath hf1
                                                                hlast1 .unit henv
                                                                fenvC hrelC
                                                                (fun _ => rfl)
                                                                (fun h => absurd h
                                                                (by simp))
                                                                fh env_arm
                                                                (HFlow.returned
                                                                e_arm)
                                                                har prog f
                                                                (some bId)
                                                                ⟨nextB + 2,
                                                                [.phi le.supply
                                                                exitT lt.val,
                                                                .phi le.supply
                                                                exitE le.val] ++
                                                                lr.instrs,
                                                                lr.term⟩ F''
                                                                hsub_tr hnodf
                                                                hfindJ fuelB (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) hg_tr
                                                                (.lit .unit)).2
                                                                e_arm rfl)
                                                            exact ⟨w_e,
                                                              hret_e.trans heq,
                                                              hentry_r.trans
                                                              hexec_arm⟩
                                                      | stuck =>
                                                          simp only [] at hrun
                                                          have hout_s : out =
                                                              .stuck :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_s] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_s] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | broke =>
                                                          simp only [] at hrun
                                                          have hout_b : out =
                                                              .broke :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_b] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_b] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | continued =>
                                                          simp only [] at hrun
                                                          have hout_c : out =
                                                              .continued :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_c] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_c] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                              | false =>
                                                  simp only [] at hrun
                                                  have hregCb : fenvC.env vc =
                                                      some (.bool false) := by
                                                    have hww : (.bool false) =
                                                        wC :=
                                                      HIR.Expr.lit.inj hrC
                                                    rw [hww]
                                                    exact hregC
                                                  have hbool : fenvC.boolOf vc =
                                                      some false :=
                                                    boolOf_of_lit fenvC vc false
                                                      hregCb
                                                  have hentry : execBlockFromIn
                                                      prog (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc
                                                      nextB (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                        (some bId)
                                                        ⟨nextB + 1, le.instrs,
                                                        le.term⟩ fenvC :=
                                                    execBlockFromIn_branch_false
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC
                                                      ⟨nextB + 1, le.instrs,
                                                      le.term⟩ hexec_ic hbool
                                                      hfindE
                                                  have hsub_e : ∀ b ∈ le.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_le hb)
                                                  have hf_e : FreshAbove ρ
                                                      lt.supply :=
                                                    FreshAbove.mono ρ s1
                                                      lt.supply hmst hf1
                                                  have hlast_e : lastVal <
                                                      lt.supply :=
                                                    Nat.lt_of_lt_of_le hlast1
                                                      hmst
                                                  have hCege : (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el) ≥
                                                      blockBound fuelB rest := by
                                                    have hBrest : blockBound
                                                        fuelB rest = 1 +
                                                        armBlockBound fuelB
                                                          rest := rfl
                                                    omega
                                                  have hg_e : F'' ≥ blockBound
                                                      fuelB el + (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el) := by
                                                    have hBel : blockBound
                                                        fuelB el = 1 +
                                                        armBlockBound fuelB
                                                          el := rfl
                                                    omega
                                                  cases har : runHIRStmts fh
                                                      henv el (HFlow.value
                                                        (.lit .unit)) with
                                                  | mk out_arm env_arm =>
                                                      rw [har] at hrun
                                                      cases out_arm with
                                                      | value u_arm =>
                                                          simp only [] at hrun
                                                          obtain ⟨w_arm, hu_arm,
                                                              F', fenv_arr, hle,
                                                              hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arr, _⟩ :=
                                                            ((lowerStmtsCFG_arm_total
                                                              budget (nextB + 1)
                                                              (nextB + 2) ρ
                                                              lt.supply lt.next
                                                              lastVal false none el
                                                              le he hael hf_e
                                                              hlast_e .unit henv
                                                              fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp))
                                                              fh env_arm
                                                              (HFlow.value
                                                              u_arm) har prog f
                                                              (some bId)
                                                              ⟨nextB + 2,
                                                              [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ F''
                                                              hsub_e hnodf
                                                              hfindJ fuelB (2 +
                                                              max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB el) hg_e
                                                              u_arm).1 rfl)
                                                          rw [hEdef] at heq_arm
                                                          rw [hrho_e] at hrel_arm
                                                          have hrep :
                                                              ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit w_arm)) =
                                                              HFlow.value
                                                              (.lit w_arm) :=
                                                            rfl
                                                          rw [hu_arm, hrep] at hrun
                                                          have hfrL : FreshAbove
                                                              ρ le.supply :=
                                                            FreshAbove.mono ρ
                                                              supply le.supply
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              hmse)) hfresh
                                                          have hrel_m : RelEnv
                                                              env_arm ρ
                                                              (fenv_arr.env.update
                                                              le.supply
                                                              w_arm) := by
                                                            intro id u hlook
                                                            obtain ⟨w0, hlookH,
                                                              hreg0⟩ :=
                                                              hrel_arm id u
                                                              hlook
                                                            have hu : u <
                                                                le.supply :=
                                                              hfrL id u
                                                              (rhoLookup_some_mem
                                                              ρ id u hlook)
                                                            have hne : u ≠
                                                                le.supply :=
                                                              Nat.ne_of_lt hu
                                                            refine ⟨w0, hlookH,
                                                              ?_⟩
                                                            have hupd :
                                                                (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                                fenv_arr.env
                                                                u := by
                                                              simp [Env.update,
                                                                hne]
                                                            show (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                              some w0
                                                            rw [hupd]
                                                            exact hreg0
                                                          have hreg_m :
                                                              (⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :
                                                              FullEnv).env
                                                              le.supply =
                                                              some w_arm := by
                                                            simp [Env.update]
                                                          have hf_r : FreshAbove
                                                              ρ (le.supply +
                                                              1) :=
                                                            FreshAbove.mono ρ
                                                              supply
                                                              (le.supply + 1)
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              (Nat.le_trans hmse
                                                              (Nat.le_succ _))))
                                                              hfresh
                                                          have hlast_r :
                                                              le.supply <
                                                              le.supply + 1 :=
                                                            Nat.lt_succ_self _
                                                          have hsub_r : ∀ b ∈
                                                              lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lr
                                                              hb)
                                                          cases F' with
                                                          | zero =>
                                                              have hB1r :
                                                                  blockBound
                                                                  fuelB rest ≥
                                                                  1 := by
                                                                rw [blockBound]
                                                                omega
                                                              exact absurd hge
                                                                (by omega)
                                                          | succ F1 =>
                                                              have happ_J :
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitE)
                                                                  fenv_arr
                                                                  ([.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs) =
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitE)
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  lr.instrs := by
                                                                simp only
                                                                  [List.cons_append,
                                                                  List.nil_append]
                                                                rw [execInstrsFullFromIn_eq,
                                                                  execInstrsFullFromIn_eq,
                                                                  execInstrsFullFrom_phi_miss
                                                                  _ _ _ _ _ _
                                                                  (Ne.symm
                                                                  hne_pe),
                                                                  execInstrsFullFrom_phi_hit
                                                                  _ _ _ _ _ _
                                                                  rfl,
                                                                  hreg_arr]
                                                              have hJeq :
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitE)
                                                                  ⟨nextB + 2,
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  fenv_arr =
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitE)
                                                                  ⟨nextB + 2,
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩ :=
                                                                execBlockFromIn_instrs_prefix
                                                                  prog F1 f
                                                                  (some exitE)
                                                                  (nextB + 2)
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val]
                                                                  lr.instrs
                                                                  lr.term
                                                                  fenv_arr
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  happ_J
                                                              have hg_r : F1 + 1 ≥
                                                                  blockBound
                                                                  fuelB rest :=
                                                                Nat.le_trans hCege
                                                                  hge
                                                              intro u
                                                              have hfb' : fh ≤ fuelB := by omega
                                                              have hltB' : nextB + 2 < le.next := by
                                                                have h1 : nextB + 3 ≤ lt.next := hmnt
                                                                have h2 : lt.next ≤ le.next := hmne
                                                                omega
                                                              have hihr := ih
                                                                (nextB + 2) ρ
                                                                (le.supply + 1)
                                                                le.next
                                                                le.supply true
                                                                lr hr hrs hf_r
                                                                hlast_r hltB' w_arm
                                                                env_arm
                                                                ⟨fenv_arr.env.update
                                                                le.supply w_arm,
                                                                fenv_arr.store⟩
                                                                hrel_m hreg_m fh
                                                                henv' out hrun
                                                                prog f
                                                                (some exitE)
                                                                (F1 + 1) hsub_r
                                                                hnodf fuelB hg_r hfb'
                                                                u
                                                              refine ⟨?_, ?_⟩
                                                              · intro hout
                                                                obtain ⟨w_u, hu,
                                                                    heq_rest⟩ :=
                                                                  hihr.1 hout
                                                                exact ⟨w_u, hu,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                              · intro e_ret hout2
                                                                obtain ⟨w_e, hu_e,
                                                                    heq_rest⟩ :=
                                                                  hihr.2 e_ret
                                                                    hout2
                                                                exact ⟨w_e, hu_e,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                      | returned e_arm =>
                                                          simp only [] at hrun
                                                          have hout_r : out =
                                                              .returned e_arm :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_r] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            have hret_e : e_ret =
                                                                e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                hout2)).symm
                                                            have hregCb_r :
                                                                fenvC.env vc =
                                                                some
                                                                (.bool false) := by
                                                              have hww :
                                                                  (.bool false) =
                                                                  wC :=
                                                                HIR.Expr.lit.inj
                                                                  hrC
                                                              rw [hww]
                                                              exact hregC
                                                            have hbool_r :
                                                                fenvC.boolOf vc =
                                                                some false :=
                                                              boolOf_of_lit
                                                                fenvC vc false
                                                                hregCb_r
                                                            have hentry_r :
                                                                execBlockFromIn
                                                                prog (F'' + 1)
                                                                f prev ⟨bId, ic,
                                                                .branch vc
                                                                nextB
                                                                (nextB + 1)⟩
                                                                fenv =
                                                                execBlockFromIn
                                                                prog F'' f
                                                                (some bId)
                                                                ⟨nextB + 1,
                                                                le.instrs,
                                                                le.term⟩
                                                                fenvC :=
                                                              execBlockFromIn_branch_false
                                                                prog F'' f prev
                                                                bId ic vc nextB
                                                                (nextB + 1)
                                                                fenv fenvC
                                                                ⟨nextB + 1,
                                                                le.instrs,
                                                                le.term⟩
                                                                hexec_ic
                                                                hbool_r hfindE
                                                            have hsub_er : ∀ b ∈
                                                                le.blocks,
                                                                b ∈ f.blocks :=
                                                              fun b hb => hsub _
                                                                (if_asm_mem_of_le
                                                                hb)
                                                            have hCege_r : (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) ≥
                                                                blockBound fuelB
                                                                rest := by
                                                              have hBrest :
                                                                  blockBound
                                                                  fuelB rest =
                                                                  1 +
                                                                  armBlockBound
                                                                  fuelB rest :=
                                                                rfl
                                                              omega
                                                            have hg_er : F'' ≥
                                                                blockBound fuelB
                                                                el + (2 + max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) := by
                                                              have hBel :
                                                                  blockBound
                                                                  fuelB el = 1 +
                                                                  armBlockBound
                                                                  fuelB el :=
                                                                rfl
                                                              omega
                                                            obtain ⟨w_e, heq,
                                                                hexec_arm⟩ :=
                                                              ((lowerStmtsCFG_arm_total
                                                                budget (nextB + 1)
                                                                (nextB + 2) ρ
                                                                lt.supply lt.next
                                                                lastVal false none el
                                                                le he hael hf_e
                                                                hlast_e .unit
                                                                henv fenvC hrelC
                                                                (fun _ => rfl)
                                                                (fun h => absurd h
                                                                (by simp))
                                                                fh env_arm
                                                                (HFlow.returned
                                                                e_arm)
                                                                har prog f
                                                                (some bId)
                                                                ⟨nextB + 2,
                                                                [.phi le.supply
                                                                exitT lt.val,
                                                                .phi le.supply
                                                                exitE le.val] ++
                                                                lr.instrs,
                                                                lr.term⟩ F''
                                                                hsub_er hnodf
                                                                hfindJ fuelB (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) hg_er
                                                                (.lit .unit)).2
                                                                e_arm rfl)
                                                            exact ⟨w_e,
                                                              hret_e.trans heq,
                                                              hentry_r.trans
                                                              hexec_arm⟩
                                                      | stuck =>
                                                          simp only [] at hrun
                                                          have hout_s : out =
                                                              .stuck :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_s] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_s] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | broke =>
                                                          simp only [] at hrun
                                                          have hout_b : out =
                                                              .broke :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_b] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_b] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | continued =>
                                                          simp only [] at hrun
                                                          have hout_c : out =
                                                              .continued :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_c] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_c] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                          | int _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | string _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | pointer _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | float _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | unit =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | undef =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | some _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | none =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | ok _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | err _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | tuple_ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | array_ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | loc _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | closure _ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
          | breakStmt =>
              simp only [lowerStmtsCFG] at h
              intro accH henv fenv hrel hacc fuelH henv' out hrun prog f
                prev F hsub hnodf fuelB hg hfb u
              refine ⟨?_, ?_⟩
              · intro hout
                simp at h
              · intro e_ret hout2
                simp at h
          | continueStmt =>
              simp only [lowerStmtsCFG] at h
              intro accH henv fenv hrel hacc fuelH henv' out hrun prog f
                prev F hsub hnodf fuelB hg hfb u
              refine ⟨?_, ?_⟩
              · intro hout
                simp at h
              · intro e_ret hout2
                simp at h
          | whileStmt c body hstr hlt hbody =>
              simp only [lowerStmtsCFG] at h
              cases hm : mkCarried ρ supply
                  ((dedupIds (assignedIds body)).filterMap
                    (fun id => (rhoLookup ρ id).map (fun _ => id))) with
              | none => rw [hm] at h; simp at h
              | some p =>
                  obtain ⟨carried, sA, ρb⟩ := p
                  rw [hm] at h
                  simp only [] at h
                  cases hc : lowerExpr ρb sA c with
                  | none => rw [hc] at h; simp at h
                  | some q =>
                      obtain ⟨vc, ic, s1⟩ := q
                      rw [hc] at h
                      simp only [] at h
                      cases hb : lowerStmtsCFG (nextB + 2) (some nextB) false
                          ρb (s1 + 1) (nextB + 3) s1 true
                          (loop := some ⟨nextB, nextB + 1, carried⟩)
                          body with
                      | none => rw [hb] at h; simp at h
                      | some lb =>
                          rw [hb] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 1) none false
                              ρb (lb.supply + 1) lb.next lb.supply true none
                              rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              cases hp : mkHeaderPhis ρ bId carried
                                  ((lb.blocks.getLast?.map fun b => b.id).getD
                                    (nextB + 2))
                                  lb.ρ
                                  (backEdgePreds lb nextB) with
                              | none => rw [hp] at h; simp at h
                              | some phis =>
                                  rw [hp] at h
                                  simp only [] at h
                                  obtain rfl := Option.some.inj h
                                  intro accH henv fenv hrel hacc fuelH henv'
                                    out hrun prog f prev F hsub hnodf fuelB
                                    hg hfb u
                                  have hbb : blockBound fuelB
                                      (.whileLoop c body :: rest) =
                                      1 + ((2 + armBlockBound fuelB body) *
                                        (fuelB + 1) +
                                        armBlockBound fuelB rest) := by
                                    rw [blockBound, armBlockBound_while]
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    cases fuelH with
                                    | zero =>
                                        have hz : runHIRStmts 0 henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (.stuck, henv) := rfl
                                        rw [hz] at hrun
                                        have hst : out = .stuck :=
                                          (congrArg Prod.fst hrun).symm
                                        rw [hst] at hout
                                        exact absurd hout (by simp)
                                    | succ fh =>
                                        have hstep : runHIRStmts (fh + 1)
                                            henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (match runHIRWhile fh henv c body with
                                             | (HFlow.value uu, env'') =>
                                                 runHIRStmts fh env'' rest
                                                   (HFlow.replace
                                                     (HFlow.value
                                                     (.lit accH)) uu)
                                             | (ff, env'') =>
                                                 (ff, env'')) := rfl
                                        rw [hstep] at hrun
                                        cases hw : runHIRWhile fh henv c
                                            body with
                                        | mk res envL =>
                                            rw [hw] at hrun
                                            cases res with
                                            | value v =>
                                                simp only [] at hrun
                                                have hv : v = .lit .unit :=
                                                  runHIRWhile_value_unit fh
                                                    henv c body v envL hw
                                                rw [hv] at hrun hw
                                                simp only
                                                  [HFlow.replace] at hrun
                                                have hfle : fh ≤ fuelB := by
                                                  omega
                                                have hF : F ≥ 1 +
                                                    ((2 + armBlockBound
                                                      fuelB body) *
                                                      (fh + 1) +
                                                      armBlockBound fuelB
                                                      rest) := by
                                                  have h1 : fh + 1 ≤
                                                      fuelB + 1 := by omega
                                                  have h2 : (2 +
                                                      armBlockBound fuelB
                                                      body) * (fh + 1) ≤
                                                      (2 + armBlockBound
                                                      fuelB body) *
                                                      (fuelB + 1) :=
                                                    Nat.mul_le_mul_left
                                                      _ h1
                                                  omega
                                                obtain ⟨hfrX, hloopV,
                                                    hloopR⟩ :=
                                                  whileLoop_correct budget
                                                    bId nextB ρ supply c body
                                                    rest carried sA ρb vc ic
                                                    s1 lb lr phis hm hc hb hr
                                                    hp hbody hrs hstr hlt hfresh hltB fh henv fenv hrel
                                                    (HFlow.value (.lit .unit)) envL hw prog f prev F
                                                    hsub hnodf fuelB hF
                                                obtain ⟨F', fenvX, hleF, hgeF,
                                                    hexit, hrelX, haccX⟩ :=
                                                  hloopV rfl
                                                have hfb'' : fh ≤ fuelB := by
                                                  omega
                                                have hsub_r : ∀ b ∈ lr.blocks,
                                                    b ∈ f.blocks :=
                                                  fun b hb => hsub _
                                                    (List.mem_append_right _
                                                      hb)
                                                have hg'_r : F' ≥ blockBound
                                                    fuelB rest := by
                                                  have hbr : blockBound fuelB
                                                      rest =
                                                      1 + armBlockBound
                                                      fuelB rest := by
                                                    rw [blockBound]
                                                  omega
                                                have hmnb : nextB + 3 ≤ lb.next :=
                                                  (lowerStmtsCFG_loopBody_inv budget _ _ _ _ _ _ _ _ _ _ hb hbody).1
                                                have hltB' : nextB + 1 < lb.next := by omega
                                                obtain ⟨w_u, hu, heq_rest⟩ :=
                                                  (ih (nextB + 1) ρb
                                                    (lb.supply + 1) lb.next
                                                    lb.supply true lr hr hrs
                                                    hfrX
                                                    (Nat.lt_succ_self _)
                                                    hltB'
                                                    .unit envL fenvX hrelX haccX fh
                                                    henv' out hrun prog f
                                                    (some (nextB + 1)) F'
                                                    hsub_r hnodf fuelB hg'_r
                                                    hfb'' u).1 hout
                                                refine ⟨w_u, hu, ?_⟩
                                                exact hexit.trans heq_rest
                                            | returned e =>
                                                simp only [] at hrun
                                                have hret : out =
                                                    .returned e :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hret] at hout
                                                exact absurd hout (by simp)
                                            | broke =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.broke) envL
                                                  hw).1 rfl).elim
                                            | continued =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.continued) envL
                                                  hw).2 rfl).elim
                                            | stuck =>
                                                simp only [] at hrun
                                                have hst : out = .stuck :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hst] at hout
                                                exact absurd hout (by simp)
                                  · intro e_ret hout2
                                    cases fuelH with
                                    | zero =>
                                        have hz : runHIRStmts 0 henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (.stuck, henv) := rfl
                                        rw [hz] at hrun
                                        have hst : out = .stuck :=
                                          (congrArg Prod.fst hrun).symm
                                        rw [hst] at hout2
                                        exact absurd hout2 (by simp)
                                    | succ fh =>
                                        have hstep : runHIRStmts (fh + 1)
                                            henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (match runHIRWhile fh henv c body with
                                             | (HFlow.value uu, env'') =>
                                                 runHIRStmts fh env'' rest
                                                   (HFlow.replace
                                                     (HFlow.value
                                                     (.lit accH)) uu)
                                             | (ff, env'') =>
                                                 (ff, env'')) := rfl
                                        rw [hstep] at hrun
                                        cases hw : runHIRWhile fh henv c
                                            body with
                                        | mk res envL =>
                                            rw [hw] at hrun
                                            cases res with
                                            | value v =>
                                                simp only [] at hrun
                                                have hv : v = .lit .unit :=
                                                  runHIRWhile_value_unit fh
                                                    henv c body v envL hw
                                                rw [hv] at hrun hw
                                                simp only
                                                  [HFlow.replace] at hrun
                                                have hfle : fh ≤ fuelB := by
                                                  omega
                                                have hF : F ≥ 1 +
                                                    ((2 + armBlockBound
                                                      fuelB body) *
                                                      (fh + 1) +
                                                      armBlockBound fuelB
                                                      rest) := by
                                                  have h1 : fh + 1 ≤
                                                      fuelB + 1 := by omega
                                                  have h2 : (2 +
                                                      armBlockBound fuelB
                                                      body) * (fh + 1) ≤
                                                      (2 + armBlockBound
                                                      fuelB body) *
                                                      (fuelB + 1) :=
                                                    Nat.mul_le_mul_left
                                                      _ h1
                                                  omega
                                                obtain ⟨hfrX, hloopV,
                                                    hloopR⟩ :=
                                                  whileLoop_correct budget
                                                    bId nextB ρ supply c body
                                                    rest carried sA ρb vc ic
                                                    s1 lb lr phis hm hc hb hr
                                                    hp hbody hrs hstr hlt hfresh hltB fh henv fenv hrel
                                                    (HFlow.value (.lit .unit)) envL hw prog f prev F
                                                    hsub hnodf fuelB hF
                                                obtain ⟨F', fenvX, hleF, hgeF,
                                                    hexit, hrelX, haccX⟩ :=
                                                  hloopV rfl
                                                have hfb'' : fh ≤ fuelB := by
                                                  omega
                                                have hsub_r : ∀ b ∈ lr.blocks,
                                                    b ∈ f.blocks :=
                                                  fun b hb => hsub _
                                                    (List.mem_append_right _
                                                      hb)
                                                have hg'_r : F' ≥ blockBound
                                                    fuelB rest := by
                                                  have hbr : blockBound fuelB
                                                      rest =
                                                      1 + armBlockBound
                                                      fuelB rest := by
                                                    rw [blockBound]
                                                  omega
                                                have hmnb : nextB + 3 ≤ lb.next :=
                                                  (lowerStmtsCFG_loopBody_inv budget _ _ _ _ _ _ _ _ _ _ hb hbody).1
                                                have hltB' : nextB + 1 < lb.next := by omega
                                                obtain ⟨w_e, heq, heq_rest⟩ :=
                                                  (ih (nextB + 1) ρb
                                                    (lb.supply + 1) lb.next
                                                    lb.supply true lr hr hrs
                                                    hfrX
                                                    (Nat.lt_succ_self _)
                                                    hltB'
                                                    .unit envL fenvX hrelX haccX fh
                                                    henv' out hrun prog f
                                                    (some (nextB + 1)) F'
                                                    hsub_r hnodf fuelB hg'_r
                                                    hfb'' u).2 e_ret hout2
                                                refine ⟨w_e, heq, ?_⟩
                                                exact hexit.trans heq_rest
                                            | returned e =>
                                                simp only [] at hrun
                                                have hret : out =
                                                    .returned e :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hret] at hout2
                                                have hee : e = e_ret :=
                                                  HFlow.returned.inj hout2
                                                have hfle_r : fh ≤ fuelB := by
                                                  omega
                                                have hF_r : F ≥ 1 +
                                                    ((2 + armBlockBound
                                                      fuelB body) *
                                                      (fh + 1) +
                                                      armBlockBound fuelB
                                                      rest) := by
                                                  have h1 : fh + 1 ≤
                                                      fuelB + 1 := by omega
                                                  have h2 : (2 +
                                                      armBlockBound fuelB
                                                      body) * (fh + 1) ≤
                                                      (2 + armBlockBound
                                                      fuelB body) *
                                                      (fuelB + 1) :=
                                                    Nat.mul_le_mul_left
                                                      _ h1
                                                  omega
                                                obtain ⟨hfrX, hloopV,
                                                    hloopR⟩ :=
                                                  whileLoop_correct budget
                                                    bId nextB ρ supply c body
                                                    rest carried sA ρb vc ic
                                                    s1 lb lr phis hm hc hb hr
                                                    hp hbody hrs hstr hlt hfresh hltB fh henv fenv hrel
                                                    (HFlow.returned e) envL hw prog f prev F
                                                    hsub hnodf fuelB hF_r
                                                obtain ⟨w_e, heq, hexec⟩ :=
                                                  hloopR e rfl
                                                rw [hee] at heq
                                                exact ⟨w_e, heq, hexec⟩
                                            | broke =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.broke) envL
                                                  hw).1 rfl).elim
                                            | continued =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.continued) envL
                                                  hw).2 rfl).elim
                                            | stuck =>
                                                simp only [] at hrun
                                                have hst : out = .stuck :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hst] at hout2
                                                exact absurd hout2 (by simp)
      | returnStmt e rest hstr _ =>
          intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
            hsub hnodf fuelB hg hfb
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              intro u
              refine ⟨?_, ?_⟩
              · intro hout
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.returnStmt e :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => (.returned v, henv)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck :=
                          (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hout
                        exact absurd hout (by simp)
              · intro e_ret hout2
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout2
                    exact absurd hout2 (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.returnStmt e :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => (.returned v, henv)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck :=
                          (congrArg Prod.fst hrun).symm
                        rw [hst] at hout2
                        exact absurd hout2 (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hout2
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2,
                            hrE2, hregE⟩ :=
                          lower_total.1 ρ supply e v ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        have hrr : r = e_ret := HFlow.returned.inj hout2
                        have heq : e_ret = .lit wE := hrr.symm ▸ hrE
                        have hnp : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                        have hexec : execInstrsFullFromIn prog prev fenv ie
                            = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _
                            hnp]
                          exact hexec1
                        have hbb : blockBound fuelB (.returnStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        have h1 : blockBound fuelB rest ≥ 1 := by
                          rw [blockBound]; omega
                        cases F with
                        | zero => omega
                        | succ F' =>
                            refine ⟨wE, heq, ?_⟩
                            have hLHS : execBlockFromIn prog (F' + 1) f prev
                                    ⟨bId, ie, .return_ v⟩ fenv =
                                    fenv1.env v := by
                              have hret' : execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, ie, .return_ v⟩ fenv =
                                  (match execInstrsFullFromIn prog prev fenv
                                      ie with
                                   | none => (none : Option Value)
                                   | some g => g.env v) := rfl
                              rw [hret', hexec]
                            have hww : wE = wE2 :=
                              HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                            rw [hLHS, hww]
                            exact hregE

/-- Top-level binding-arm `if` case (C2c C3 integration): an `if` with
`BindArmStmts` arms at top level (`arm = false`, `loop = none`). The arm
executions come in as worker contracts (arrival equation plus arm-exit
`RelEnv`, value-register fact, and fuel threading, in `arm_total`'s
conclusion shape — the future arm worker discharges them); the HIR
inversion, entry stepping, and fuel splitting mirror `lowerStmtsCFG_total`.
The join goes through `bindArm_join_exec` uniformly on both merge paths
(the empty path is the merge path with no phis), and the tail invokes
`lowerStmtsCFG_total` itself under the merged env. -/
theorem lowerStmtsCFG_bindArm_if_total (budget : Nat) :
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
      ∀ (_harmT : ∀ (s1 : Nat) (lt : Lowered) (exitT : MIR.BlockId),
        lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3)
          lastVal false none th = some lt →
        ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) = exitT →
        ∀ (joinBlock : Block),
        findBlock f (nextB + 2) = some joinBlock →
        ∀ (fenvC : FullEnv) (F1 C : Nat),
        RelEnv henv ρ fenvC.env →
        F1 ≥ blockBound fuelB th + C →
        ∀ (fh : Nat) (henvArm : HEnv) (outArm : HFlow),
        runHIRStmts fh henv th (.value (.lit .unit)) = (outArm, henvArm) →
        ∀ (_hs1 : supply ≤ s1) (_hsubT : ∀ b ∈ lt.blocks, b ∈ f.blocks)
          (_hregT : fenvC.env lastVal = some .unit),
        (∀ (uArm : HIR.Expr), outArm = .value uArm →
          ∃ wArm fenvT F1', uArm = .lit wArm ∧ F1' ≤ F1 ∧ F1' ≥ C ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB, lt.instrs,
            lt.term⟩ fenvC =
            execBlockFromIn prog F1' f (some exitT) joinBlock fenvT ∧
          RelEnv henvArm lt.ρ fenvT.env ∧ fenvT.env lt.val = some wArm) ∧
        (∀ (e : HIR.Expr), outArm = .returned e →
          ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB, lt.instrs,
            lt.term⟩ fenvC =
            some w_e)),
      ∀ (_harmE : ∀ (s1t : Nat) (ltE : Lowered) (s1e : Nat) (le : Lowered)
        (exitE : MIR.BlockId),
        lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1t (nextB + 3)
          lastVal false none th = some ltE →
        lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ s1e ltE.next
          lastVal false none el = some le →
        ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1)) = exitE →
        ∀ (joinBlock : Block),
        findBlock f (nextB + 2) = some joinBlock →
        ∀ (fenvC : FullEnv) (F1 C : Nat),
        RelEnv henv ρ fenvC.env →
        F1 ≥ blockBound fuelB el + C →
        ∀ (fh : Nat) (henvArm : HEnv) (outArm : HFlow),
        runHIRStmts fh henv el (.value (.lit .unit)) = (outArm, henvArm) →
        ∀ (_hsubE : ∀ b ∈ le.blocks, b ∈ f.blocks)
          (_hfE : FreshAbove ρ s1e) (_hlE : lastVal < s1e)
          (_hregE : fenvC.env lastVal = some .unit),
        (∀ (uArm : HIR.Expr), outArm = .value uArm →
          ∃ wArm fenvT F1', uArm = .lit wArm ∧ F1' ≤ F1 ∧ F1' ≥ C ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB + 1, le.instrs,
            le.term⟩ fenvC =
            execBlockFromIn prog F1' f (some exitE) joinBlock fenvT ∧
          RelEnv henvArm le.ρ fenvT.env ∧ fenvT.env le.val = some wArm) ∧
        (∀ (e : HIR.Expr), outArm = .returned e →
          ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB + 1, le.instrs,
            le.term⟩ fenvC =
            some w_e)),
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
    prog f prev F hsub hnodf fuelB hg hfb harmT harmE u
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
              have hf1 : FreshAbove ρ s1 :=
                FreshAbove.mono ρ supply s1 hs1 hfresh
              have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
              have hst : s1 ≤ lt.supply :=
                (lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ ht
                  hTh).2.1
              have hse : lt.supply ≤ le.supply :=
                (lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ he
                  hEl).2.1
              have hfrρ : FreshAbove ρ
                  le.supply :=
                FreshAbove.mono ρ supply
                  le.supply (Nat.le_trans hs1
                  (Nat.le_trans hst hse))
                  hfresh
              have hbb_if : blockBound fuelB (.ifStmt c th el :: rest) =
                  1 + (3 + max (armBlockBound fuelB th)
                    (armBlockBound fuelB el) +
                    armBlockBound fuelB rest) := by
                rw [blockBound, armBlockBound_if]
              have hB1 : blockBound fuelB (.ifStmt c th el :: rest) ≥ 1 := by
                rw [blockBound]; omega
              have hne_pe : ((le.blocks.getLast?.map (fun b => b.id)).getD
                  (nextB + 1)) ≠
                  ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) := by
                have hexitT : ((lt.blocks.getLast?.map (fun b => b.id)).getD
                    nextB) = nextB ∨
                    ∃ b ∈ lt.blocks,
                      ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) =
                        b.id := by
                  cases hgl : lt.blocks.getLast? with
                  | none =>
                      exact Or.inl (by simp)
                  | some b =>
                      have hm : b ∈ lt.blocks := getLast?_mem hgl
                      exact Or.inr ⟨b, hm, by simp⟩
                have hexitE : ((le.blocks.getLast?.map (fun b => b.id)).getD
                    (nextB + 1)) = nextB + 1 ∨
                    ∃ b ∈ le.blocks,
                      ((le.blocks.getLast?.map (fun b => b.id)).getD
                        (nextB + 1)) = b.id := by
                  cases hgl : le.blocks.getLast? with
                  | none =>
                      exact Or.inl (by simp)
                  | some b =>
                      have hm : b ∈ le.blocks := getLast?_mem hgl
                      exact Or.inr ⟨b, hm, by simp⟩
                rcases hexitT with hT | ⟨bt, hbt, hT⟩
                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                  · simp [hT, hE]
                  · obtain ⟨hlo, -⟩ := hbnde be hbe
                    rw [hE, hT]
                    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega)
                      (Nat.le_trans hmnt hlo))
                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                  · obtain ⟨hlo, -⟩ := hbndt bt hbt
                    rw [hE, hT]
                    exact Nat.ne_of_lt (Nat.le_trans (Nat.le_of_lt
                      (Nat.add_lt_add_left (by decide) nextB)) hlo)
                  · obtain ⟨-, hhi⟩ := hbndt bt hbt
                    obtain ⟨hlo, -⟩ := hbnde be hbe
                    rw [hE, hT]
                    exact Nat.ne_of_gt
                      (Nat.lt_of_lt_of_le hhi hlo)
              have hgF : F ≥ 1 + (3 + max (armBlockBound fuelB th)
                  (armBlockBound fuelB el) + armBlockBound fuelB rest) := by
                rw [← hbb_if]; exact hg
              cases F with
              | zero => omega
              | succ F'' =>
                  cases fuelH with
                  | zero =>
                      have hz : runHIRStmts 0 henv
                          (.ifStmt c th el :: rest)
                          (.value (.lit accH)) = (.stuck, henv) := rfl
                      rw [hz] at hrun
                      have hst : out = .stuck :=
                        (congrArg Prod.fst hrun).symm
                      refine ⟨?_, ?_⟩
                      · intro hout
                        simp [hst] at hout
                      · intro e hout
                        simp [hst] at hout
                  | succ fh =>
                      have hstep : runHIRStmts (fh + 1) henv
                          (.ifStmt c th el :: rest)
                          (.value (.lit accH)) =
                          (match evalHIR 256 henv c with
                            | some (.lit (.bool true)) =>
                              match runHIRStmts fh henv th
                                  (HFlow.value (.lit .unit)) with
                              | (HFlow.value u, env') =>
                                  runHIRStmts fh env' rest
                                    ((HFlow.value (.lit accH)).replace
                                      u)
                              | (f, env') => (f, env')
                            | some (.lit (.bool false)) =>
                              match runHIRStmts fh henv el
                                  (HFlow.value (.lit .unit)) with
                              | (HFlow.value u, env') =>
                                  runHIRStmts fh env' rest
                                    ((HFlow.value (.lit accH)).replace
                                      u)
                              | (f, env') => (f, env')
                            | _ => (.stuck, henv)) := rfl
                      rw [hstep] at hrun
                      cases hevC : evalHIR 256 henv c with
                      | none =>
                          rw [hevC] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          refine ⟨?_, ?_⟩
                          · intro hout
                            simp [hst] at hout
                          · intro e hout
                            simp [hst] at hout
                      | some r =>
                          rw [hevC] at hrun
                          obtain ⟨⟨w, hrw⟩, fenvC, hexecC, hstoreC,
                              wC, hrC, hregC⟩ :=
                            lower_total.1 ρ supply c vc ic s1 heC hstr
                              hfresh henv fenv hrel 256 r hevC
                          subst hrw
                          have hnp_ic : ∀ dst pred src,
                              .phi dst pred src ∉ ic := by
                            intro d p s hm
                            exact IsPure_not_phi
                              (lower_isPure.1 _ _ _ _ _ _ heC _ hm)
                              d p s rfl
                          have hexec_ic : execInstrsFullFromIn prog
                              prev fenv ic = some fenvC := by
                            rw [execInstrsFullFromIn_of_noPhi prog prev
                              fenv _ hnp_ic]
                            exact hexecC
                          have hrelC : RelEnv henv ρ fenvC.env :=
                            RelEnv_exec henv ρ supply c vc ic s1 heC
                              fenv fenvC hrel hfresh hexecC
                          have hentryC : fenvC.env lastVal = some .unit := by
                            have hp : fenvC.env lastVal = fenv.env lastVal :=
                              lower_preserv_regs ρ supply c vc ic s1 heC fenv
                                fenvC hexecC lastVal hlast
                            rw [hp, hacc, haccU]
                          have hsuffix : ∀ (ρm : List
                              (HIR.Id × ValId)) (s2 : Nat)
                              (mphis : List Instr)
                              (lr : Lowered),
                              (hmk : mkMergePhis ρ lt.ρ
                                le.ρ (le.supply + 1)
                                ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD
                                nextB)
                                ((le.blocks.getLast?.map
                                (fun b => b.id)).getD
                                (nextB + 1))
                                (mergeIds ρ lt.ρ le.ρ) =
                                some (mphis, s2, ρm)) →
                              (hr : lowerStmtsCFG
                                (nextB + 2) none false ρm
                                s2 le.next le.supply true
                                none rest = some lr) →
                              (hsubR : ∀ b ∈ lt.blocks ++
                                [⟨nextB, lt.instrs,
                                lt.term⟩] ++ le.blocks ++
                                [⟨nextB + 1, le.instrs,
                                le.term⟩] ++ [⟨nextB + 2,
                                [MIR.Instr.phi le.supply
                                ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD
                                nextB) lt.val,
                                MIR.Instr.phi le.supply
                                ((le.blocks.getLast?.map
                                (fun b => b.id)).getD
                                (nextB + 1)) le.val] ++
                                mphis ++ lr.instrs,
                                lr.term⟩] ++ lr.blocks,
                                b ∈ f.blocks) →
                              (armPrev : Option MIR.BlockId) →
                              (armEntry : Block) →
                              (armExit : MIR.BlockId) →
                              (hentry : execBlockFromIn prog
                                (F'' + 1) f prev
                                ⟨bId, ic, .branch vc nextB
                                (nextB + 1)⟩ fenv =
                                execBlockFromIn prog F'' f
                                armPrev armEntry fenvC) →
                              (henvArm : HEnv) →
                              (wArm : Value) →
                              (henv' : HEnv) →
                              (out : HFlow) →
                              (hrunTail : runHIRStmts fh
                                henvArm rest
                                (.value (.lit wArm)) =
                                (out, henv')) →
                              (C : Nat) →
                              (hCtge : C ≥ blockBound fuelB
                                rest) →
                              ∀ (fenvT : FullEnv)
                              (F1' : Nat),
                              F1' ≤ F'' →
                              F1' ≥ C →
                              (heq_arm : execBlockFromIn
                              prog F'' f armPrev
                              armEntry fenvC =
                              execBlockFromIn prog F1' f
                              (some armExit) ⟨nextB + 2,
                              [MIR.Instr.phi le.supply
                              ((lt.blocks.getLast?.map
                              (fun b => b.id)).getD
                              nextB) lt.val,
                              MIR.Instr.phi le.supply
                              ((le.blocks.getLast?.map
                              (fun b => b.id)).getD
                              (nextB + 1)) le.val] ++
                              mphis ++ lr.instrs,
                              lr.term⟩ fenvT) →
                              (fenvJ : FullEnv) →
                              (happJ : execInstrsFullFromIn prog
                              (some armExit) fenvT
                              (([MIR.Instr.phi le.supply
                              ((lt.blocks.getLast?.map
                              (fun b => b.id)).getD
                              nextB) lt.val,
                              MIR.Instr.phi le.supply
                              ((le.blocks.getLast?.map
                              (fun b => b.id)).getD
                              (nextB + 1)) le.val] ++
                              mphis) ++ lr.instrs) =
                              execInstrsFullFromIn prog
                              (some armExit) fenvJ lr.instrs) →
                              (hrelJ : RelEnv henvArm ρm
                                fenvJ.env) →
                              (hvmJ : fenvJ.env le.supply =
                              some wArm) →
                              (out = .value u →
                              ∃ w_u, u = .lit w_u ∧
                              execBlockFromIn prog (F'' + 1) f
                              prev ⟨bId, ic, .branch vc
                              nextB (nextB + 1)⟩ fenv =
                              some w_u) ∧
                              (∀ (e : HIR.Expr),
                              out = .returned e →
                              ∃ w_e, e = .lit w_e ∧
                              execBlockFromIn prog (F'' + 1) f
                              prev ⟨bId, ic, .branch vc
                              nextB (nextB + 1)⟩ fenv =
                              some w_e) := by
                            intro ρm s2 mphis lr hmk hr
                              hsubR armPrev armEntry armExit
                              hentry henvArm wArm henv'
                              out hrunTail C hCtge
                              fenvT F1' hle hge
                              heq_arm fenvJ happJ hrelJ hvmJ
                            have hJmem : (⟨nextB + 2,
                                [MIR.Instr.phi le.supply
                                ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD
                                nextB) lt.val,
                                MIR.Instr.phi le.supply
                                ((le.blocks.getLast?.map
                                (fun b => b.id)).getD
                                (nextB + 1)) le.val] ++
                                mphis ++ lr.instrs,
                                lr.term⟩ : Block) ∈
                                f.blocks :=
                              hsubR _ if_asm_mem_join
                            have hfindJ : findBlock f
                                (nextB + 2) = some ⟨nextB + 2,
                                [MIR.Instr.phi le.supply
                                ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD
                                nextB) lt.val,
                                MIR.Instr.phi le.supply
                                ((le.blocks.getLast?.map
                                (fun b => b.id)).getD
                                (nextB + 1)) le.val] ++
                                mphis ++ lr.instrs,
                                lr.term⟩ :=
                              findBlock_of_nodup_mem hnodf
                                hJmem
                            have hJeq : execBlockFromIn prog
                                F1' f (some armExit)
                                ⟨nextB + 2,
                                [MIR.Instr.phi le.supply
                                ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD
                                nextB) lt.val,
                                MIR.Instr.phi le.supply
                                ((le.blocks.getLast?.map
                                (fun b => b.id)).getD
                                (nextB + 1)) le.val] ++
                                mphis ++ lr.instrs,
                                lr.term⟩ fenvT =
                                execBlockFromIn prog F1'
                                f (some armExit) ⟨nextB + 2,
                                lr.instrs, lr.term⟩
                                fenvJ := by
                              cases F1' with
                              | zero =>
                                  have hB1r : blockBound fuelB
                                      rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  exact absurd hge (by omega)
                              | succ G =>
                                  exact execBlockFromIn_instrs_prefix
                                    prog G f (some armExit)
                                    (nextB + 2)
                                    ([MIR.Instr.phi le.supply
                                    ((lt.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    nextB) lt.val,
                                    MIR.Instr.phi le.supply
                                    ((le.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    (nextB + 1)) le.val] ++
                                    mphis) lr.instrs lr.term
                                    fenvT fenvJ happJ
                            have hf_r : FreshAbove ρm s2 :=
                              (mkMergePhis_growth_fresh
                              (FreshAbove.mono ρ supply
                              (le.supply + 1) (by omega)
                              hfresh) hmk).2
                            have hlast_r : le.supply < s2 :=
                              Nat.lt_of_lt_of_le
                              (Nat.lt_succ_self _)
                              (mkMergePhis_le hmk)
                            have hltB' : nextB + 2 < le.next := by
                              have h1 : nextB + 3 ≤ lt.next :=
                                hmnt
                              have h2 : lt.next ≤ le.next :=
                                hmne
                              omega
                            have hsub_r : ∀ b ∈ lr.blocks,
                                b ∈ f.blocks :=
                              fun b hb => hsubR _
                                (if_asm_mem_of_lr hb)
                            cases F1' with
                            | zero =>
                                have hB1r : blockBound fuelB
                                    rest ≥ 1 := by
                                  rw [blockBound]; omega
                                exact absurd hge (by omega)
                            | succ F1 =>
                                have hg_r : F1 + 1 ≥
                                    blockBound fuelB rest :=
                                  Nat.le_trans hCtge hge
                                have hfb' : fh ≤ fuelB := by
                                  omega
                                have htail :=
                                  lowerStmtsCFG_total budget
                                  (nextB + 2) ρm s2 le.next
                                  le.supply true rest lr hr hrs
                                  hf_r hlast_r hltB' wArm
                                  henvArm fenvJ hrelJ hvmJ fh
                                  henv' out hrunTail prog f
                                  (some armExit) (F1 + 1) hsub_r
                                  hnodf fuelB hg_r hfb'
                                refine ⟨?_, ?_⟩
                                · intro hout
                                  obtain ⟨w_u, hu,
                                      heq_rest⟩ :=
                                    (htail u).1 hout
                                  exact ⟨w_u, hu,
                                    hentry.trans
                                    (heq_arm.trans
                                    (hJeq.trans
                                    heq_rest))⟩
                                · intro e_ret hout2
                                  obtain ⟨w_e, hu_e,
                                      heq_rest⟩ :=
                                    (htail u).2 e_ret hout2
                                  exact ⟨w_e, hu_e,
                                    hentry.trans
                                    (heq_arm.trans
                                    (hJeq.trans
                                    heq_rest))⟩
                          cases w with
                          | bool b =>
                              cases b with
                              | true =>
                                  simp only [] at hrun
                                  cases har : runHIRStmts fh henv th
                                      (HFlow.value (.lit .unit)) with
                                  | mk out_arm env_arm =>
                                      rw [har] at hrun
                                      cases out_arm with
                                      | value u_arm =>
                                          simp only [] at hrun
                                          have hregCb : fenvC.env vc =
                                              some (.bool true) := by
                                            have hww : (.bool true) =
                                                wC :=
                                              HIR.Expr.lit.inj hrC
                                            rw [hww]
                                            exact hregC
                                          have hbool : fenvC.boolOf vc =
                                              some true :=
                                            boolOf_of_lit fenvC vc true
                                              hregCb
                                          have hCtge : (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB th) ≥
                                              blockBound fuelB rest := by
                                            have hBrest : blockBound
                                                fuelB rest = 1 +
                                                armBlockBound fuelB
                                                  rest := rfl
                                            omega
                                          have hg_t : F'' ≥ blockBound
                                              fuelB th + (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB th) := by
                                            have hBth : blockBound
                                                fuelB th = 1 +
                                                armBlockBound fuelB
                                                  th := rfl
                                            omega
                                          have hfrT :=
                                            lowerStmtsCFG_bindArm_fresh
                                              budget _ _ _ _ _ _ _ _ _ ht
                                              hTh hf1 hlast1
                                          have hfreshT : ∀ id srcT,
                                              id ∈ mergeIds ρ lt.ρ le.ρ →
                                              rhoLookup lt.ρ id =
                                              some srcT →
                                              srcT < le.supply + 1 := by
                                            intro id srcT hmem hlook
                                            have h1 : srcT < lt.supply :=
                                              hfrT id srcT
                                              (rhoLookup_some_mem lt.ρ id
                                              srcT hlook)
                                            exact Nat.lt_of_lt_of_le h1
                                              (Nat.le_trans hse
                                                (Nat.le_succ _))
                                          have hne : ∀ id srcT,
                                              id ∈ mergeIds ρ lt.ρ le.ρ →
                                              rhoLookup lt.ρ id =
                                              some srcT →
                                              srcT ≠ le.supply := by
                                            intro id srcT hmem hlook
                                            have h1 : srcT < lt.supply :=
                                              hfrT id srcT
                                              (rhoLookup_some_mem lt.ρ id
                                              srcT hlook)
                                            exact fun heq =>
                                              (Nat.not_lt.mpr hse)
                                                (heq.symm ▸ h1)
                                          cases hm : mergeIds ρ lt.ρ le.ρ with
                                          | nil =>
                                              have hmk : mkMergePhis ρ lt.ρ
                                                  le.ρ (le.supply + 1)
                                                  ((lt.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  nextB)
                                                  ((le.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  (nextB + 1))
                                                  (mergeIds ρ lt.ρ le.ρ) =
                                                  some ([], le.supply + 1,
                                                  ρ) := by
                                                rw [hm]
                                                rfl
                                              rw [hm] at h
                                              simp only [] at h
                                              cases hr : lowerStmtsCFG
                                                  (nextB + 2) none false ρ
                                                  (le.supply + 1) le.next
                                                  le.supply true none
                                                  rest with
                                              | none => rw [hr] at h; simp at h
                                              | some lr =>
                                                  rw [hr] at h
                                                  simp only [] at h
                                                  obtain rfl :=
                                                    Option.some.inj h
                                                  dsimp only at hsub ⊢
                                                  have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                      ∈ f.blocks :=
                                                    hsub _ if_asm_mem_then
                                                  have hfindT : findBlock f nextB =
                                                      some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf hTmem
                                                  have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                      ∈ f.blocks :=
                                                    hsub _ if_asm_mem_else
                                                  have hfindE : findBlock f (nextB + 1) =
                                                      some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf hEmem
                                                  have hfindJb : findBlock f
                                                      (nextB + 2) = some ⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      lr.instrs,
                                                      lr.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf
                                                      (hsub _ if_asm_mem_join)
                                                  obtain ⟨wArm, fenvT, F1',
                                                      huArm, hle, hge, heq_arm,
                                                      hrel_arm,
                                                      hreg_arm⟩ :=
                                                    ((harmT s1 lt
                                                    ((lt.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    nextB) ht rfl ⟨nextB + 2,
                                                    [MIR.Instr.phi le.supply
                                                    ((lt.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    nextB) lt.val,
                                                    MIR.Instr.phi le.supply
                                                    ((le.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    (nextB + 1)) le.val] ++
                                                    lr.instrs,
                                                    lr.term⟩ hfindJb fenvC F''
                                                    (2 + max
                                                    (armBlockBound fuelB th)
                                                    (armBlockBound fuelB el) +
                                                    armBlockBound fuelB rest -
                                                    armBlockBound fuelB th)
                                                    hrelC hg_t fh env_arm
                                                    (HFlow.value u_arm)
                                                    har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).1 u_arm rfl)
                                                  obtain ⟨fenvJ, happJ, hrelJ,
                                                      hvmJ, -⟩ :=
                                                    bindArm_join_exec prog hmk rfl
                                                      hne_pe hrel_arm hreg_arm
                                                      hfreshT hne
                                                      (Nat.lt_succ_self _) hfrρ
                                                  have hentry : execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc nextB
                                                      (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                      (some bId)
                                                      ⟨nextB, lt.instrs,
                                                      lt.term⟩ fenvC :=
                                                    execBlockFromIn_branch_true
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC ⟨nextB, lt.instrs,
                                                      lt.term⟩ hexec_ic hbool
                                                      hfindT
                                                  have hsubR : ∀ b ∈ lt.blocks ++
                                                      [⟨nextB, lt.instrs,
                                                      lt.term⟩] ++ le.blocks ++
                                                      [⟨nextB + 1, le.instrs,
                                                      le.term⟩] ++ [⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      ([] : List Instr) ++
                                                      lr.instrs,
                                                      lr.term⟩] ++ lr.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _ hb
                                                  have hrep : ((HFlow.value
                                                      (.lit accH)).replace
                                                      (.lit wArm)) =
                                                      HFlow.value
                                                        (.lit wArm) := rfl
                                                  rw [huArm, hrep] at hrun
                                                  exact hsuffix _ _ _ _ hmk hr
                                                    hsubR (some bId) ⟨nextB, lt.instrs,
                                                    lt.term⟩ ((lt.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    nextB) hentry env_arm wArm
                                                    henv' out hrun (2 + max
                                                    (armBlockBound fuelB th)
                                                    (armBlockBound fuelB el) +
                                                    armBlockBound fuelB rest -
                                                    armBlockBound fuelB th)
                                                    hCtge fenvT F1'
                                                    hle hge heq_arm
                                                    fenvJ happJ hrelJ hvmJ
                                          | cons hd tl =>
                                              rw [hm] at h
                                              simp only [] at h
                                              cases hmphi : mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                                                  ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                                                  ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                                                  (hd :: tl) with
                                              | none => rw [hmphi] at h; simp at h
                                              | some q =>
                                                  obtain ⟨mphis, s2, ρm⟩ := q
                                                  rw [hmphi] at h
                                                  simp only [] at h
                                                  cases hr : lowerStmtsCFG
                                                      (nextB + 2) none false ρm
                                                      s2 le.next
                                                      le.supply true none
                                                      rest with
                                                  | none => rw [hr] at h; simp at h
                                                  | some lr =>
                                                      rw [hr] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      dsimp only at hsub ⊢
                                                      have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                          ∈ f.blocks :=
                                                        hsub _ if_asm_mem_then
                                                      have hfindT : findBlock f nextB =
                                                          some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf hTmem
                                                      have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                          ∈ f.blocks :=
                                                        hsub _ if_asm_mem_else
                                                      have hfindE : findBlock f (nextB + 1) =
                                                          some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf hEmem
                                                      have hmk : mkMergePhis ρ lt.ρ
                                                          le.ρ (le.supply + 1)
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB)
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1))
                                                          (mergeIds ρ lt.ρ le.ρ) =
                                                          some (mphis, s2, ρm) := by
                                                        rw [hm]
                                                        exact hmphi
                                                      have hfindJb : findBlock f
                                                          (nextB + 2) = some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphis ++ lr.instrs,
                                                          lr.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      obtain ⟨wArm, fenvT, F1',
                                                          huArm, hle, hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arm⟩ :=
                                                        ((harmT s1 lt
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) ht rfl ⟨nextB + 2,
                                                        [MIR.Instr.phi le.supply
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) lt.val,
                                                        MIR.Instr.phi le.supply
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) le.val] ++
                                                        mphis ++ lr.instrs,
                                                        lr.term⟩ hfindJb fenvC F''
                                                        (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB th)
                                                        hrelC hg_t fh env_arm
                                                        (HFlow.value u_arm)
                                                        har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).1 u_arm rfl)
                                                      obtain ⟨fenvJ, happJ, hrelJ,
                                                          hvmJ, -⟩ :=
                                                        bindArm_join_exec prog hmk rfl
                                                          hne_pe hrel_arm hreg_arm
                                                          hfreshT hne
                                                          (Nat.lt_succ_self _) hfrρ
                                                      have hentry : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB, lt.instrs,
                                                          lt.term⟩ fenvC :=
                                                        execBlockFromIn_branch_true
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB, lt.instrs,
                                                          lt.term⟩ hexec_ic hbool
                                                          hfindT
                                                      have hsubR : ∀ b ∈ lt.blocks ++
                                                          [⟨nextB, lt.instrs,
                                                          lt.term⟩] ++ le.blocks ++
                                                          [⟨nextB + 1, le.instrs,
                                                          le.term⟩] ++ [⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphis ++ lr.instrs,
                                                          lr.term⟩] ++ lr.blocks,
                                                          b ∈ f.blocks :=
                                                        fun b hb => hsub _ hb
                                                      have hrep : ((HFlow.value
                                                          (.lit accH)).replace
                                                          (.lit wArm)) =
                                                          HFlow.value
                                                            (.lit wArm) := rfl
                                                      rw [huArm, hrep] at hrun
                                                      exact hsuffix _ _ _ _ hmk hr
                                                        hsubR (some bId) ⟨nextB, lt.instrs,
                                                        lt.term⟩ ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) hentry env_arm wArm
                                                        henv' out hrun (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB th)
                                                        hCtge fenvT F1'
                                                        hle hge heq_arm
                                                        fenvJ happJ hrelJ hvmJ
                                      | returned e_arm =>
                                          simp only [] at hrun
                                          have hout_r : out =
                                              .returned e_arm :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          have hregCb_r : fenvC.env vc =
                                              some (.bool true) := by
                                            have hww : (.bool true) =
                                                wC :=
                                              HIR.Expr.lit.inj hrC
                                            rw [hww]
                                            exact hregC
                                          have hbool_r : fenvC.boolOf vc =
                                              some true :=
                                            boolOf_of_lit fenvC vc true
                                              hregCb_r
                                          have hg_tr : F'' ≥ blockBound
                                              fuelB th + (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB th) := by
                                            have hBth : blockBound
                                                fuelB th = 1 +
                                                armBlockBound fuelB
                                                  th := rfl
                                            omega
                                          cases hmR : mergeIds ρ lt.ρ le.ρ with
                                          | nil =>
                                              rw [hmR] at h
                                              simp only [] at h
                                              cases hrR : lowerStmtsCFG
                                                  (nextB + 2) none false ρ
                                                  (le.supply + 1) le.next
                                                  le.supply true none
                                                  rest with
                                              | none =>
                                                  rw [hrR] at h
                                                  simp at h
                                              | some lrR =>
                                                  rw [hrR] at h
                                                  simp only [] at h
                                                  obtain rfl :=
                                                    Option.some.inj h
                                                  have hfindT : findBlock f nextB =
                                                      some ⟨nextB, lt.instrs,
                                                      lt.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf
                                                      (hsub _ if_asm_mem_then)
                                                  have hfindJb : findBlock f (nextB + 2) =
                                                      some ⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      ([] : List Instr) ++
                                                      lrR.instrs,
                                                      lrR.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf
                                                      (hsub _ if_asm_mem_join)
                                                  have hentry_r : execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc nextB
                                                      (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                      (some bId)
                                                      ⟨nextB, lt.instrs,
                                                      lt.term⟩ fenvC :=
                                                    execBlockFromIn_branch_true
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC ⟨nextB, lt.instrs,
                                                      lt.term⟩ hexec_ic hbool_r
                                                      hfindT
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    simp [hout_r] at hout
                                                  · intro e hout2
                                                    have hret_e : e = e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
                                                    obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                      ((harmT s1 lt
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) ht rfl ⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      ([] : List Instr) ++
                                                      lrR.instrs,
                                                      lrR.term⟩ hfindJb fenvC F''
                                                      (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th)
                                                      hrelC hg_tr fh env_arm
                                                      (HFlow.returned e_arm)
                                                      har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).2 e_arm rfl)
                                                    exact ⟨w_e, hret_e.trans hu_e,
                                                      hentry_r.trans heq_e⟩
                                          | cons hdR tlR =>
                                              rw [hmR] at h
                                              simp only [] at h
                                              cases hmphiR : mkMergePhis ρ lt.ρ le.ρ
                                                  (le.supply + 1)
                                                  ((lt.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  nextB)
                                                  ((le.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  (nextB + 1))
                                                  (hdR :: tlR) with
                                              | none =>
                                                  rw [hmphiR] at h
                                                  simp at h
                                              | some qR =>
                                                  obtain ⟨mphisR, s2R,
                                                      ρmR⟩ := qR
                                                  rw [hmphiR] at h
                                                  simp only [] at h
                                                  cases hrR : lowerStmtsCFG
                                                      (nextB + 2) none false
                                                      ρmR s2R le.next
                                                      le.supply true none
                                                      rest with
                                                  | none =>
                                                      rw [hrR] at h
                                                      simp at h
                                                  | some lrR =>
                                                      rw [hrR] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      have hfindT : findBlock f nextB =
                                                          some ⟨nextB, lt.instrs,
                                                          lt.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_then)
                                                      have hfindJb : findBlock f (nextB + 2) =
                                                          some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphisR ++
                                                          lrR.instrs,
                                                          lrR.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      have hentry_r : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB, lt.instrs,
                                                          lt.term⟩ fenvC :=
                                                        execBlockFromIn_branch_true
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB, lt.instrs,
                                                          lt.term⟩ hexec_ic hbool_r
                                                          hfindT
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        simp [hout_r] at hout
                                                      · intro e hout2
                                                        have hret_e : e = e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                              hout2)).symm
                                                        obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                          ((harmT s1 lt
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) ht rfl ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphisR ++
                                                          lrR.instrs,
                                                          lrR.term⟩ hfindJb fenvC F''
                                                          (2 + max
                                                          (armBlockBound fuelB th)
                                                          (armBlockBound fuelB el) +
                                                          armBlockBound fuelB rest -
                                                          armBlockBound fuelB th)
                                                          hrelC hg_tr fh env_arm
                                                          (HFlow.returned e_arm)
                                                          har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).2 e_arm rfl)
                                                        exact ⟨w_e, hret_e.trans hu_e,
                                                          hentry_r.trans heq_e⟩
                                      | broke =>
                                          simp only [] at hrun
                                          have hout_r : out = .broke :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hout_r] at hout
                                          · intro e hout2
                                            simp [hout_r] at hout2
                                      | continued =>
                                          simp only [] at hrun
                                          have hout_r : out = .continued :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hout_r] at hout
                                          · intro e hout2
                                            simp [hout_r] at hout2
                                      | stuck =>
                                          simp only [] at hrun
                                          have hout_r : out = .stuck :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hout_r] at hout
                                          · intro e hout2
                                            simp [hout_r] at hout2
                              | false =>
                                  simp only [] at hrun
                                  cases har : runHIRStmts fh henv el
                                      (HFlow.value (.lit .unit)) with
                                  | mk out_arm env_arm =>
                                      rw [har] at hrun
                                      cases out_arm with
                                      | value u_arm =>
                                          simp only [] at hrun
                                          have hregCb : fenvC.env vc =
                                              some (.bool false) := by
                                            have hww : (.bool false) =
                                                wC :=
                                              HIR.Expr.lit.inj hrC
                                            rw [hww]
                                            exact hregC
                                          have hbool : fenvC.boolOf vc =
                                              some false :=
                                            boolOf_of_lit fenvC vc false
                                              hregCb
                                          have hCtge' : (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB el) ≥
                                              blockBound fuelB rest := by
                                            have hBrest : blockBound
                                                fuelB rest = 1 +
                                                armBlockBound fuelB
                                                  rest := rfl
                                            omega
                                          have hg_e : F'' ≥ blockBound
                                              fuelB el + (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB el) := by
                                            have hBel : blockBound
                                                fuelB el = 1 +
                                                armBlockBound fuelB
                                                  el := rfl
                                            omega
                                          have hfE1 : FreshAbove ρ lt.supply :=
                                            FreshAbove.mono ρ supply lt.supply
                                              (Nat.le_trans hs1 hst) hfresh
                                          have hlastE1 : lastVal < lt.supply :=
                                            Nat.lt_of_lt_of_le hlast1 hst
                                          have hfrE :=
                                            lowerStmtsCFG_bindArm_fresh
                                              budget _ _ _ _ _ _ _ _ _ he
                                              hEl hfE1 hlastE1
                                          have hfreshE : ∀ id srcE,
                                              id ∈ mergeIds ρ lt.ρ le.ρ →
                                              rhoLookup le.ρ id =
                                              some srcE →
                                              srcE < le.supply + 1 := by
                                            intro id srcE hmem hlook
                                            have h1 : srcE < le.supply :=
                                              hfrE id srcE
                                              (rhoLookup_some_mem le.ρ id
                                              srcE hlook)
                                            exact Nat.lt_of_lt_of_le h1
                                              (Nat.le_succ _)
                                          have hneE : ∀ id srcE,
                                              id ∈ mergeIds ρ lt.ρ le.ρ →
                                              rhoLookup le.ρ id =
                                              some srcE →
                                              srcE ≠ le.supply := by
                                            intro id srcE hmem hlook
                                            have h1 : srcE < le.supply :=
                                              hfrE id srcE
                                              (rhoLookup_some_mem le.ρ id
                                              srcE hlook)
                                            exact Nat.ne_of_lt h1
                                          cases hm : mergeIds ρ lt.ρ le.ρ with
                                          | nil =>
                                              have hmk : mkMergePhis ρ lt.ρ
                                                  le.ρ (le.supply + 1)
                                                  ((lt.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  nextB)
                                                  ((le.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  (nextB + 1))
                                                  (mergeIds ρ lt.ρ le.ρ) =
                                                  some ([], le.supply + 1,
                                                  ρ) := by
                                                rw [hm]
                                                rfl
                                              rw [hm] at h
                                              simp only [] at h
                                              cases hr : lowerStmtsCFG
                                                  (nextB + 2) none false ρ
                                                  (le.supply + 1) le.next
                                                  le.supply true none
                                                  rest with
                                              | none => rw [hr] at h; simp at h
                                              | some lr =>
                                                  rw [hr] at h
                                                  simp only [] at h
                                                  obtain rfl :=
                                                    Option.some.inj h
                                                  dsimp only at hsub ⊢
                                                  have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                      ∈ f.blocks :=
                                                    hsub _ if_asm_mem_then
                                                  have hfindT : findBlock f nextB =
                                                      some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf hTmem
                                                  have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                      ∈ f.blocks :=
                                                    hsub _ if_asm_mem_else
                                                  have hfindE : findBlock f (nextB + 1) =
                                                      some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf hEmem
                                                  have hfindJb : findBlock f
                                                      (nextB + 2) = some ⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      lr.instrs,
                                                      lr.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf
                                                      (hsub _ if_asm_mem_join)
                                                  obtain ⟨wArm, fenvT, F1',
                                                      huArm, hle, hge, heq_arm,
                                                      hrel_arm,
                                                      hreg_arm⟩ :=
                                                    ((harmE s1 lt lt.supply le
                                                    ((le.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    (nextB + 1)) ht he rfl ⟨nextB + 2,
                                                    [MIR.Instr.phi le.supply
                                                    ((lt.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    nextB) lt.val,
                                                    MIR.Instr.phi le.supply
                                                    ((le.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    (nextB + 1)) le.val] ++
                                                    lr.instrs,
                                                    lr.term⟩ hfindJb fenvC F''
                                                    (2 + max
                                                    (armBlockBound fuelB th)
                                                    (armBlockBound fuelB el) +
                                                    armBlockBound fuelB rest -
                                                    armBlockBound fuelB el)
                                                    hrelC hg_e fh env_arm
                                                    (HFlow.value u_arm)
                                                    har (fun b hb => hsub _ (if_asm_mem_of_le hb)) hfE1 hlastE1 hentryC).1 u_arm rfl)
                                                  obtain ⟨fenvJ, happJ, hrelJ,
                                                      hvmJ, -⟩ :=
                                                    bindArm_join_execE prog hmk
                                                      (Ne.symm hne_pe) rfl
                                                      hrel_arm hreg_arm
                                                      hfreshE hneE
                                                      (Nat.lt_succ_self _) hfrρ
                                                  have hentry : execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc nextB
                                                      (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                      (some bId)
                                                      ⟨nextB + 1, le.instrs,
                                                      le.term⟩ fenvC :=
                                                    execBlockFromIn_branch_false
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC ⟨nextB + 1, le.instrs,
                                                      le.term⟩ hexec_ic hbool
                                                      hfindE
                                                  have hsubR : ∀ b ∈ lt.blocks ++
                                                      [⟨nextB, lt.instrs,
                                                      lt.term⟩] ++ le.blocks ++
                                                      [⟨nextB + 1, le.instrs,
                                                      le.term⟩] ++ [⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      ([] : List Instr) ++
                                                      lr.instrs,
                                                      lr.term⟩] ++ lr.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _ hb
                                                  have hrep : ((HFlow.value
                                                      (.lit accH)).replace
                                                      (.lit wArm)) =
                                                      HFlow.value
                                                        (.lit wArm) := rfl
                                                  rw [huArm, hrep] at hrun
                                                  exact hsuffix _ _ _ _ hmk hr
                                                    hsubR (some bId)
                                                    ⟨nextB + 1, le.instrs,
                                                    le.term⟩
                                                    ((le.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    (nextB + 1)) hentry env_arm wArm
                                                    henv' out hrun (2 + max
                                                    (armBlockBound fuelB th)
                                                    (armBlockBound fuelB el) +
                                                    armBlockBound fuelB rest -
                                                    armBlockBound fuelB el)
                                                    hCtge' fenvT F1'
                                                    hle hge heq_arm
                                                    fenvJ happJ hrelJ hvmJ
                                          | cons hd tl =>
                                              rw [hm] at h
                                              simp only [] at h
                                              cases hmphi : mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                                                  ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                                                  ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                                                  (hd :: tl) with
                                              | none => rw [hmphi] at h; simp at h
                                              | some q =>
                                                  obtain ⟨mphis, s2, ρm⟩ := q
                                                  rw [hmphi] at h
                                                  simp only [] at h
                                                  cases hr : lowerStmtsCFG
                                                      (nextB + 2) none false ρm
                                                      s2 le.next
                                                      le.supply true none
                                                      rest with
                                                  | none => rw [hr] at h; simp at h
                                                  | some lr =>
                                                      rw [hr] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      dsimp only at hsub ⊢
                                                      have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                          ∈ f.blocks :=
                                                        hsub _ if_asm_mem_then
                                                      have hfindT : findBlock f nextB =
                                                          some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf hTmem
                                                      have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                          ∈ f.blocks :=
                                                        hsub _ if_asm_mem_else
                                                      have hfindE : findBlock f (nextB + 1) =
                                                          some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf hEmem
                                                      have hmk : mkMergePhis ρ lt.ρ
                                                          le.ρ (le.supply + 1)
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB)
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1))
                                                          (mergeIds ρ lt.ρ le.ρ) =
                                                          some (mphis, s2, ρm) := by
                                                        rw [hm]
                                                        exact hmphi
                                                      have hfindJb : findBlock f
                                                          (nextB + 2) = some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphis ++ lr.instrs,
                                                          lr.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      obtain ⟨wArm, fenvT, F1',
                                                          huArm, hle, hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arm⟩ :=
                                                        ((harmE s1 lt lt.supply le
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) ht he rfl ⟨nextB + 2,
                                                        [MIR.Instr.phi le.supply
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) lt.val,
                                                        MIR.Instr.phi le.supply
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) le.val] ++
                                                        mphis ++ lr.instrs,
                                                        lr.term⟩ hfindJb fenvC F''
                                                        (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB el)
                                                        hrelC hg_e fh env_arm
                                                        (HFlow.value u_arm)
                                                        har (fun b hb => hsub _ (if_asm_mem_of_le hb)) hfE1 hlastE1 hentryC).1 u_arm rfl)
                                                      obtain ⟨fenvJ, happJ, hrelJ,
                                                          hvmJ, -⟩ :=
                                                        bindArm_join_execE prog hmk
                                                          (Ne.symm hne_pe) rfl
                                                          hrel_arm hreg_arm
                                                          hfreshE hneE
                                                          (Nat.lt_succ_self _) hfrρ
                                                      have hentry : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB + 1, le.instrs,
                                                          le.term⟩ fenvC :=
                                                        execBlockFromIn_branch_false
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB + 1, le.instrs,
                                                          le.term⟩ hexec_ic hbool
                                                          hfindE
                                                      have hsubR : ∀ b ∈ lt.blocks ++
                                                          [⟨nextB, lt.instrs,
                                                          lt.term⟩] ++ le.blocks ++
                                                          [⟨nextB + 1, le.instrs,
                                                          le.term⟩] ++ [⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphis ++ lr.instrs,
                                                          lr.term⟩] ++ lr.blocks,
                                                          b ∈ f.blocks :=
                                                        fun b hb => hsub _ hb
                                                      have hrep : ((HFlow.value
                                                          (.lit accH)).replace
                                                          (.lit wArm)) =
                                                          HFlow.value
                                                            (.lit wArm) := rfl
                                                      rw [huArm, hrep] at hrun
                                                      exact hsuffix _ _ _ _ hmk hr
                                                        hsubR (some bId)
                                                        ⟨nextB + 1, le.instrs,
                                                        le.term⟩
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) hentry env_arm wArm
                                                        henv' out hrun (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB el)
                                                        hCtge' fenvT F1'
                                                        hle hge heq_arm
                                                        fenvJ happJ hrelJ hvmJ
                                      | returned e_arm =>
                                          simp only [] at hrun
                                          have hout_r : out =
                                              .returned e_arm :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          have hregCb_r : fenvC.env vc =
                                              some (.bool false) := by
                                            have hww : (.bool false) =
                                                wC :=
                                              HIR.Expr.lit.inj hrC
                                            rw [hww]
                                            exact hregC
                                          have hbool_r : fenvC.boolOf vc =
                                              some false :=
                                            boolOf_of_lit fenvC vc false
                                              hregCb_r
                                          have hg_er : F'' ≥ blockBound
                                              fuelB el + (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB el) := by
                                            have hBel : blockBound
                                                fuelB el = 1 +
                                                armBlockBound fuelB
                                                  el := rfl
                                            omega
                                          cases hmR : mergeIds ρ lt.ρ le.ρ with
                                          | nil =>
                                              rw [hmR] at h
                                              simp only [] at h
                                              cases hrR : lowerStmtsCFG
                                                  (nextB + 2) none false ρ
                                                  (le.supply + 1) le.next
                                                  le.supply true none
                                                  rest with
                                              | none =>
                                                  rw [hrR] at h
                                                  simp at h
                                              | some lrR =>
                                                  rw [hrR] at h
                                                  simp only [] at h
                                                  obtain rfl :=
                                                    Option.some.inj h
                                                  have hfindE : findBlock f (nextB + 1) =
                                                      some ⟨nextB + 1, le.instrs,
                                                      le.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf
                                                      (hsub _ if_asm_mem_else)
                                                  have hfindJb : findBlock f (nextB + 2) =
                                                      some ⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      ([] : List Instr) ++
                                                      lrR.instrs,
                                                      lrR.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf
                                                      (hsub _ if_asm_mem_join)
                                                  have hentry_r : execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc nextB
                                                      (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                      (some bId)
                                                      ⟨nextB + 1, le.instrs,
                                                      le.term⟩ fenvC :=
                                                    execBlockFromIn_branch_false
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC ⟨nextB + 1, le.instrs,
                                                      le.term⟩ hexec_ic hbool_r
                                                      hfindE
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    simp [hout_r] at hout
                                                  · intro e hout2
                                                    have hret_e : e = e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
                                                    obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                      ((harmE s1 lt lt.supply le
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) ht he rfl ⟨nextB + 2,
                                                      [MIR.Instr.phi le.supply
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) lt.val,
                                                      MIR.Instr.phi le.supply
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) le.val] ++
                                                      ([] : List Instr) ++
                                                      lrR.instrs,
                                                      lrR.term⟩ hfindJb fenvC F''
                                                      (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el)
                                                      hrelC hg_er fh env_arm
                                                      (HFlow.returned e_arm)
                                                      har (fun b hb => hsub _ (if_asm_mem_of_le hb)) (FreshAbove.mono ρ supply lt.supply (Nat.le_trans hs1 hst) hfresh) (Nat.lt_of_lt_of_le hlast1 hst) hentryC).2 e_arm rfl)
                                                    exact ⟨w_e, hret_e.trans hu_e,
                                                      hentry_r.trans heq_e⟩
                                          | cons hdR tlR =>
                                              rw [hmR] at h
                                              simp only [] at h
                                              cases hmphiR : mkMergePhis ρ lt.ρ le.ρ
                                                  (le.supply + 1)
                                                  ((lt.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  nextB)
                                                  ((le.blocks.getLast?.map
                                                  (fun b => b.id)).getD
                                                  (nextB + 1))
                                                  (hdR :: tlR) with
                                              | none =>
                                                  rw [hmphiR] at h
                                                  simp at h
                                              | some qR =>
                                                  obtain ⟨mphisR, s2R,
                                                      ρmR⟩ := qR
                                                  rw [hmphiR] at h
                                                  simp only [] at h
                                                  cases hrR : lowerStmtsCFG
                                                      (nextB + 2) none false
                                                      ρmR s2R le.next
                                                      le.supply true none
                                                      rest with
                                                  | none =>
                                                      rw [hrR] at h
                                                      simp at h
                                                  | some lrR =>
                                                      rw [hrR] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      have hfindE : findBlock f (nextB + 1) =
                                                          some ⟨nextB + 1, le.instrs,
                                                          le.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_else)
                                                      have hfindJb : findBlock f (nextB + 2) =
                                                          some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphisR ++
                                                          lrR.instrs,
                                                          lrR.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      have hentry_r : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB + 1, le.instrs,
                                                          le.term⟩ fenvC :=
                                                        execBlockFromIn_branch_false
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB + 1, le.instrs,
                                                          le.term⟩ hexec_ic hbool_r
                                                          hfindE
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        simp [hout_r] at hout
                                                      · intro e hout2
                                                        have hret_e : e = e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                              hout2)).symm
                                                        obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                          ((harmE s1 lt lt.supply le
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) ht he rfl ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          mphisR ++
                                                          lrR.instrs,
                                                          lrR.term⟩ hfindJb fenvC F''
                                                          (2 + max
                                                          (armBlockBound fuelB th)
                                                          (armBlockBound fuelB el) +
                                                          armBlockBound fuelB rest -
                                                          armBlockBound fuelB el)
                                                          hrelC hg_er fh env_arm
                                                          (HFlow.returned e_arm)
                                                          har (fun b hb => hsub _ (if_asm_mem_of_le hb)) (FreshAbove.mono ρ supply lt.supply (Nat.le_trans hs1 hst) hfresh) (Nat.lt_of_lt_of_le hlast1 hst) hentryC).2 e_arm rfl)
                                                        exact ⟨w_e, hret_e.trans hu_e,
                                                          hentry_r.trans heq_e⟩
                                      | broke =>
                                          simp only [] at hrun
                                          have hout_r : out = .broke :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hout_r] at hout
                                          · intro e hout2
                                            simp [hout_r] at hout2
                                      | continued =>
                                          simp only [] at hrun
                                          have hout_r : out = .continued :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hout_r] at hout
                                          · intro e hout2
                                            simp [hout_r] at hout2
                                      | stuck =>
                                          simp only [] at hrun
                                          have hout_r : out = .stuck :=
                                            (congrArg Prod.fst
                                              hrun).symm
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hout_r] at hout
                                          · intro e hout2
                                            simp [hout_r] at hout2
                          | int _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | string _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | pointer _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | float _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | unit =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | undef =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | some _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | none =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | ok _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | err _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | tuple_ _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | array_ _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | loc _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | closure _ _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2

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

/-- Top corollary (C3 exit): a closed lowered program runs the oracle's value.
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
                          hr hrs
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
                              hr hrs
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

/-! ## The lowered CFG runs
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


These are evidence, not the theorem: the same expression in both arms would pass
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

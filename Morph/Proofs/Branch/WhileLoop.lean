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

/-!
# Stage C loop execution core: `whileLoop_correct`

Eleventh proof leaf out of the `HIRToMIRBranch` monolith: the loop
execution core (moved verbatim, ~1.7k lines). It chains entry phis,
cond, body, and back-edge phis across exactly the oracle's iterations,
citing the Spine leaf; `lowerStmtsCFG_total`'s `whileStmt` case cites
exactly this interface.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- NOTE (Stage C hard gate C7-loop, refined). The while-loop execution
core: the MIR
entry block (`goto` header) runs the header phis, the re-evaluated
condition, and the body assembly for exactly the oracle's iterations, reaching the exit block with a related environment (value case)
or returning the body's value (returned case). The proof decomposes into
three additive pieces: (1) a LoopStmts body-spine worker that threads the
header-phis through one body iteration (closed bodies bind, so the existing
arm workers do not chain iterations); (2) an arm-continued (header-reaching)
lemma lifting each if-arm inside the body to the back-edge; (3) header-phi
chaining tying carried registers to the HIR env across iterations. Note
`arm_total`/`arm_broke` are both loop-parametric (they already cover if-arms
inside loop bodies), so the gap is strictly the spine worker plus (2)-(3).
The fuel inequality `fh ≤ fuelB` (loop fuel adequacy, cf. the worker's new
hypothesis) funds `(fh + 1)` iterations. Deferred; the `whileStmt` case of
`lowerStmtsCFG_total` cites exactly this interface.

WARNING (former soundness obstruction, now fixed at the fragment level): the
statement used to be FALSE as written — a body declaring a fresh variable
(`while false { varDecl x … }`) lowered fine with zero oracle iterations,
but `lb.ρ ∋ (x, _)` while `x` was unbound in `henv`, so `RelEnv env' lb.ρ _`
failed (see `RelEnv_of_lookup_none` and the refusal pin above). The
`loop = some` refusal plus the `ρb`-restoring and break-snapshot changes
remove both known counterexamples; what remains is proving the spine.

Loop 183 probing (operational miscompilation, same root cause):
`x = 5; while (x < 2) { x = x + 1 }; x` runs zero trips, so HIR yields
`value (lit (int 5))`, but `lowerProgramCFG` + `execFuncFrom 19` yields `none`
— the post-loop `rest` reads the body's exit register, which was never
assigned on the zero-trip path (repro in /tmp/probe_zero.lean). So even
`assign`-only bodies miscompile on zero trips: any body binding breaks the
zero-trip path, not just `varDecl`. The `ifStmtBreak` predicate already
handles the symmetric break-skips-tail hazard (binding tails after
breakable `if`s are refused), but nothing guards zero trips.
Fix implemented in the lowering: `rest` is lowered under the body-entry env
`ρb` (carried ids already read the phi registers there, and non-carried ids
are untouched by bodies in-fragment), `varDecl` under `loop = some` is
refused in `lowerStmtsCFG` (declarations push and escape; even shadowed ones
break zero trips — pinned by the `= none` example above), and `break`
snapshots carried regs (like `continue`) so the phi reads break-time values.
The loop-exit block seeds `lb.supply` (rest's entry accumulator) with unit,
not `lr.supply` (rest's exit reg, which rest never reads before writing): with
the wrong seed nothing in the loop's blocks ever wrote `lb.supply`, so the
spine's `fenvX.env lb.supply = unit` conjunct was unprovable. This keeps
`whileCountProg` (counter via `assign`, pinned passing) while making zero
trips sound. Exit-copy remediation was considered and rejected:
replaying carried regs into body-exit regs clobbers under register aliasing
(`x = y` aliases `v_y`), which `VarFree` excludes in-fragment but the
lowering still accepts out-of-fragment. The `break` snapshot is wired
through `CarriedExcl` hypotheses in `lowerStmtsCFG_arm_broke` (proved via
`carryCopies_exec`, with `mkCarried_excl` deriving exclusivity and
`mkCarried_reg_inj` giving distinctness from `hmk`).
Closed hard gate (the former gap in `header_loop_correct`'s
`continued` branch): the four `whileLoop_correct` recursion leaves (value
and continued bodies × value and returned conclusions) now cite
`header_loop_correct`, which chains entry phis, cond, body, back-edge phis
(`headerPhis_exec_back`), and the fuel IH. Pieces (1)-(4) from the old note
all landed: edge distinctness is proved inline (`hfallNe`/`htrNe` from
`loopBody_inv` bounds), `arm_continued` and the loopBody `continued`
selector exist, and `conv_backRelEnv` re-establishes `RelEnv`. What closed it
is `header_loop_correct`'s `continued` case: synthesizing
`RelEnv envB lb.ρ` for the back-edge phis from the continued selector's
carried-bindings + frame (the value selector's `RelEnv` is unavailable
there). The naive fix — strengthening `lowerStmtsCFG_loopBody_run`'s continued
conjunct with `RelEnv henv' L.ρ` — is FALSE: a continued arm skips `rest`
(`runHIRStmts` returns `(f, env')` directly for non-value arm outcomes), but
`L.ρ` is `rest`'s exit env lowered under the pre-branch `ρ`, so its fresh
regs are unwritten on that path (e.g. `if c then continue else skip; x = 1`).
What the header needs instead is `RelEnv` under the body-ENTRY env `ρb`,
dispatched on the arrival predecessor `blkPrev`: (a) `blkPrev ∈ tramps` —
trampoline self-copies are identity (`headerPhis_tramp_hit_exec`) and
`cont_post_RelEnv` restores `RelEnv envB ρb` from the selector's carried
binds + frame via `spine_P` + `runHIRStmts_loopBody_lookup` (no `lb.ρ`
needed); (b) `blkPrev ∉ tramps`, `≠ fallEnd` — every phi misses
(`headerPhis_miss_exec`) + same `cont_post_RelEnv`; (c) `blkPrev = fallEnd`
— the back phi fires and needs carried ids' EXIT-reg values, a new worker
fact (only reachable via trailing-`continue` in `rest`). -/
theorem whileLoop_correct (budget : Nat) :
    ∀ (bId nextB : MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply : Nat)
      (c : HIR.Expr) (body rest : List HIR.Stmt)
      (carried : List (HIR.Id × ValId)) (sA : Nat) (ρb : List (HIR.Id × ValId))
      (vc : ValId) (ic : List MIR.Instr) (s1 : Nat)
      (lb lr : Lowered) (phis : List MIR.Instr),
      mkCarried ρ supply
          ((dedupIds (assignedIds body)).filterMap
            (fun id => (rhoLookup ρ id).map (fun _ => id))) =
          some (carried, sA, ρb) →
      lowerExpr ρb sA c = some (vc, ic, s1) →
      lowerStmtsCFG (nextB + 2) (some nextB) false ρb (s1 + 1) (nextB + 3) s1
          true (some ⟨nextB, nextB + 1, carried⟩) body = some lb →
      lowerStmtsCFG (nextB + 1) none false ρb (lb.supply + 1) lb.next
          lb.supply true none rest = some lr →
      mkHeaderPhis ρ bId carried
          ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
          (lb.blocks.filterMap (fun b =>
            match b.terminator with
            | .goto t =>
                if t == nextB &&
                    b.id != (lb.blocks.getLast?.map fun b => b.id).getD
                      (nextB + 2) then
                  some b.id
                else none
            | _ => none)) = some phis →
      LoopStmts budget body →
      BranchStmts budget rest →
      IsStraight c → SLWeight c < budget →
      FreshAbove ρ supply → bId < nextB →
      ∀ (fh : Nat) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      ∀ (res : HFlow) (env' : HEnv),
      runHIRWhile fh henv c body = (res, env') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId) (F : Nat),
      (∀ b ∈ lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs,
          lb.term⟩] ++
          [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
          [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++
          lr.blocks,
        b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB : Nat),
      F ≥ 1 + ((2 + armBlockBound fuelB body) * (fh + 1) +
        armBlockBound fuelB rest) →
      FreshAbove ρb (lb.supply + 1) ∧
      ((res = .value (.lit .unit)) →
        ∃ F' fenvX, F' ≤ F ∧ F' ≥ 1 + armBlockBound fuelB rest ∧
          execBlockFromIn prog F f prev ⟨bId, [], .goto nextB⟩ fenv =
            execBlockFromIn prog F' f (some (nextB + 1))
              ⟨nextB + 1, lr.instrs, lr.term⟩ fenvX ∧
          RelEnv env' ρb fenvX.env ∧ fenvX.env lb.supply = some .unit) ∧
      ((∀ (e : HIR.Expr), res = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f prev ⟨bId, [], .goto nextB⟩ fenv =
            some w_e)) := by
  intro bId nextB ρ supply c body rest carried sA ρb vc ic s1 lb lr phis hmk
    hcond hbody hrest hphis hloop hrestP hstr hlt hfresh hltB fh
  have hfrX : FreshAbove ρb (lb.supply + 1) :=
    whileLoop_correct_fresh budget bId nextB ρ supply c body rest carried sA ρb
      vc ic s1 lb lr phis hmk hcond hbody hrest hphis hloop hrestP hstr hlt
      hfresh
  induction fh with
  | zero =>
      intro henv fenv hrel res env' hrun prog f prev F hsub hnodf fuelB hF
      refine ⟨hfrX, ?_, ?_⟩
      · intro hres
        rw [runHIRWhile_zero_eq] at hrun
        have hst : res = .stuck := (congrArg Prod.fst hrun).symm
        rw [hst] at hres
        exact absurd hres (by simp)
      · intro e he
        rw [runHIRWhile_zero_eq] at hrun
        have hst : res = .stuck := (congrArg Prod.fst hrun).symm
        rw [hst] at he
        exact absurd he (by simp)
  | succ fh ih =>
      intro henv fenv hrel res env' hrun prog f prev F hsub hnodf fuelB hF
      refine ⟨hfrX, ?_, ?_⟩
      · intro hres
        simp only [runHIRWhile] at hrun
        cases heval : evalHIR 256 henv c with
        | none =>
            rw [heval] at hrun
            have hst : res = .stuck := (congrArg Prod.fst hrun).symm
            rw [hst] at hres
            exact absurd hres (by simp)
        | some r =>
            rw [heval] at hrun
            cases r with
            | lit w =>
                cases w with
                | bool b =>
                    cases b with
                    | false =>
                        simp only [] at hrun
                        have hpair : (res, env') = ((.value (.lit .unit)), henv) := by
                          rw [hrun]
                        have henvEq : env' = henv := congrArg Prod.snd hpair
                        have hresEq : res = .value (.lit .unit) := hres
                        subst env'
                        -- exit path: header entry phis + cond-false + exit const
                        have hmemH : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
                            lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                            [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                            [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by
                          simp
                        have hmemE : (⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ : Block) ∈
                            lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                            [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                            [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by
                          simp
                        have hfindH : findBlock f nextB =
                            some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
                          findBlock_of_nodup_mem hnodf (hsub _ hmemH)
                        have hfindE : findBlock f (nextB + 1) =
                            some ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ :=
                          findBlock_of_nodup_mem hnodf (hsub _ hmemE)
                        have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
                            match a with
                            | none => none
                            | some ps =>
                                match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                                | some entrySrc, some backSrc =>
                                    some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                                      (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                                | _, _ => none) (some []) = some phis := by
                          simpa [mkHeaderPhis] using hphis
                        obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
                          ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                          (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                          carried [] phis hfold
                        have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
                          have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                          have hbnd := hinv.2.2.1
                          cases hgl : lb.blocks.getLast? with
                          | none =>
                              simp only [hgl, Option.map_none, Option.getD_none]
                              exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
                          | some bb =>
                              have hm : bb ∈ lb.blocks := getLast?_mem hgl
                              have hb := hbnd bb hm
                              simp only [hgl, Option.map_some, Option.getD_some]
                              have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                              exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                        have htrNe : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)), t ≠ bId := by
                          intro t ht
                          have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                          have hbnd := hinv.2.2.1
                          have hmemF : ∃ b ∈ lb.blocks, t = b.id := by
                            rw [List.mem_filterMap] at ht
                            obtain ⟨b, hb, hfb⟩ := ht
                            cases htb : b.terminator with
                            | goto tt =>
                                simp only [htb] at hfb
                                by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                                · simp only [hC, if_true] at hfb
                                  exact ⟨b, hb, (Option.some.inj hfb).symm⟩
                                · simp only [hC, if_false] at hfb
                                  exact absurd hfb (by simp)
                            | _ =>
                                simp only [htb] at hfb
                                exact absurd hfb (by simp)
                          obtain ⟨b, hb, rfl⟩ := hmemF
                          have hb2 := hbnd b hb
                          have hle : nextB ≤ b.id := Nat.le_trans (Nat.le_add_right _ _) hb2.1
                          exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                        have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
                        have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
                        have hleCar : ∀ q ∈ carried, supply ≤ q.2 := fun q hq => mkCarried_mem_lo hmk hq
                        have hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried → r₁ = r₂ → id₁ = id₂ := by
                          intro a b c d h1 h2 he
                          subst he
                          exact mkCarried_reg_inj hmk h1 h2
                        have hphiEq : phis = (carried.map phif).flatten := by rw [hflat]; simp
                        obtain ⟨fenvP, hexP, hrelP, hvalP, hframeP⟩ :=
                          headerPhis_exec_entry ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                            (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                            carried phif hphif hfallNe htrNe supply hfresh hleCar hdistC prog fenv henv hrel
                        rw [←hphiEq] at hexP
                        have hrelPb : RelEnv henv ρb fenvP.env := by
                          intro id u hlook
                          rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                          · subst hid
                            subst hu
                            obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hphif (id, u) hmem
                            obtain ⟨w, hlookH, hreg⟩ := hrel id esrc he1
                            refine ⟨w, hlookH, ?_⟩
                            exact hvalP id u w hmem hlookH
                          · obtain ⟨w, hlookH, hreg⟩ := hrel id u hbase
                            refine ⟨w, hlookH, ?_⟩
                            have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
                            have hnotin : ∀ idx, (idx, u) ∉ carried := by
                              intro idx hcon
                              have hle := mkCarried_mem_lo hmk hcon
                              exact absurd hle (Nat.not_le_of_gt hlt)
                            rw [hframeP u hnotin]
                            exact hreg
                        have hfrP : FreshAbove ρb sA := FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
                        obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                          lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt hfrP henv fenvP hrelPb prog (some bId) _ heval
                        have hrw : (HIR.Expr.lit (.bool false)) = HIR.Expr.lit wc := hrc
                        have hwc : wc = .bool false := (HIR.Expr.lit.inj hrw).symm
                        subst hwc
                        have hbool : fenvC.boolOf vc = some false := boolOf_of_lit fenvC vc false hregC
                        have hexPhiIc : execInstrsFullFromIn prog (some bId) fenv (phis ++ ic) = some fenvC := by
                          rw [execInstrsFullFromIn_append prog (some bId) fenv phis ic, hexP]
                          simp only [Option.some.injEq] at hexC ⊢
                          rw [execInstrsFullFromIn_of_noPhi] at hexC ⊢
                          · exact hexC
                          · intro d p src hm
                            exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                          · intro d p src hm
                            exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                        have h1le : 2 ≤ (2 + armBlockBound fuelB body) := by omega
                        have h2le : 1 ≤ (fh + 1 + 1) := by omega
                        have hmul : 2 * 1 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.mul_le_mul h1le h2le
                        have hF3 : F ≥ 3 := by omega
                        obtain ⟨Fmid, rfl⟩ : ∃ n, F = n + 3 := ⟨F - 3, by omega⟩
                        have hF'ge : Fmid + 1 ≥ 1 + armBlockBound fuelB rest := by omega
                        have hF'le : Fmid + 1 ≤ Fmid + 3 := by omega
                        refine ⟨Fmid + 1, ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩, hF'le, hF'ge, ?_, ?_, ?_⟩
                        · have hexec0 : execInstrsFullFromIn prog prev fenv ([] : List MIR.Instr) = some fenv := by
                            simp [execInstrsFullFromIn_eq]
                          have hgoto : execBlockFromIn prog (Fmid + 3) f prev ⟨bId, [], .goto nextB⟩ fenv =
                              execBlockFromIn prog (Fmid + 2) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv :=
                            execBlockFromIn_goto prog (Fmid + 2) f prev bId [] nextB fenv fenv ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ hexec0 hfindH
                          have hbranch : execBlockFromIn prog (Fmid + 2) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv =
                              execBlockFromIn prog (Fmid + 1) f (some nextB) ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ fenvC :=
                            execBlockFromIn_branch_false prog (Fmid + 1) f (some bId) nextB (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv fenvC ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ hexPhiIc hbool hfindE
                          have hnp_lr : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ lr.instrs := by
                            intro d p src hm
                            have hpure := lowerStmtsCFG_instrs_pure (nextB + 1) none false ρb (lb.supply + 1) lb.next lb.supply true rest lr hrest _ hm
                            exact IsPure_not_phi hpure d p src rfl
                          have hconst : execInstrsFullFromIn prog (some nextB) fenvC [MIR.Instr.const lb.supply Value.unit] =
                              some ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ := by
                            simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                          have hexit : execBlockFromIn prog (Fmid + 1) f (some nextB) ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ fenvC =
                              execBlockFromIn prog (Fmid + 1) f (some (nextB + 1)) ⟨nextB + 1, lr.instrs, lr.term⟩ ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ := by
                            cases hFmid : Fmid with
                            | zero =>
                                simp only [execBlockFromIn, hconst]
                                have happ : execInstrsFullFromIn prog (some nextB) fenvC (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ lr.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const lb.supply Value.unit] lr.instrs
                                  simp only at happ0
                                  rw [hconst] at happ0
                                  simpa using happ0
                                rw [happ]
                                have heq1 : execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ lr.instrs =
                                    execInstrsFullFromIn prog (some (nextB + 1)) ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ lr.instrs := by
                                  rw [execInstrsFullFromIn_of_noPhi prog (some nextB) _ lr.instrs hnp_lr, execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _ lr.instrs hnp_lr]
                                rw [heq1]
                            | succ n =>
                                simp only [execBlockFromIn]
                                have happ : execInstrsFullFromIn prog (some nextB) fenvC (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ lr.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const lb.supply Value.unit] lr.instrs
                                  simp only at happ0
                                  rw [hconst] at happ0
                                  simpa using happ0
                                rw [happ]
                                have heq1 : execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ lr.instrs =
                                    execInstrsFullFromIn prog (some (nextB + 1)) ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ lr.instrs := by
                                  rw [execInstrsFullFromIn_of_noPhi prog (some nextB) _ lr.instrs hnp_lr, execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _ lr.instrs hnp_lr]
                                rw [heq1]
                          exact hgoto.trans (hbranch.trans hexit)
                        · have hrelC : RelEnv henv ρb fenvC.env := by
                            have hexPure : execInstrsFull fenvP ic = some fenvC := by
                              have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                intro d p src hm
                                exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                              have h1 : execInstrsFullFromIn prog (some bId) fenvP ic = execInstrsFull fenvP ic := execInstrsFullFromIn_of_noPhi prog (some bId) fenvP ic hnp
                              rw [h1] at hexC
                              exact hexC
                            exact RelEnv_exec henv ρb sA c vc ic s1 hcond fenvP fenvC hrelPb hfrP hexPure
                          have hlb : s1 + 1 ≤ lb.supply :=
                            (lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop).2.1
                          intro id u hlook
                          obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                          refine ⟨w, hlookH, ?_⟩
                          by_cases heq : u = lb.supply
                          · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                            have h1 : lb.supply < sA := heq ▸ hlt
                            have hlt2 : sA < lb.supply := Nat.lt_of_le_of_lt hsA (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlb)
                            have hcontra : lb.supply < lb.supply := Nat.lt_trans h1 hlt2
                            exact absurd hcontra (Nat.lt_irrefl _)
                          · have hbeq : ¬ (u == lb.supply) := by simpa using heq
                            simp only [Env.update, hbeq]
                            exact hreg
                        · simp [Env.update]
                    | true =>
                        simp only [] at hrun
                        cases hbrun : runHIRStmts fh henv body (.value (.lit .unit)) with
                        | mk out envB =>
                            rw [hbrun] at hrun
                            cases out with
                            | value u =>
                                simp only [] at hrun
                                have hrem : runHIRWhile fh envB c body = (res, env') := hrun
                                have hmemH : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemB : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hfindH : findBlock f nextB =
                                    some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemH)
                                have hfindB : findBlock f (nextB + 2) =
                                    some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemB)
                                have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
                                    match a with
                                    | none => none
                                    | some ps =>
                                        match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                                        | some entrySrc, some backSrc =>
                                            some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                                              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                                        | _, _ => none) (some []) = some phis := by
                                  simpa [mkHeaderPhis] using hphis
                                obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
                                  ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                  (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                  carried [] phis hfold
                                have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  cases hgl : lb.blocks.getLast? with
                                  | none =>
                                      simp only [hgl, Option.map_none, Option.getD_none]
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
                                  | some bb =>
                                      have hm : bb ∈ lb.blocks := getLast?_mem hgl
                                      have hb := hbnd bb hm
                                      simp only [hgl, Option.map_some, Option.getD_some]
                                      have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have htrNe : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)), t ≠ bId := by
                                  intro t ht
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  have hmemF : ∃ b ∈ lb.blocks, t = b.id := by
                                    rw [List.mem_filterMap] at ht
                                    obtain ⟨b, hb, hfb⟩ := ht
                                    cases htb : b.terminator with
                                    | goto tt =>
                                        simp only [htb] at hfb
                                        by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                                        · simp only [hC, if_true] at hfb
                                          exact ⟨b, hb, (Option.some.inj hfb).symm⟩
                                        · simp only [hC, if_false] at hfb
                                          exact absurd hfb (by simp)
                                    | _ =>
                                        simp only [htb] at hfb
                                        exact absurd hfb (by simp)
                                  obtain ⟨b, hb, rfl⟩ := hmemF
                                  have hb2 := hbnd b hb
                                  have hle : nextB ≤ b.id := Nat.le_trans (Nat.le_add_right _ _) hb2.1
                                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
                                have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
                                have hleCar : ∀ q ∈ carried, supply ≤ q.2 := fun q hq => mkCarried_mem_lo hmk hq
                                have hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried → r₁ = r₂ → id₁ = id₂ := by
                                  intro a b c d h1 h2 he
                                  subst he
                                  exact mkCarried_reg_inj hmk h1 h2
                                have hphiEq : phis = (carried.map phif).flatten := by rw [hflat]; simp
                                obtain ⟨fenvP, hexP, hrelP, hvalP, hframeP⟩ :=
                                  headerPhis_exec_entry ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                    (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                    carried phif hphif hfallNe htrNe supply hfresh hleCar hdistC prog fenv henv hrel
                                rw [←hphiEq] at hexP
                                have hrelPb : RelEnv henv ρb fenvP.env := by
                                  intro id u hlook
                                  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                                  · subst hid
                                    subst hu
                                    obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hphif (id, u) hmem
                                    obtain ⟨w, hlookH, hreg⟩ := hrel id esrc he1
                                    refine ⟨w, hlookH, ?_⟩
                                    exact hvalP id u w hmem hlookH
                                  · obtain ⟨w, hlookH, hreg⟩ := hrel id u hbase
                                    refine ⟨w, hlookH, ?_⟩
                                    have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
                                    have hnotin : ∀ idx, (idx, u) ∉ carried := by
                                      intro idx hcon
                                      have hle := mkCarried_mem_lo hmk hcon
                                      exact absurd hle (Nat.not_le_of_gt hlt)
                                    rw [hframeP u hnotin]
                                    exact hreg
                                have hfrP : FreshAbove ρb sA := FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
                                obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                                  lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt hfrP henv fenvP hrelPb prog (some bId) _ heval
                                have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                                have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                                subst hwc
                                have hbool : fenvC.boolOf vc = some true := boolOf_of_lit fenvC vc true hregC
                                have hexPhiIc : execInstrsFullFromIn prog (some bId) fenv (phis ++ ic) = some fenvC := by
                                  have happ := execInstrsFullFromIn_append prog (some bId) fenv phis ic
                                  simp only [happ, hexP, hexC]
                                have hrelC : RelEnv henv ρb fenvC.env := by
                                  have hexPure : execInstrsFull fenvP ic = some fenvC := by
                                    have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                      intro d p src hm
                                      exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                                    have h1 : execInstrsFullFromIn prog (some bId) fenvP ic = execInstrsFull fenvP ic := execInstrsFullFromIn_of_noPhi prog (some bId) fenvP ic hnp
                                    rw [h1] at hexC
                                    exact hexC
                                  exact RelEnv_exec henv ρb sA c vc ic s1 hcond fenvP fenvC hrelPb hfrP hexPure
                                have hconstB : execInstrsFullFromIn prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] =
                                    some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                have hfreshB : FreshAbove ρb (s1 + 1) := FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
                                have hrelB0 : RelEnv henv ρb (fenvC.env.update s1 Value.unit) := by
                                  intro id u hlook
                                  obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                                  refine ⟨w, hlookH, ?_⟩
                                  by_cases heq : u = s1
                                  · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                    have hcontra : s1 < sA := heq ▸ hlt
                                    omega
                                  · have hbeq : ¬ (u == s1) := by simpa using heq
                                    simp only [Env.update, hbeq]
                                    exact hreg
                                have haccB0 : (fenvC.env.update s1 Value.unit) s1 = some Value.unit := by simp [Env.update]
                                have hB2 : 2 ≤ 2 + armBlockBound fuelB body := Nat.le_add_right _ _
                                have hfh2 : 2 ≤ fh + 1 + 1 := by omega
                                have hmul : 2 * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.mul_le_mul hB2 hfh2
                                have hF5 : F ≥ 5 := by omega
                                obtain ⟨Fmid, rfl⟩ : ∃ n, F = n + 5 := ⟨F - 5, by omega⟩
                                have hexec0 : execInstrsFullFromIn prog prev fenv ([] : List MIR.Instr) = some fenv := by
                                  simp [execInstrsFullFromIn_eq]
                                have hgoto : execBlockFromIn prog (Fmid + 5) f prev ⟨bId, [], .goto nextB⟩ fenv =
                                    execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv := by
                                  have hF5e : Fmid + 5 = (Fmid + 4) + 1 := by omega
                                  rw [hF5e]
                                  exact execBlockFromIn_goto prog (Fmid + 4) f prev bId [] nextB fenv fenv _ hexec0 hfindH
                                have hbranchT : execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC := by
                                  have hF4 : Fmid + 4 = (Fmid + 3) + 1 := by omega
                                  rw [hF4]
                                  exact execBlockFromIn_branch_true prog (Fmid + 3) f (some bId) nextB (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv fenvC _ hexPhiIc hbool hfindB
                                have happB : execInstrsFullFromIn prog (some nextB) fenvC ([MIR.Instr.const s1 Value.unit] ++ lb.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ lb.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                                  simp only at happ0
                                  rw [hconstB] at happ0
                                  simpa using happ0
                                have hbodyConst : execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, lb.instrs, lb.term⟩ ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  have hF3 : Fmid + 3 = (Fmid + 2) + 1 := by omega
                                  rw [hF3]
                                  exact execBlockFromIn_instrs_prefix prog (Fmid + 2) f (some nextB) (nextB + 2) [MIR.Instr.const s1 Value.unit] lb.instrs lb.term fenvC ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ happB
                                have hexpand : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                    (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) := by
                                  have h1 : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                      (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) * 1 := by
                                    rw [Nat.mul_add]
                                  rw [h1, Nat.mul_one]
                                rw [hexpand] at hF
                                have hFH : Fmid + 3 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + armBlockBound fuelB rest := by omega
                                have hmemLb : ∀ b ∈ lb.blocks, b ∈ f.blocks :=
                                  fun b hb => hsub _ (List.mem_append_left _ (List.mem_append_left _
                                    (List.mem_append_left _ (List.mem_append_left _ hb))))
                                have hsubH : (∀ b ∈ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks,
                                  b ∈ f.blocks) := by
                                  intro b hb
                                  apply hsub
                                  rcases List.mem_append.mp hb with h | h
                                  · rcases List.mem_append.mp h with h | h
                                    · rcases List.mem_append.mp h with h | h
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_left _ (List.mem_append_right lb.blocks h)))
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_right (lb.blocks ++
                                            [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) h))
                                    · exact List.mem_append_left _ (List.mem_append_right
                                        ((lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) ++
                                          [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩]) h)
                                  · exact List.mem_append_right _ h
                                have hH := header_loop_correct budget bId nextB ρ supply c body rest carried sA ρb vc ic s1 lb lr phis
                                  hmk hcond hbody hrest hphis hloop hrestP hstr hlt hfresh hltB fh henv
                                  ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ (HFlow.value u) envB hrelB0 haccB0 hbrun
                                  res env' (Or.inl ⟨u, rfl⟩) (by intro h; simp at h) (by intro h; simp at h)
                                  (fun u' _ => hrem) prog f (Fmid + 3) hmemLb hsubH hnodf fuelB
                                  (armBlockBound fuelB rest) hFH (Nat.le_refl _)
                                obtain ⟨F', fenvX, hleF, hgeF, hexecH, hrelX, haccX⟩ := hH.1 hres
                                refine ⟨F', fenvX, Nat.le_trans hleF (by omega), hgeF, ?_, hrelX, haccX⟩
                                exact hgoto.trans (hbranchT.trans (hbodyConst.trans hexecH))
                            | returned er =>
                                simp only [] at hrun
                                have hst : res = .returned er := (congrArg Prod.fst hrun).symm
                                rw [hst] at hres
                                exact absurd hres (by simp)
                            | broke =>
                                simp only [] at hrun
                                have hpairB : (res, env') = ((.value (.lit .unit)), envB) := by rw [hrun]
                                have henvBEq : env' = envB := congrArg Prod.snd hpairB
                                subst env'
                                have hmemH : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemB : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemE : (⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hfindH : findBlock f nextB =
                                    some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemH)
                                have hfindB : findBlock f (nextB + 2) =
                                    some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemB)
                                have hfindE : findBlock f (nextB + 1) =
                                    some ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemE)
                                have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
                                    match a with
                                    | none => none
                                    | some ps =>
                                        match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                                        | some entrySrc, some backSrc =>
                                            some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                                              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                                        | _, _ => none) (some []) = some phis := by
                                  simpa [mkHeaderPhis] using hphis
                                obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
                                  ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                  (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                  carried [] phis hfold
                                have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  cases hgl : lb.blocks.getLast? with
                                  | none =>
                                      simp only [Option.map_none, Option.getD_none]
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
                                  | some bb =>
                                      have hm : bb ∈ lb.blocks := getLast?_mem hgl
                                      have hb := hbnd bb hm
                                      simp only [hgl, Option.map_some, Option.getD_some]
                                      have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have htrNe : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)), t ≠ bId := by
                                  intro t ht
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  have hmemF : ∃ b ∈ lb.blocks, t = b.id := by
                                    rw [List.mem_filterMap] at ht
                                    obtain ⟨b, hb, hfb⟩ := ht
                                    cases htb : b.terminator with
                                    | goto tt =>
                                        simp only [htb] at hfb
                                        by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                                        · simp only [hC, if_true] at hfb
                                          exact ⟨b, hb, (Option.some.inj hfb).symm⟩
                                        · simp only [hC] at hfb
                                          exact absurd hfb (by simp)
                                    | _ =>
                                        simp only [htb] at hfb
                                        exact absurd hfb (by simp)
                                  obtain ⟨b, hb, rfl⟩ := hmemF
                                  have hb2 := hbnd b hb
                                  have hle : nextB ≤ b.id := Nat.le_trans (Nat.le_add_right _ _) hb2.1
                                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
                                have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
                                have hleCar : ∀ q ∈ carried, supply ≤ q.2 := fun q hq => mkCarried_mem_lo hmk hq
                                have hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried → r₁ = r₂ → id₁ = id₂ := by
                                  intro a b c d h1 h2 he
                                  subst he
                                  exact mkCarried_reg_inj hmk h1 h2
                                have hphiEq : phis = (carried.map phif).flatten := by rw [hflat]; simp
                                obtain ⟨fenvP, hexP, hrelP, hvalP, hframeP⟩ :=
                                  headerPhis_exec_entry ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                    (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                    carried phif hphif hfallNe htrNe supply hfresh hleCar hdistC prog fenv henv hrel
                                rw [←hphiEq] at hexP
                                have hrelPb : RelEnv henv ρb fenvP.env := by
                                  intro id u hlook
                                  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                                  · subst hid
                                    subst hu
                                    obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hphif (id, u) hmem
                                    obtain ⟨w, hlookH, hreg⟩ := hrel id esrc he1
                                    refine ⟨w, hlookH, ?_⟩
                                    exact hvalP id u w hmem hlookH
                                  · obtain ⟨w, hlookH, hreg⟩ := hrel id u hbase
                                    refine ⟨w, hlookH, ?_⟩
                                    have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
                                    have hnotin : ∀ idx, (idx, u) ∉ carried := by
                                      intro idx hcon
                                      have hle := mkCarried_mem_lo hmk hcon
                                      exact absurd hle (Nat.not_le_of_gt hlt)
                                    rw [hframeP u hnotin]
                                    exact hreg
                                have hfrP : FreshAbove ρb sA := FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
                                obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                                  lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt hfrP henv fenvP hrelPb prog (some bId) _ heval
                                have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                                have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                                subst hwc
                                have hbool : fenvC.boolOf vc = some true := boolOf_of_lit fenvC vc true hregC
                                have hexPhiIc : execInstrsFullFromIn prog (some bId) fenv (phis ++ ic) = some fenvC := by
                                  have happ := execInstrsFullFromIn_append prog (some bId) fenv phis ic
                                  simp only [happ, hexP, hexC]
                                have hrelC : RelEnv henv ρb fenvC.env := by
                                  have hexPure : execInstrsFull fenvP ic = some fenvC := by
                                    have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                      intro d p src hm
                                      exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                                    have h1 : execInstrsFullFromIn prog (some bId) fenvP ic = execInstrsFull fenvP ic := execInstrsFullFromIn_of_noPhi prog (some bId) fenvP ic hnp
                                    rw [h1] at hexC
                                    exact hexC
                                  exact RelEnv_exec henv ρb sA c vc ic s1 hcond fenvP fenvC hrelPb hfrP hexPure
                                have h1le : 2 ≤ (2 + armBlockBound fuelB body) := by omega
                                have h2le : 2 ≤ (fh + 1 + 1) := by omega
                                have hmul : 2 * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.mul_le_mul h1le h2le
                                have hmul2 : 2 + armBlockBound fuelB body ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
                                have he4 : 4 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := hmul
                                have h5le : 5 ≤ 1 + ((2 + armBlockBound fuelB body) * (fh + 1 + 1) + armBlockBound fuelB rest) := by
                                  have hj : 0 ≤ armBlockBound fuelB rest := Nat.zero_le _
                                  have h1 : 4 + armBlockBound fuelB rest ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) + armBlockBound fuelB rest :=
                                    Nat.add_le_add_right he4 _
                                  omega
                                have hF5 : F ≥ 5 := Nat.le_trans h5le hF
                                obtain ⟨Fmid, rfl⟩ : ∃ n, F = n + 5 := ⟨F - 5, by omega⟩
                                have hmul3 : (2 + armBlockBound fuelB body) * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) :=
                                  Nat.mul_le_mul_left _ h2le
                                have h4B : 4 + armBlockBound fuelB body ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := by
                                  have hexpand : (2 + armBlockBound fuelB body) * 2 = 4 + armBlockBound fuelB body + armBlockBound fuelB body := by
                                    omega
                                  omega
                                have hFbody : Fmid + 3 ≥ blockBound fuelB body + (2 + armBlockBound fuelB rest) := by
                                  simp only [blockBound]
                                  have hFmid : Fmid + 5 ≥ 1 + ((2 + armBlockBound fuelB body) * (fh + 1 + 1) + armBlockBound fuelB rest) := hF
                                  omega
                                have hexcl : CarriedExcl ρb carried := mkCarried_excl hfresh hmk
                                have hsup : ∀ id r, (id, r) ∈ carried → r < s1 + 1 := by
                                  intro id r hmem
                                  have hlt : r < sA := mkCarried_mem_hi hmk hmem
                                  exact Nat.lt_of_lt_of_le hlt (Nat.le_trans hsA (Nat.le_succ _))
                                have hmemLb : ∀ b ∈ lb.blocks, b ∈ (lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++ [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++ [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks) := by
                                  intro b hb
                                  simp [hb]
                                have hsubLb : ∀ b ∈ lb.blocks, b ∈ f.blocks := fun b hb => hsub _ (hmemLb b hb)
                                have hconstB : execInstrsFullFromIn prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] =
                                    some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                have hfreshB : FreshAbove ρb (s1 + 1) := FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
                                have hrelB0 : RelEnv henv ρb (fenvC.env.update s1 Value.unit) := by
                                  intro id u hlook
                                  obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                                  refine ⟨w, hlookH, ?_⟩
                                  by_cases heq : u = s1
                                  · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                    have hcontra : s1 < sA := heq ▸ hlt
                                    omega
                                  · have hbeq : ¬ (u == s1) := by simpa using heq
                                    simp only [Env.update, hbeq]
                                    exact hreg
                                have haccB0 : (fenvC.env.update s1 Value.unit) s1 = some Value.unit := by simp [Env.update]
                                obtain ⟨Fb, fenvArr, blkPrev, hFb_le, hFb_ge, hexecB, hrelArr, hvalArr⟩ :=
                                  ((lowerStmtsCFG_loopBody_run budget (nextB + 2) ρb (s1 + 1) (nextB + 3) nextB s1 (some ⟨nextB, nextB + 1, carried⟩) ⟨nextB, nextB + 1, carried⟩ body lb rfl hbody hloop hfreshB (Nat.lt_succ_self _) 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) Value.unit henv ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ hrelB0 haccB0 fh envB .broke hbrun prog f (some nextB) (Fmid + 3) hsubLb hnodf fuelB (2 + armBlockBound fuelB rest) hFbody hexcl hsup hdistC ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ ⟨nextB + 1, .const lb.supply Value.unit :: lr.instrs, lr.term⟩ ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ hfindH hfindE hfindH).2.1 rfl)
                                have hlb : s1 + 1 ≤ lb.supply :=
                                  (lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop).2.1
                                have hnp_lr : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ lr.instrs := by
                                  intro d p src hm
                                  have hpure := lowerStmtsCFG_instrs_pure (nextB + 1) none false ρb (lb.supply + 1) lb.next lb.supply true rest lr hrest _ hm
                                  exact IsPure_not_phi hpure d p src rfl
                                have hrelRb : RelEnv envB ρb fenvArr.env := by
                                  intro id u hlook
                                  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                                  · subst hid
                                    subst hu
                                    obtain ⟨u', hLb⟩ := lowerStmtsCFG_loopBody_mem_preserv budget (nextB + 2) nextB ρb (s1 + 1) (nextB + 3) s1 _ _ body lb id u rfl hbody hloop hlook
                                    obtain ⟨w, hlookH, hreg⟩ := hrelArr id u' hLb
                                    exact ⟨w, hlookH, hvalArr id u w hmem hlookH⟩
                                  · by_cases hass : id ∈ assignedIds body
                                    · have hmemIds : id ∈ (dedupIds (assignedIds body)).filterMap (fun id => (rhoLookup ρ id).map (fun _ => id)) := by
                                        rw [List.mem_filterMap]
                                        exact ⟨id, dedupIds_mem hass, by simp [hbase]⟩
                                      obtain ⟨r, hlookB, hmemC⟩ := mkCarried_mem_lookup hmemIds hmk
                                      have hur : r = u := Option.some.inj (hlookB.symm.trans hlook)
                                      subst hur
                                      obtain ⟨u', hLb⟩ := lowerStmtsCFG_loopBody_mem_preserv budget (nextB + 2) nextB ρb (s1 + 1) (nextB + 3) s1 _ _ body lb id r rfl hbody hloop hlook
                                      obtain ⟨w, hlookH, hreg⟩ := hrelArr id u' hLb
                                      exact ⟨w, hlookH, hvalArr id r w hmemC hlookH⟩
                                    · have hLb : rhoLookup lb.ρ id = some u := by
                                        have hEq := lowerStmtsCFG_loopBody_rho_preserv budget (nextB + 2) nextB ρb (s1 + 1) (nextB + 3) s1 _ _ body lb id rfl hbody hloop hass
                                        rw [hEq]
                                        exact hlook
                                      obtain ⟨w, hlookH, hreg⟩ := hrelArr id u hLb
                                      exact ⟨w, hlookH, hreg⟩
                                have hexec0 : execInstrsFullFromIn prog prev fenv ([] : List MIR.Instr) = some fenv := by
                                  simp [execInstrsFullFromIn_eq]
                                have hgoto : execBlockFromIn prog (Fmid + 5) f prev ⟨bId, [], .goto nextB⟩ fenv =
                                    execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv := by
                                  have hF5 : Fmid + 5 = (Fmid + 4) + 1 := by omega
                                  rw [hF5]
                                  exact execBlockFromIn_goto prog (Fmid + 4) f prev bId [] nextB fenv fenv _ hexec0 hfindH
                                have hbranchT : execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC := by
                                  have hF4 : Fmid + 4 = (Fmid + 3) + 1 := by omega
                                  rw [hF4]
                                  exact execBlockFromIn_branch_true prog (Fmid + 3) f (some bId) nextB (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv fenvC _ hexPhiIc hbool hfindB
                                have happB : execInstrsFullFromIn prog (some nextB) fenvC ([MIR.Instr.const s1 Value.unit] ++ lb.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ lb.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                                  simp only at happ0
                                  rw [hconstB] at happ0
                                  simpa using happ0
                                have hbodyConst : execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, lb.instrs, lb.term⟩ ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  have hF3 : Fmid + 3 = (Fmid + 2) + 1 := by omega
                                  rw [hF3]
                                  exact execBlockFromIn_instrs_prefix prog (Fmid + 2) f (some nextB) (nextB + 2) [MIR.Instr.const s1 Value.unit] lb.instrs lb.term fenvC ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ happB
                                obtain ⟨Fbp, rfl⟩ : ∃ n, Fb = n + 1 := ⟨Fb - 1, by omega⟩
                                have hconstE : execInstrsFullFromIn prog (some blkPrev) fenvArr [MIR.Instr.const lb.supply Value.unit] =
                                    some ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ := by
                                  simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                have hexitB : execBlockFromIn prog (Fbp + 1) f (some blkPrev) ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ fenvArr =
                                    execBlockFromIn prog (Fbp + 1) f (some (nextB + 1)) ⟨nextB + 1, lr.instrs, lr.term⟩ ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ := by
                                  cases hFbp : Fbp with
                                  | zero =>
                                      simp only [execBlockFromIn, hconstE]
                                      have happ : execInstrsFullFromIn prog (some blkPrev) fenvArr (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                          execInstrsFullFromIn prog (some blkPrev) ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ lr.instrs := by
                                        have happ0 := execInstrsFullFromIn_append prog (some blkPrev) fenvArr [MIR.Instr.const lb.supply Value.unit] lr.instrs
                                        simp only at happ0
                                        rw [hconstE] at happ0
                                        simpa using happ0
                                      rw [happ]
                                      have heq1 : execInstrsFullFromIn prog (some blkPrev) ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ lr.instrs =
                                          execInstrsFullFromIn prog (some (nextB + 1)) ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ lr.instrs := by
                                        rw [execInstrsFullFromIn_of_noPhi prog (some blkPrev) _ lr.instrs hnp_lr, execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _ lr.instrs hnp_lr]
                                      rw [heq1]
                                  | succ n =>
                                      simp only [execBlockFromIn]
                                      have happ : execInstrsFullFromIn prog (some blkPrev) fenvArr (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                          execInstrsFullFromIn prog (some blkPrev) ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ lr.instrs := by
                                        have happ0 := execInstrsFullFromIn_append prog (some blkPrev) fenvArr [MIR.Instr.const lb.supply Value.unit] lr.instrs
                                        simp only at happ0
                                        rw [hconstE] at happ0
                                        simpa using happ0
                                      rw [happ]
                                      have heq1 : execInstrsFullFromIn prog (some blkPrev) ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ lr.instrs =
                                          execInstrsFullFromIn prog (some (nextB + 1)) ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩ lr.instrs := by
                                        rw [execInstrsFullFromIn_of_noPhi prog (some blkPrev) _ lr.instrs hnp_lr, execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _ lr.instrs hnp_lr]
                                      rw [heq1]
                                refine ⟨Fbp + 1, ⟨fenvArr.env.update lb.supply Value.unit, fenvArr.store⟩, by omega, by omega, ?_, ?_, ?_⟩
                                · exact hgoto.trans (hbranchT.trans (hbodyConst.trans (hexecB.trans hexitB)))
                                · intro id u hlook
                                  obtain ⟨w, hlookH, hreg⟩ := hrelRb id u hlook
                                  refine ⟨w, hlookH, ?_⟩
                                  by_cases heq : u = lb.supply
                                  · have hlt : u < sA := hfrb id u (rhoLookup_some_mem _ _ _ hlook)
                                    have h1 : lb.supply < sA := heq ▸ hlt
                                    have hlt2 : sA < lb.supply := Nat.lt_of_le_of_lt hsA (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlb)
                                    have hcontra : lb.supply < lb.supply := Nat.lt_trans h1 hlt2
                                    exact absurd hcontra (Nat.lt_irrefl _)
                                  · have hbeq : ¬ (u == lb.supply) := by simpa using heq
                                    simp only [Env.update, hbeq]
                                    exact hreg
                                · simp [Env.update]
                            | continued =>
                                simp only [] at hrun
                                have hrem : runHIRWhile fh envB c body = (res, env') := hrun
                                have hmemH : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemB : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hfindH : findBlock f nextB =
                                    some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemH)
                                have hfindB : findBlock f (nextB + 2) =
                                    some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemB)
                                have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
                                    match a with
                                    | none => none
                                    | some ps =>
                                        match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                                        | some entrySrc, some backSrc =>
                                            some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                                              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                                        | _, _ => none) (some []) = some phis := by
                                  simpa [mkHeaderPhis] using hphis
                                obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
                                  ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                  (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                  carried [] phis hfold
                                have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  cases hgl : lb.blocks.getLast? with
                                  | none =>
                                      simp only [hgl, Option.map_none, Option.getD_none]
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
                                  | some bb =>
                                      have hm : bb ∈ lb.blocks := getLast?_mem hgl
                                      have hb := hbnd bb hm
                                      simp only [hgl, Option.map_some, Option.getD_some]
                                      have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have htrNe : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)), t ≠ bId := by
                                  intro t ht
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  have hmemF : ∃ b ∈ lb.blocks, t = b.id := by
                                    rw [List.mem_filterMap] at ht
                                    obtain ⟨b, hb, hfb⟩ := ht
                                    cases htb : b.terminator with
                                    | goto tt =>
                                        simp only [htb] at hfb
                                        by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                                        · simp only [hC, if_true] at hfb
                                          exact ⟨b, hb, (Option.some.inj hfb).symm⟩
                                        · simp only [hC, if_false] at hfb
                                          exact absurd hfb (by simp)
                                    | _ =>
                                        simp only [htb] at hfb
                                        exact absurd hfb (by simp)
                                  obtain ⟨b, hb, rfl⟩ := hmemF
                                  have hb2 := hbnd b hb
                                  have hle : nextB ≤ b.id := Nat.le_trans (Nat.le_add_right _ _) hb2.1
                                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
                                have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
                                have hleCar : ∀ q ∈ carried, supply ≤ q.2 := fun q hq => mkCarried_mem_lo hmk hq
                                have hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried → r₁ = r₂ → id₁ = id₂ := by
                                  intro a b c d h1 h2 he
                                  subst he
                                  exact mkCarried_reg_inj hmk h1 h2
                                have hphiEq : phis = (carried.map phif).flatten := by rw [hflat]; simp
                                obtain ⟨fenvP, hexP, hrelP, hvalP, hframeP⟩ :=
                                  headerPhis_exec_entry ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                    (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                    carried phif hphif hfallNe htrNe supply hfresh hleCar hdistC prog fenv henv hrel
                                rw [←hphiEq] at hexP
                                have hrelPb : RelEnv henv ρb fenvP.env := by
                                  intro id u hlook
                                  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                                  · subst hid
                                    subst hu
                                    obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hphif (id, u) hmem
                                    obtain ⟨w, hlookH, hreg⟩ := hrel id esrc he1
                                    refine ⟨w, hlookH, ?_⟩
                                    exact hvalP id u w hmem hlookH
                                  · obtain ⟨w, hlookH, hreg⟩ := hrel id u hbase
                                    refine ⟨w, hlookH, ?_⟩
                                    have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
                                    have hnotin : ∀ idx, (idx, u) ∉ carried := by
                                      intro idx hcon
                                      have hle := mkCarried_mem_lo hmk hcon
                                      exact absurd hle (Nat.not_le_of_gt hlt)
                                    rw [hframeP u hnotin]
                                    exact hreg
                                have hfrP : FreshAbove ρb sA := FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
                                obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                                  lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt hfrP henv fenvP hrelPb prog (some bId) _ heval
                                have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                                have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                                subst hwc
                                have hbool : fenvC.boolOf vc = some true := boolOf_of_lit fenvC vc true hregC
                                have hexPhiIc : execInstrsFullFromIn prog (some bId) fenv (phis ++ ic) = some fenvC := by
                                  have happ := execInstrsFullFromIn_append prog (some bId) fenv phis ic
                                  simp only [happ, hexP, hexC]
                                have hrelC : RelEnv henv ρb fenvC.env := by
                                  have hexPure : execInstrsFull fenvP ic = some fenvC := by
                                    have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                      intro d p src hm
                                      exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                                    have h1 : execInstrsFullFromIn prog (some bId) fenvP ic = execInstrsFull fenvP ic := execInstrsFullFromIn_of_noPhi prog (some bId) fenvP ic hnp
                                    rw [h1] at hexC
                                    exact hexC
                                  exact RelEnv_exec henv ρb sA c vc ic s1 hcond fenvP fenvC hrelPb hfrP hexPure
                                have hconstB : execInstrsFullFromIn prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] =
                                    some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                have hfreshB : FreshAbove ρb (s1 + 1) := FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
                                have hrelB0 : RelEnv henv ρb (fenvC.env.update s1 Value.unit) := by
                                  intro id u hlook
                                  obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                                  refine ⟨w, hlookH, ?_⟩
                                  by_cases heq : u = s1
                                  · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                    have hcontra : s1 < sA := heq ▸ hlt
                                    omega
                                  · have hbeq : ¬ (u == s1) := by simpa using heq
                                    simp only [Env.update, hbeq]
                                    exact hreg
                                have haccB0 : (fenvC.env.update s1 Value.unit) s1 = some Value.unit := by simp [Env.update]
                                have hB2 : 2 ≤ 2 + armBlockBound fuelB body := Nat.le_add_right _ _
                                have hfh2 : 2 ≤ fh + 1 + 1 := by omega
                                have hmul : 2 * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.mul_le_mul hB2 hfh2
                                have hF5 : F ≥ 5 := by omega
                                obtain ⟨Fmid, rfl⟩ : ∃ n, F = n + 5 := ⟨F - 5, by omega⟩
                                have hexec0 : execInstrsFullFromIn prog prev fenv ([] : List MIR.Instr) = some fenv := by
                                  simp [execInstrsFullFromIn_eq]
                                have hgoto : execBlockFromIn prog (Fmid + 5) f prev ⟨bId, [], .goto nextB⟩ fenv =
                                    execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv := by
                                  have hF5e : Fmid + 5 = (Fmid + 4) + 1 := by omega
                                  rw [hF5e]
                                  exact execBlockFromIn_goto prog (Fmid + 4) f prev bId [] nextB fenv fenv _ hexec0 hfindH
                                have hbranchT : execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC := by
                                  have hF4 : Fmid + 4 = (Fmid + 3) + 1 := by omega
                                  rw [hF4]
                                  exact execBlockFromIn_branch_true prog (Fmid + 3) f (some bId) nextB (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv fenvC _ hexPhiIc hbool hfindB
                                have happB : execInstrsFullFromIn prog (some nextB) fenvC ([MIR.Instr.const s1 Value.unit] ++ lb.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ lb.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                                  simp only at happ0
                                  rw [hconstB] at happ0
                                  simpa using happ0
                                have hbodyConst : execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, lb.instrs, lb.term⟩ ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  have hF3 : Fmid + 3 = (Fmid + 2) + 1 := by omega
                                  rw [hF3]
                                  exact execBlockFromIn_instrs_prefix prog (Fmid + 2) f (some nextB) (nextB + 2) [MIR.Instr.const s1 Value.unit] lb.instrs lb.term fenvC ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ happB
                                have hexpand : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                    (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) := by
                                  have h1 : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                      (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) * 1 := by
                                    rw [Nat.mul_add]
                                  rw [h1, Nat.mul_one]
                                rw [hexpand] at hF
                                have hFH : Fmid + 3 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + armBlockBound fuelB rest := by omega
                                have hmemLb : ∀ b ∈ lb.blocks, b ∈ f.blocks :=
                                  fun b hb => hsub _ (List.mem_append_left _ (List.mem_append_left _
                                    (List.mem_append_left _ (List.mem_append_left _ hb))))
                                have hsubH : (∀ b ∈ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks,
                                  b ∈ f.blocks) := by
                                  intro b hb
                                  apply hsub
                                  rcases List.mem_append.mp hb with h | h
                                  · rcases List.mem_append.mp h with h | h
                                    · rcases List.mem_append.mp h with h | h
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_left _ (List.mem_append_right lb.blocks h)))
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_right (lb.blocks ++
                                            [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) h))
                                    · exact List.mem_append_left _ (List.mem_append_right
                                        ((lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) ++
                                          [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩]) h)
                                  · exact List.mem_append_right _ h
                                have hH := header_loop_correct budget bId nextB ρ supply c body rest carried sA ρb vc ic s1 lb lr phis
                                  hmk hcond hbody hrest hphis hloop hrestP hstr hlt hfresh hltB fh henv
                                  ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ HFlow.continued envB hrelB0 haccB0 hbrun
                                  res env' (Or.inr rfl) (by intro h; simp at h) (fun _ => hrem)
                                  (by intro u' h; simp at h) prog f (Fmid + 3) hmemLb hsubH hnodf fuelB
                                  (armBlockBound fuelB rest) hFH (Nat.le_refl _)
                                obtain ⟨F', fenvX, hleF, hgeF, hexecH, hrelX, haccX⟩ := hH.1 hres
                                refine ⟨F', fenvX, Nat.le_trans hleF (by omega), hgeF, ?_, hrelX, haccX⟩
                                exact hgoto.trans (hbranchT.trans (hbodyConst.trans hexecH))
                            | stuck =>
                                simp only [] at hrun
                                have hst : res = .stuck := (congrArg Prod.fst hrun).symm
                                rw [hst] at hres
                                exact absurd hres (by simp)
                | _ =>
                    simp only [] at hrun
                    have hst : res = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hres
                    exact absurd hres (by simp)
            | _ =>
                simp only [] at hrun
                have hst : res = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hres
                exact absurd hres (by simp)
      · intro e he
        simp only [runHIRWhile] at hrun
        cases heval : evalHIR 256 henv c with
        | none =>
            rw [heval] at hrun
            have hst : res = .stuck := (congrArg Prod.fst hrun).symm
            rw [hst] at he
            exact absurd he (by simp)
        | some r =>
            rw [heval] at hrun
            cases r with
            | lit w =>
                cases w with
                | bool b =>
                    cases b with
                    | false =>
                        simp only [] at hrun
                        have hpair : (res, env') = ((.value (.lit .unit)), henv) := by
                          rw [hrun]
                        have hst : res = .value (.lit .unit) := congrArg Prod.fst hpair
                        rw [hst] at he
                        exact absurd he (by simp)
                    | true =>
                        simp only [] at hrun
                        cases hbrun : runHIRStmts fh henv body (.value (.lit .unit)) with
                        | mk out envB =>
                            rw [hbrun] at hrun
                            cases out with
                            | value u =>
                                simp only [] at hrun
                                have hrem : runHIRWhile fh envB c body = (res, env') := hrun
                                have hmemH : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemB : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hfindH : findBlock f nextB =
                                    some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemH)
                                have hfindB : findBlock f (nextB + 2) =
                                    some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemB)
                                have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
                                    match a with
                                    | none => none
                                    | some ps =>
                                        match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                                        | some entrySrc, some backSrc =>
                                            some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                                              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                                        | _, _ => none) (some []) = some phis := by
                                  simpa [mkHeaderPhis] using hphis
                                obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
                                  ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                  (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                  carried [] phis hfold
                                have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  cases hgl : lb.blocks.getLast? with
                                  | none =>
                                      simp only [hgl, Option.map_none, Option.getD_none]
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
                                  | some bb =>
                                      have hm : bb ∈ lb.blocks := getLast?_mem hgl
                                      have hb := hbnd bb hm
                                      simp only [hgl, Option.map_some, Option.getD_some]
                                      have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have htrNe : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)), t ≠ bId := by
                                  intro t ht
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  have hmemF : ∃ b ∈ lb.blocks, t = b.id := by
                                    rw [List.mem_filterMap] at ht
                                    obtain ⟨b, hb, hfb⟩ := ht
                                    cases htb : b.terminator with
                                    | goto tt =>
                                        simp only [htb] at hfb
                                        by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                                        · simp only [hC, if_true] at hfb
                                          exact ⟨b, hb, (Option.some.inj hfb).symm⟩
                                        · simp only [hC, if_false] at hfb
                                          exact absurd hfb (by simp)
                                    | _ =>
                                        simp only [htb] at hfb
                                        exact absurd hfb (by simp)
                                  obtain ⟨b, hb, rfl⟩ := hmemF
                                  have hb2 := hbnd b hb
                                  have hle : nextB ≤ b.id := Nat.le_trans (Nat.le_add_right _ _) hb2.1
                                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
                                have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
                                have hleCar : ∀ q ∈ carried, supply ≤ q.2 := fun q hq => mkCarried_mem_lo hmk hq
                                have hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried → r₁ = r₂ → id₁ = id₂ := by
                                  intro a b c d h1 h2 he
                                  subst he
                                  exact mkCarried_reg_inj hmk h1 h2
                                have hphiEq : phis = (carried.map phif).flatten := by rw [hflat]; simp
                                obtain ⟨fenvP, hexP, hrelP, hvalP, hframeP⟩ :=
                                  headerPhis_exec_entry ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                    (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                    carried phif hphif hfallNe htrNe supply hfresh hleCar hdistC prog fenv henv hrel
                                rw [←hphiEq] at hexP
                                have hrelPb : RelEnv henv ρb fenvP.env := by
                                  intro id u hlook
                                  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                                  · subst hid
                                    subst hu
                                    obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hphif (id, u) hmem
                                    obtain ⟨w, hlookH, hreg⟩ := hrel id esrc he1
                                    refine ⟨w, hlookH, ?_⟩
                                    exact hvalP id u w hmem hlookH
                                  · obtain ⟨w, hlookH, hreg⟩ := hrel id u hbase
                                    refine ⟨w, hlookH, ?_⟩
                                    have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
                                    have hnotin : ∀ idx, (idx, u) ∉ carried := by
                                      intro idx hcon
                                      have hle := mkCarried_mem_lo hmk hcon
                                      exact absurd hle (Nat.not_le_of_gt hlt)
                                    rw [hframeP u hnotin]
                                    exact hreg
                                have hfrP : FreshAbove ρb sA := FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
                                obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                                  lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt hfrP henv fenvP hrelPb prog (some bId) _ heval
                                have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                                have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                                subst hwc
                                have hbool : fenvC.boolOf vc = some true := boolOf_of_lit fenvC vc true hregC
                                have hexPhiIc : execInstrsFullFromIn prog (some bId) fenv (phis ++ ic) = some fenvC := by
                                  have happ := execInstrsFullFromIn_append prog (some bId) fenv phis ic
                                  simp only [happ, hexP, hexC]
                                have hrelC : RelEnv henv ρb fenvC.env := by
                                  have hexPure : execInstrsFull fenvP ic = some fenvC := by
                                    have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                      intro d p src hm
                                      exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                                    have h1 : execInstrsFullFromIn prog (some bId) fenvP ic = execInstrsFull fenvP ic := execInstrsFullFromIn_of_noPhi prog (some bId) fenvP ic hnp
                                    rw [h1] at hexC
                                    exact hexC
                                  exact RelEnv_exec henv ρb sA c vc ic s1 hcond fenvP fenvC hrelPb hfrP hexPure
                                have hconstB : execInstrsFullFromIn prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] =
                                    some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                have hfreshB : FreshAbove ρb (s1 + 1) := FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
                                have hrelB0 : RelEnv henv ρb (fenvC.env.update s1 Value.unit) := by
                                  intro id u hlook
                                  obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                                  refine ⟨w, hlookH, ?_⟩
                                  by_cases heq : u = s1
                                  · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                    have hcontra : s1 < sA := heq ▸ hlt
                                    omega
                                  · have hbeq : ¬ (u == s1) := by simpa using heq
                                    simp only [Env.update, hbeq]
                                    exact hreg
                                have haccB0 : (fenvC.env.update s1 Value.unit) s1 = some Value.unit := by simp [Env.update]
                                have hB2 : 2 ≤ 2 + armBlockBound fuelB body := Nat.le_add_right _ _
                                have hfh2 : 2 ≤ fh + 1 + 1 := by omega
                                have hmul : 2 * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.mul_le_mul hB2 hfh2
                                have hF5 : F ≥ 5 := by omega
                                obtain ⟨Fmid, rfl⟩ : ∃ n, F = n + 5 := ⟨F - 5, by omega⟩
                                have hexec0 : execInstrsFullFromIn prog prev fenv ([] : List MIR.Instr) = some fenv := by
                                  simp [execInstrsFullFromIn_eq]
                                have hgoto : execBlockFromIn prog (Fmid + 5) f prev ⟨bId, [], .goto nextB⟩ fenv =
                                    execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv := by
                                  have hF5e : Fmid + 5 = (Fmid + 4) + 1 := by omega
                                  rw [hF5e]
                                  exact execBlockFromIn_goto prog (Fmid + 4) f prev bId [] nextB fenv fenv _ hexec0 hfindH
                                have hbranchT : execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC := by
                                  have hF4 : Fmid + 4 = (Fmid + 3) + 1 := by omega
                                  rw [hF4]
                                  exact execBlockFromIn_branch_true prog (Fmid + 3) f (some bId) nextB (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv fenvC _ hexPhiIc hbool hfindB
                                have happB : execInstrsFullFromIn prog (some nextB) fenvC ([MIR.Instr.const s1 Value.unit] ++ lb.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ lb.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                                  simp only at happ0
                                  rw [hconstB] at happ0
                                  simpa using happ0
                                have hbodyConst : execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, lb.instrs, lb.term⟩ ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  have hF3 : Fmid + 3 = (Fmid + 2) + 1 := by omega
                                  rw [hF3]
                                  exact execBlockFromIn_instrs_prefix prog (Fmid + 2) f (some nextB) (nextB + 2) [MIR.Instr.const s1 Value.unit] lb.instrs lb.term fenvC ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ happB
                                have hexpand : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                    (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) := by
                                  have h1 : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                      (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) * 1 := by
                                    rw [Nat.mul_add]
                                  rw [h1, Nat.mul_one]
                                rw [hexpand] at hF
                                have hFH : Fmid + 3 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + armBlockBound fuelB rest := by omega
                                have hmemLb : ∀ b ∈ lb.blocks, b ∈ f.blocks :=
                                  fun b hb => hsub _ (List.mem_append_left _ (List.mem_append_left _
                                    (List.mem_append_left _ (List.mem_append_left _ hb))))
                                have hsubH : (∀ b ∈ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks,
                                  b ∈ f.blocks) := by
                                  intro b hb
                                  apply hsub
                                  rcases List.mem_append.mp hb with h | h
                                  · rcases List.mem_append.mp h with h | h
                                    · rcases List.mem_append.mp h with h | h
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_left _ (List.mem_append_right lb.blocks h)))
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_right (lb.blocks ++
                                            [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) h))
                                    · exact List.mem_append_left _ (List.mem_append_right
                                        ((lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) ++
                                          [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩]) h)
                                  · exact List.mem_append_right _ h
                                have hH := header_loop_correct budget bId nextB ρ supply c body rest carried sA ρb vc ic s1 lb lr phis
                                  hmk hcond hbody hrest hphis hloop hrestP hstr hlt hfresh hltB fh henv
                                  ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ (HFlow.value u) envB hrelB0 haccB0 hbrun
                                  res env' (Or.inl ⟨u, rfl⟩) (by intro h; simp at h) (by intro h; simp at h)
                                  (fun u' _ => hrem) prog f (Fmid + 3) hmemLb hsubH hnodf fuelB
                                  (armBlockBound fuelB rest) hFH (Nat.le_refl _)
                                obtain ⟨w_e, hlite, hexecRet⟩ := hH.2 e he
                                refine ⟨w_e, hlite, ?_⟩
                                exact hgoto.trans (hbranchT.trans (hbodyConst.trans hexecRet))
                            | returned er =>
                                simp only [] at hrun
                                have hmemH : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemB : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemE : (⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hfindH : findBlock f nextB =
                                    some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemH)
                                have hfindB : findBlock f (nextB + 2) =
                                    some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemB)
                                have hfindE : findBlock f (nextB + 1) =
                                    some ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemE)
                                have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
                                    match a with
                                    | none => none
                                    | some ps =>
                                        match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                                        | some entrySrc, some backSrc =>
                                            some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                                              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                                        | _, _ => none) (some []) = some phis := by
                                  simpa [mkHeaderPhis] using hphis
                                obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
                                  ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                  (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                  carried [] phis hfold
                                have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  cases hgl : lb.blocks.getLast? with
                                  | none =>
                                      simp only [Option.map_none, Option.getD_none]
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
                                  | some bb =>
                                      have hm : bb ∈ lb.blocks := getLast?_mem hgl
                                      have hb := hbnd bb hm
                                      simp only [hgl, Option.map_some, Option.getD_some]
                                      have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have htrNe : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)), t ≠ bId := by
                                  intro t ht
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  have hmemF : ∃ b ∈ lb.blocks, t = b.id := by
                                    rw [List.mem_filterMap] at ht
                                    obtain ⟨b, hb, hfb⟩ := ht
                                    cases htb : b.terminator with
                                    | goto tt =>
                                        simp only [htb] at hfb
                                        by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                                        · simp only [hC, if_true] at hfb
                                          exact ⟨b, hb, (Option.some.inj hfb).symm⟩
                                        · simp only [hC] at hfb
                                          exact absurd hfb (by simp)
                                    | _ =>
                                        simp only [htb] at hfb
                                        exact absurd hfb (by simp)
                                  obtain ⟨b, hb, rfl⟩ := hmemF
                                  have hb2 := hbnd b hb
                                  have hle : nextB ≤ b.id := Nat.le_trans (Nat.le_add_right _ _) hb2.1
                                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
                                have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
                                have hleCar : ∀ q ∈ carried, supply ≤ q.2 := fun q hq => mkCarried_mem_lo hmk hq
                                have hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried → r₁ = r₂ → id₁ = id₂ := by
                                  intro a b c d h1 h2 he
                                  subst he
                                  exact mkCarried_reg_inj hmk h1 h2
                                have hphiEq : phis = (carried.map phif).flatten := by rw [hflat]; simp
                                obtain ⟨fenvP, hexP, hrelP, hvalP, hframeP⟩ :=
                                  headerPhis_exec_entry ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                    (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                    carried phif hphif hfallNe htrNe supply hfresh hleCar hdistC prog fenv henv hrel
                                rw [←hphiEq] at hexP
                                have hrelPb : RelEnv henv ρb fenvP.env := by
                                  intro id u hlook
                                  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                                  · subst hid
                                    subst hu
                                    obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hphif (id, u) hmem
                                    obtain ⟨w, hlookH, hreg⟩ := hrel id esrc he1
                                    refine ⟨w, hlookH, ?_⟩
                                    exact hvalP id u w hmem hlookH
                                  · obtain ⟨w, hlookH, hreg⟩ := hrel id u hbase
                                    refine ⟨w, hlookH, ?_⟩
                                    have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
                                    have hnotin : ∀ idx, (idx, u) ∉ carried := by
                                      intro idx hcon
                                      have hle := mkCarried_mem_lo hmk hcon
                                      exact absurd hle (Nat.not_le_of_gt hlt)
                                    rw [hframeP u hnotin]
                                    exact hreg
                                have hfrP : FreshAbove ρb sA := FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
                                obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                                  lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt hfrP henv fenvP hrelPb prog (some bId) _ heval
                                have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                                have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                                subst hwc
                                have hbool : fenvC.boolOf vc = some true := boolOf_of_lit fenvC vc true hregC
                                have hexPhiIc : execInstrsFullFromIn prog (some bId) fenv (phis ++ ic) = some fenvC := by
                                  have happ := execInstrsFullFromIn_append prog (some bId) fenv phis ic
                                  simp only [happ, hexP, hexC]
                                have hrelC : RelEnv henv ρb fenvC.env := by
                                  have hexPure : execInstrsFull fenvP ic = some fenvC := by
                                    have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                      intro d p src hm
                                      exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                                    have h1 : execInstrsFullFromIn prog (some bId) fenvP ic = execInstrsFull fenvP ic := execInstrsFullFromIn_of_noPhi prog (some bId) fenvP ic hnp
                                    rw [h1] at hexC
                                    exact hexC
                                  exact RelEnv_exec henv ρb sA c vc ic s1 hcond fenvP fenvC hrelPb hfrP hexPure
                                have h1le : 2 ≤ (2 + armBlockBound fuelB body) := by omega
                                have h2le : 2 ≤ (fh + 1 + 1) := by omega
                                have hmul : 2 * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.mul_le_mul h1le h2le
                                have hmul2 : 2 + armBlockBound fuelB body ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
                                have he4 : 4 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := hmul
                                have h5le : 5 ≤ 1 + ((2 + armBlockBound fuelB body) * (fh + 1 + 1) + armBlockBound fuelB rest) := by
                                  have hj : 0 ≤ armBlockBound fuelB rest := Nat.zero_le _
                                  have h1 : 4 + armBlockBound fuelB rest ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) + armBlockBound fuelB rest :=
                                    Nat.add_le_add_right he4 _
                                  omega
                                have hF5 : F ≥ 5 := Nat.le_trans h5le hF
                                obtain ⟨Fmid, rfl⟩ : ∃ n, F = n + 5 := ⟨F - 5, by omega⟩
                                have hmul3 : (2 + armBlockBound fuelB body) * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) :=
                                  Nat.mul_le_mul_left _ h2le
                                have h4B : 4 + armBlockBound fuelB body ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := by
                                  have hexpand : (2 + armBlockBound fuelB body) * 2 = 4 + armBlockBound fuelB body + armBlockBound fuelB body := by
                                    omega
                                  omega
                                have hFbody : Fmid + 3 ≥ blockBound fuelB body + (2 + armBlockBound fuelB rest) := by
                                  simp only [blockBound]
                                  have hFmid : Fmid + 5 ≥ 1 + ((2 + armBlockBound fuelB body) * (fh + 1 + 1) + armBlockBound fuelB rest) := hF
                                  omega
                                have hexcl : CarriedExcl ρb carried := mkCarried_excl hfresh hmk
                                have hsup : ∀ id r, (id, r) ∈ carried → r < s1 + 1 := by
                                  intro id r hmem
                                  have hlt : r < sA := mkCarried_mem_hi hmk hmem
                                  exact Nat.lt_of_lt_of_le hlt (Nat.le_trans hsA (Nat.le_succ _))
                                have hmemLb : ∀ b ∈ lb.blocks, b ∈ (lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++ [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++ [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks) := by
                                  intro b hb
                                  simp [hb]
                                have hsubLb : ∀ b ∈ lb.blocks, b ∈ f.blocks := fun b hb => hsub _ (hmemLb b hb)
                                have hconstB : execInstrsFullFromIn prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] =
                                    some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                have hfreshB : FreshAbove ρb (s1 + 1) := FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
                                have hrelB0 : RelEnv henv ρb (fenvC.env.update s1 Value.unit) := by
                                  intro id u hlook
                                  obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                                  refine ⟨w, hlookH, ?_⟩
                                  by_cases heq : u = s1
                                  · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                    have hcontra : s1 < sA := heq ▸ hlt
                                    omega
                                  · have hbeq : ¬ (u == s1) := by simpa using heq
                                    simp only [Env.update, hbeq]
                                    exact hreg
                                have haccB0 : (fenvC.env.update s1 Value.unit) s1 = some Value.unit := by simp [Env.update]
                                have hexec0 : execInstrsFullFromIn prog prev fenv ([] : List MIR.Instr) = some fenv := by
                                  simp [execInstrsFullFromIn_eq]
                                have hgoto : execBlockFromIn prog (Fmid + 5) f prev ⟨bId, [], .goto nextB⟩ fenv =
                                    execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv := by
                                  have hF5 : Fmid + 5 = (Fmid + 4) + 1 := by omega
                                  rw [hF5]
                                  exact execBlockFromIn_goto prog (Fmid + 4) f prev bId [] nextB fenv fenv _ hexec0 hfindH
                                have hbranchT : execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC := by
                                  have hF4 : Fmid + 4 = (Fmid + 3) + 1 := by omega
                                  rw [hF4]
                                  exact execBlockFromIn_branch_true prog (Fmid + 3) f (some bId) nextB (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv fenvC _ hexPhiIc hbool hfindB
                                have happB : execInstrsFullFromIn prog (some nextB) fenvC ([MIR.Instr.const s1 Value.unit] ++ lb.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ lb.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                                  simp only at happ0
                                  rw [hconstB] at happ0
                                  simpa using happ0
                                have hbodyConst : execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, lb.instrs, lb.term⟩ ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  have hF3 : Fmid + 3 = (Fmid + 2) + 1 := by omega
                                  rw [hF3]
                                  exact execBlockFromIn_instrs_prefix prog (Fmid + 2) f (some nextB) (nextB + 2) [MIR.Instr.const s1 Value.unit] lb.instrs lb.term fenvC ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ happB
                                have hpairR : (res, env') = ((.returned er), envB) := by rw [hrun]
                                have heer : er = e := by
                                  have h1 : res = .returned er := congrArg Prod.fst hpairR
                                  rw [h1] at he
                                  cases he
                                  rfl
                                obtain ⟨w_e, hlite, hexecRet⟩ := (((lowerStmtsCFG_loopBody_run budget (nextB + 2) ρb (s1 + 1) (nextB + 3) nextB s1 (some ⟨nextB, nextB + 1, carried⟩) ⟨nextB, nextB + 1, carried⟩ body lb rfl hbody hloop hfreshB (Nat.lt_succ_self _) 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) Value.unit henv ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ hrelB0 haccB0 fh envB (.returned er) hbrun prog f (some nextB) (Fmid + 3) hsubLb hnodf fuelB (2 + armBlockBound fuelB rest) hFbody hexcl hsup hdistC ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ ⟨nextB + 1, .const lb.supply Value.unit :: lr.instrs, lr.term⟩ ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ hfindH hfindE hfindH).2.2.2) er rfl)
                                refine ⟨w_e, ?_, ?_⟩
                                · rw [←heer]
                                  exact hlite
                                · exact hgoto.trans (hbranchT.trans (hbodyConst.trans hexecRet))
                            | broke =>
                                simp only [] at hrun
                                have hst : res = .value (.lit .unit) := (congrArg Prod.fst hrun).symm
                                rw [hst] at he
                                exact absurd he (by simp)
                            | continued =>
                                simp only [] at hrun
                                have hrem : runHIRWhile fh envB c body = (res, env') := hrun
                                have hmemH : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hmemB : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
                                    lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
                                have hfindH : findBlock f nextB =
                                    some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemH)
                                have hfindB : findBlock f (nextB + 2) =
                                    some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                                  findBlock_of_nodup_mem hnodf (hsub _ hmemB)
                                have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
                                    match a with
                                    | none => none
                                    | some ps =>
                                        match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                                        | some entrySrc, some backSrc =>
                                            some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                                              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                                        | _, _ => none) (some []) = some phis := by
                                  simpa [mkHeaderPhis] using hphis
                                obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
                                  ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                  (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                  carried [] phis hfold
                                have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  cases hgl : lb.blocks.getLast? with
                                  | none =>
                                      simp only [hgl, Option.map_none, Option.getD_none]
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
                                  | some bb =>
                                      have hm : bb ∈ lb.blocks := getLast?_mem hgl
                                      have hb := hbnd bb hm
                                      simp only [hgl, Option.map_some, Option.getD_some]
                                      have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                                      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have htrNe : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)), t ≠ bId := by
                                  intro t ht
                                  have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
                                  have hbnd := hinv.2.2.1
                                  have hmemF : ∃ b ∈ lb.blocks, t = b.id := by
                                    rw [List.mem_filterMap] at ht
                                    obtain ⟨b, hb, hfb⟩ := ht
                                    cases htb : b.terminator with
                                    | goto tt =>
                                        simp only [htb] at hfb
                                        by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                                        · simp only [hC, if_true] at hfb
                                          exact ⟨b, hb, (Option.some.inj hfb).symm⟩
                                        · simp only [hC, if_false] at hfb
                                          exact absurd hfb (by simp)
                                    | _ =>
                                        simp only [htb] at hfb
                                        exact absurd hfb (by simp)
                                  obtain ⟨b, hb, rfl⟩ := hmemF
                                  have hb2 := hbnd b hb
                                  have hle : nextB ≤ b.id := Nat.le_trans (Nat.le_add_right _ _) hb2.1
                                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
                                have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
                                have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
                                have hleCar : ∀ q ∈ carried, supply ≤ q.2 := fun q hq => mkCarried_mem_lo hmk hq
                                have hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried → r₁ = r₂ → id₁ = id₂ := by
                                  intro a b c d h1 h2 he
                                  subst he
                                  exact mkCarried_reg_inj hmk h1 h2
                                have hphiEq : phis = (carried.map phif).flatten := by rw [hflat]; simp
                                obtain ⟨fenvP, hexP, hrelP, hvalP, hframeP⟩ :=
                                  headerPhis_exec_entry ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
                                    (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
                                    carried phif hphif hfallNe htrNe supply hfresh hleCar hdistC prog fenv henv hrel
                                rw [←hphiEq] at hexP
                                have hrelPb : RelEnv henv ρb fenvP.env := by
                                  intro id u hlook
                                  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
                                  · subst hid
                                    subst hu
                                    obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hphif (id, u) hmem
                                    obtain ⟨w, hlookH, hreg⟩ := hrel id esrc he1
                                    refine ⟨w, hlookH, ?_⟩
                                    exact hvalP id u w hmem hlookH
                                  · obtain ⟨w, hlookH, hreg⟩ := hrel id u hbase
                                    refine ⟨w, hlookH, ?_⟩
                                    have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
                                    have hnotin : ∀ idx, (idx, u) ∉ carried := by
                                      intro idx hcon
                                      have hle := mkCarried_mem_lo hmk hcon
                                      exact absurd hle (Nat.not_le_of_gt hlt)
                                    rw [hframeP u hnotin]
                                    exact hreg
                                have hfrP : FreshAbove ρb sA := FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
                                obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                                  lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt hfrP henv fenvP hrelPb prog (some bId) _ heval
                                have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                                have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                                subst hwc
                                have hbool : fenvC.boolOf vc = some true := boolOf_of_lit fenvC vc true hregC
                                have hexPhiIc : execInstrsFullFromIn prog (some bId) fenv (phis ++ ic) = some fenvC := by
                                  have happ := execInstrsFullFromIn_append prog (some bId) fenv phis ic
                                  simp only [happ, hexP, hexC]
                                have hrelC : RelEnv henv ρb fenvC.env := by
                                  have hexPure : execInstrsFull fenvP ic = some fenvC := by
                                    have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                      intro d p src hm
                                      exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                                    have h1 : execInstrsFullFromIn prog (some bId) fenvP ic = execInstrsFull fenvP ic := execInstrsFullFromIn_of_noPhi prog (some bId) fenvP ic hnp
                                    rw [h1] at hexC
                                    exact hexC
                                  exact RelEnv_exec henv ρb sA c vc ic s1 hcond fenvP fenvC hrelPb hfrP hexPure
                                have hconstB : execInstrsFullFromIn prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] =
                                    some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                have hfreshB : FreshAbove ρb (s1 + 1) := FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
                                have hrelB0 : RelEnv henv ρb (fenvC.env.update s1 Value.unit) := by
                                  intro id u hlook
                                  obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                                  refine ⟨w, hlookH, ?_⟩
                                  by_cases heq : u = s1
                                  · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                    have hcontra : s1 < sA := heq ▸ hlt
                                    omega
                                  · have hbeq : ¬ (u == s1) := by simpa using heq
                                    simp only [Env.update, hbeq]
                                    exact hreg
                                have haccB0 : (fenvC.env.update s1 Value.unit) s1 = some Value.unit := by simp [Env.update]
                                have hB2 : 2 ≤ 2 + armBlockBound fuelB body := Nat.le_add_right _ _
                                have hfh2 : 2 ≤ fh + 1 + 1 := by omega
                                have hmul : 2 * 2 ≤ (2 + armBlockBound fuelB body) * (fh + 1 + 1) := Nat.mul_le_mul hB2 hfh2
                                have hF5 : F ≥ 5 := by omega
                                obtain ⟨Fmid, rfl⟩ : ∃ n, F = n + 5 := ⟨F - 5, by omega⟩
                                have hexec0 : execInstrsFullFromIn prog prev fenv ([] : List MIR.Instr) = some fenv := by
                                  simp [execInstrsFullFromIn_eq]
                                have hgoto : execBlockFromIn prog (Fmid + 5) f prev ⟨bId, [], .goto nextB⟩ fenv =
                                    execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv := by
                                  have hF5e : Fmid + 5 = (Fmid + 4) + 1 := by omega
                                  rw [hF5e]
                                  exact execBlockFromIn_goto prog (Fmid + 4) f prev bId [] nextB fenv fenv _ hexec0 hfindH
                                have hbranchT : execBlockFromIn prog (Fmid + 4) f (some bId) ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC := by
                                  have hF4 : Fmid + 4 = (Fmid + 3) + 1 := by omega
                                  rw [hF4]
                                  exact execBlockFromIn_branch_true prog (Fmid + 3) f (some bId) nextB (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv fenvC _ hexPhiIc hbool hfindB
                                have happB : execInstrsFullFromIn prog (some nextB) fenvC ([MIR.Instr.const s1 Value.unit] ++ lb.instrs) =
                                    execInstrsFullFromIn prog (some nextB) ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ lb.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB) fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                                  simp only at happ0
                                  rw [hconstB] at happ0
                                  simpa using happ0
                                have hbodyConst : execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ fenvC =
                                    execBlockFromIn prog (Fmid + 3) f (some nextB) ⟨nextB + 2, lb.instrs, lb.term⟩ ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                                  have hF3 : Fmid + 3 = (Fmid + 2) + 1 := by omega
                                  rw [hF3]
                                  exact execBlockFromIn_instrs_prefix prog (Fmid + 2) f (some nextB) (nextB + 2) [MIR.Instr.const s1 Value.unit] lb.instrs lb.term fenvC ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ happB
                                have hexpand : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                    (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) := by
                                  have h1 : (2 + armBlockBound fuelB body) * (fh + 1 + 1) =
                                      (2 + armBlockBound fuelB body) * (fh + 1) + (2 + armBlockBound fuelB body) * 1 := by
                                    rw [Nat.mul_add]
                                  rw [h1, Nat.mul_one]
                                rw [hexpand] at hF
                                have hFH : Fmid + 3 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + armBlockBound fuelB rest := by omega
                                have hmemLb : ∀ b ∈ lb.blocks, b ∈ f.blocks :=
                                  fun b hb => hsub _ (List.mem_append_left _ (List.mem_append_left _
                                    (List.mem_append_left _ (List.mem_append_left _ hb))))
                                have hsubH : (∀ b ∈ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
                                    [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
                                    [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks,
                                  b ∈ f.blocks) := by
                                  intro b hb
                                  apply hsub
                                  rcases List.mem_append.mp hb with h | h
                                  · rcases List.mem_append.mp h with h | h
                                    · rcases List.mem_append.mp h with h | h
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_left _ (List.mem_append_right lb.blocks h)))
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_right (lb.blocks ++
                                            [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) h))
                                    · exact List.mem_append_left _ (List.mem_append_right
                                        ((lb.blocks ++ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩]) ++
                                          [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩]) h)
                                  · exact List.mem_append_right _ h
                                have hH := header_loop_correct budget bId nextB ρ supply c body rest carried sA ρb vc ic s1 lb lr phis
                                  hmk hcond hbody hrest hphis hloop hrestP hstr hlt hfresh hltB fh henv
                                  ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ HFlow.continued envB hrelB0 haccB0 hbrun
                                  res env' (Or.inr rfl) (by intro h; simp at h) (fun _ => hrem)
                                  (by intro u' h; simp at h) prog f (Fmid + 3) hmemLb hsubH hnodf fuelB
                                  (armBlockBound fuelB rest) hFH (Nat.le_refl _)
                                obtain ⟨w_e, hlite, hexecRet⟩ := hH.2 e he
                                refine ⟨w_e, hlite, ?_⟩
                                exact hgoto.trans (hbranchT.trans (hbodyConst.trans hexecRet))
                            | stuck =>
                                simp only [] at hrun
                                have hst : res = .stuck := (congrArg Prod.fst hrun).symm
                                rw [hst] at he
                                exact absurd he (by simp)
                | _ =>
                    simp only [] at hrun
                    have hst : res = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at he
                    exact absurd he (by simp)
            | _ =>
                simp only [] at hrun
                have hst : res = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at he
                exact absurd he (by simp)


end Morph.HIRToMIRCorrect

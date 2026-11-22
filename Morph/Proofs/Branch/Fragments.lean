/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal

/-!
# Proof crate `Fragments` (L0 leaf): the Stage C statement grammars

Estate-style leaf: depends on `Core`/`Total` only, never on
`Morph.HIRToMIRBranch` or another leaf. `Morph.HIRToMIRBranch` imports this
module back; the tree stays green between cuts.

Provenance (statements unchanged, proofs verbatim): `VarFree`, `ArmStmts`,
`BindArmStmts` (C2c Phase A), `ArmStmts_to_BindArmStmts`, `ArmNoBreak`,
`HFlow_replace_ne_broke`, `ArmNoBreak_run`, the `BranchStep`/`BranchStmts`
mutual block, `LoopStmts`, `straightStmts_to_branch`,
`LoopStmts_to_BranchStmts` — extracted from `Morph/HIRToMIRBranch.lean`
§ "The statement grammars" through § "Stage C does not shrink Stage A".

`ArmStmts` stays binding-free on purpose: `LoopStmts.ifStmtBreak` tails and
every loop-body arm rely on the binding-free gate (an arm `break` skips the
tail while the static exit env still mentions its registers), so the gate
cannot move. `BindArmStmts` is for top-level `if` arms only (Phase B).
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Variable-free expressions: no `.var` anywhere (deep). A loop-body binding
(`var`/`assign`) with a `.var` right-hand side would alias the source register,
which the header phis then overwrite on behalf of the carried id — the HIR
keeps the old value while the MIR reads the new one. Literals and operations
allocate fresh registers, so only `.var` aliases. Statement conditions and
discards only read, so they need no restriction. -/
inductive VarFree : HIR.Expr → Prop where
  | lit (v : Value) : VarFree (.lit v)
  | unop (op : Operator) (e : HIR.Expr) : VarFree e → VarFree (.unop op e)
  | binop (op : Operator) (a b : HIR.Expr) :
      VarFree a → VarFree b → VarFree (.binop op a b)
  | let_ (id : HIR.Id) (init body : HIR.Expr) :
      VarFree init → VarFree body → VarFree (.let id init body)
  | block (es : List HIR.Expr) :
      (∀ e ∈ es, VarFree e) → VarFree (.block es)

/-- Statement lists an `if` arm may contain: no `varDecl`, no `assign` (see the
module note). `return` is allowed and is terminal, like everywhere else.
`break`/`continue` are allowed here so an arm inside a loop body can leave it:
validity is enforced by the lowering (under `loop = none` they refuse, making
those theorem cases vacuous), not by the predicate. -/
inductive ArmStmts (budget : Nat) : List HIR.Stmt → Prop where
  | nil : ArmStmts budget []
  | exprStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → ArmStmts budget rest →
      ArmStmts budget (.exprStmt e :: rest)
  | nop (rest : List HIR.Stmt) : ArmStmts budget rest → ArmStmts budget (.nop :: rest)
  | ifStmt (c : HIR.Expr) (th el : List HIR.Stmt) (rest : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      ArmStmts budget th → ArmStmts budget el → ArmStmts budget rest →
      ArmStmts budget (.ifStmt c th el :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → ArmStmts budget (.returnStmt e :: rest)
  | breakStmt (rest : List HIR.Stmt) :
      ArmStmts budget rest → ArmStmts budget (.break :: rest)
  | continueStmt (rest : List HIR.Stmt) :
      ArmStmts budget rest → ArmStmts budget (.continue :: rest)

/-- Binding arms (C2c Phase A): `ArmStmts` plus `varDecl`/`assign`, for
TOP-LEVEL `if` arms only. `ArmStmts` itself stays binding-free on purpose:
`LoopStmts.ifStmtBreak` tails and every loop-body arm rely on the
binding-free gate (an arm `break` skips the tail while the static exit env
still mentions its registers), so the gate cannot move. Top-level arms are
different: there is no `break`/`continue` outside a loop (the lowering
refuses them when `loop = none`), and a `return`-arm exits the function
without claiming the tail env, while fall-through arms always run the tail
(which then materializes every bound register). The join therefore merges
the two arm-exit envs (`mergeIds`/`mkMergePhis`) and lowers the tail under
the merged env (Phase B: loop-keyed lowering switch plus the top-level C3
rework; this fragment is pure addition until then). Binders mirror
`LoopStmts` (including the `VarFree` RHS side condition the spine-literal
lemmas need). `break`/`continue` constructors are kept so the inclusion
below is total; under `loop = none` the lowering refuses them, making those
cases vacuous. -/
inductive BindArmStmts (budget : Nat) : List HIR.Stmt → Prop where
  | nil : BindArmStmts budget []
  | exprStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → BindArmStmts budget rest →
      BindArmStmts budget (.exprStmt e :: rest)
  | varDecl (id : HIR.Id) (τ : Typ) (init : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight init → SLWeight init < budget → BindArmStmts budget rest →
      VarFree init →
      BindArmStmts budget (.varDecl id τ init :: rest)
  | assign (id : HIR.Id) (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → BindArmStmts budget rest →
      VarFree e →
      BindArmStmts budget (.assign id e :: rest)
  | nop (rest : List HIR.Stmt) : BindArmStmts budget rest →
      BindArmStmts budget (.nop :: rest)
  | ifStmt (c : HIR.Expr) (th el : List HIR.Stmt) (rest : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      BindArmStmts budget th → BindArmStmts budget el → BindArmStmts budget rest →
      BindArmStmts budget (.ifStmt c th el :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → BindArmStmts budget (.returnStmt e :: rest)
  | breakStmt (rest : List HIR.Stmt) :
      BindArmStmts budget rest → BindArmStmts budget (.break :: rest)
  | continueStmt (rest : List HIR.Stmt) :
      BindArmStmts budget rest → BindArmStmts budget (.continue :: rest)

/-- Every binding-free arm is a binding arm: constructor-for-constructor map.
Loop-body call sites keep `ArmStmts` (the gate); only the top-level `if`
will widen to `BindArmStmts` in Phase B. -/
theorem ArmStmts_to_BindArmStmts {budget : Nat} :
    ∀ {ss : List HIR.Stmt}, ArmStmts budget ss → BindArmStmts budget ss
  | _, .nil => .nil
  | _, .exprStmt e rest h1 h2 h3 =>
      .exprStmt e rest h1 h2 (ArmStmts_to_BindArmStmts h3)
  | _, .nop rest h => .nop rest (ArmStmts_to_BindArmStmts h)
  | _, .ifStmt c th el rest h1 h2 hath hael h =>
      .ifStmt c th el rest h1 h2 (ArmStmts_to_BindArmStmts hath)
        (ArmStmts_to_BindArmStmts hael) (ArmStmts_to_BindArmStmts h)
  | _, .returnStmt e rest h1 h2 => .returnStmt e rest h1 h2
  | _, .breakStmt rest h => .breakStmt rest (ArmStmts_to_BindArmStmts h)
  | _, .continueStmt rest h => .continueStmt rest (ArmStmts_to_BindArmStmts h)

/-- Break-free arms: no `.break` anywhere (deep through nested arm `if`s).
`continue` is allowed (it recurses, so the exit env stays reachable) as are
`return` (propagates) and straight-line steps. A loop-body `if` with
break-free arms may bind after it (top-level `break` is terminal in the
lowering, so the exit env is exact); an `if` whose arms may break must have
a binding-free tail (see `LoopStmts.ifStmtBreak`), because an arm `break`
skips the tail while the static exit env still mentions its registers. -/
inductive ArmNoBreak : List HIR.Stmt → Prop where
  | nil : ArmNoBreak []
  | exprStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      ArmNoBreak rest → ArmNoBreak (.exprStmt e :: rest)
  | nop (rest : List HIR.Stmt) : ArmNoBreak rest → ArmNoBreak (.nop :: rest)
  | ifStmt (c : HIR.Expr) (th el : List HIR.Stmt) (rest : List HIR.Stmt) :
      ArmNoBreak th → ArmNoBreak el → ArmNoBreak rest →
      ArmNoBreak (.ifStmt c th el :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) : ArmNoBreak (.returnStmt e :: rest)
  | continueStmt (rest : List HIR.Stmt) :
      ArmNoBreak rest → ArmNoBreak (.continue :: rest)

/-- Break-free arms never produce `.broke`: the only HIR step that yields it
is `.break` itself, which has no `ArmNoBreak` constructor. Arms run from a
value accumulator (every caller passes `.unit`), so the `nil` case cannot
inherit a `.broke` either. The loop-body worker uses this to discharge the
`broke` subcase of a break-free-arm `if`.
Replacing the accumulator never produces `.broke`: a value stays a value
and every other flow is untouched (the `.broke` case itself is absurd). -/
theorem HFlow_replace_ne_broke {acc : HFlow} (u : HIR.Expr) (h : acc ≠ .broke) :
    acc.replace u ≠ .broke := by
  cases acc with
  | value _ => simp [HFlow.replace]
  | broke => exact absurd rfl h
  | returned _ => simp [HFlow.replace]
  | continued => simp [HFlow.replace]
  | stuck => simp [HFlow.replace]

theorem ArmNoBreak_run {ss : List HIR.Stmt} (hnb : ArmNoBreak ss) :
    ∀ (fuelH : Nat) (henv henv' : HEnv) (acc out : HFlow),
      acc ≠ .broke →
      runHIRStmts fuelH henv ss acc = (out, henv') →
      out = .broke → False := by
  induction hnb with
  | nil =>
      intro fuelH henv henv' acc out hacc hrun hbroke
      cases fuelH with
      | zero =>
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hacc' : out = acc := (congrArg Prod.fst hrun).symm
          rw [hacc'] at hbroke
          exact absurd hbroke hacc
  | exprStmt e rest _ ih =>
      intro fuelH henv henv' acc out hacc hrun hbroke
      cases fuelH with
      | zero =>
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv (.exprStmt e :: rest) acc =
              (match evalHIR 256 henv e with
                | none => (HFlow.stuck, henv)
                | some v => runHIRStmts fh henv rest (.value v)) := rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              have hst : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hst] at hbroke
              exact absurd hbroke (by simp)
          | some v =>
              rw [hev] at hrun
              exact ih fh henv henv' _ _ (by simp) hrun hbroke
  | nop rest _ ih =>
      intro fuelH henv henv' acc out hacc hrun hbroke
      cases fuelH with
      | zero =>
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv (.nop :: rest) acc =
              runHIRStmts fh henv rest acc := rfl
          rw [hstep] at hrun
          exact ih fh henv henv' _ _ hacc hrun hbroke
  | ifStmt c th el rest _ _ _ ihth ihel ihrest =>
      intro fuelH henv henv' acc out hacc hrun hbroke
      cases fuelH with
      | zero =>
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv
              (.ifStmt c th el :: rest) acc =
              (match evalHIR 256 henv c with
                | some (.lit (.bool true)) =>
                    match runHIRStmts fh henv th (.value (.lit .unit)) with
                    | (.value u, env') =>
                        runHIRStmts fh env' rest (acc.replace u)
                    | (f, env') => (f, env')
                | some (.lit (.bool false)) =>
                    match runHIRStmts fh henv el (.value (.lit .unit)) with
                    | (.value u, env') =>
                        runHIRStmts fh env' rest (acc.replace u)
                    | (f, env') => (f, env')
                | _ => (HFlow.stuck, henv)) := rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv c with
          | none =>
              rw [hev] at hrun
              have hst : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hst] at hbroke
              exact absurd hbroke (by simp)
          | some r =>
              rw [hev] at hrun
              cases r with
              | lit v =>
                  cases v with
                  | bool b =>
                      cases b with
                      | true =>
                          simp only [] at hrun
                          cases har : runHIRStmts fh henv th
                              (.value (.lit .unit)) with
                          | mk out_arm env_arm =>
                              rw [har] at hrun
                              cases out_arm with
                              | value u =>
                                  simp only [] at hrun
                                  exact ihrest fh env_arm henv' _ _
                                    (HFlow_replace_ne_broke _ hacc)
                                    hrun hbroke
                              | returned e =>
                                  have hr : out = .returned e :=
                                    (congrArg Prod.fst hrun).symm
                                  rw [hr] at hbroke
                                  exact absurd hbroke (by simp)
                              | broke =>
                                  exact ihth fh henv env_arm _ _
                                    (by simp) har rfl
                              | continued =>
                                  have hr : out = .continued :=
                                    (congrArg Prod.fst hrun).symm
                                  rw [hr] at hbroke
                                  exact absurd hbroke (by simp)
                              | stuck =>
                                  have hr : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  rw [hr] at hbroke
                                  exact absurd hbroke (by simp)
                      | false =>
                          simp only [] at hrun
                          cases har : runHIRStmts fh henv el
                              (.value (.lit .unit)) with
                          | mk out_arm env_arm =>
                              rw [har] at hrun
                              cases out_arm with
                              | value u =>
                                  simp only [] at hrun
                                  exact ihrest fh env_arm henv' _ _
                                    (HFlow_replace_ne_broke _ hacc)
                                    hrun hbroke
                              | returned e =>
                                  have hr : out = .returned e :=
                                    (congrArg Prod.fst hrun).symm
                                  rw [hr] at hbroke
                                  exact absurd hbroke (by simp)
                              | broke =>
                                  exact ihel fh henv env_arm _ _
                                    (by simp) har rfl
                              | continued =>
                                  have hr : out = .continued :=
                                    (congrArg Prod.fst hrun).symm
                                  rw [hr] at hbroke
                                  exact absurd hbroke (by simp)
                              | stuck =>
                                  have hr : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  rw [hr] at hbroke
                                  exact absurd hbroke (by simp)
                  | _ =>
                      have hst : out = .stuck :=
                        (congrArg Prod.fst hrun).symm
                      rw [hst] at hbroke
                      exact absurd hbroke (by simp)
              | _ =>
                  have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                  rw [hst] at hbroke
                  exact absurd hbroke (by simp)
  | returnStmt e rest =>
      intro fuelH henv henv' acc out hacc hrun hbroke
      cases fuelH with
      | zero =>
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv (.returnStmt e :: rest) acc =
              (match evalHIR 256 henv e with
                | none => (HFlow.stuck, henv)
                | some v => (.returned v, henv)) := rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              have hst : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hst] at hbroke
              exact absurd hbroke (by simp)
          | some v =>
              rw [hev] at hrun
              have hr : out = .returned v := (congrArg Prod.fst hrun).symm
              rw [hr] at hbroke
              exact absurd hbroke (by simp)
  | continueStmt rest _ _ih =>
      intro fuelH henv henv' acc out hacc hrun hbroke
      cases fuelH with
      | zero =>
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv (.continue :: rest) acc =
              (.continued, henv) := rfl
          rw [hstep] at hrun
          have hr : out = .continued := (congrArg Prod.fst hrun).symm
          rw [hr] at hbroke
          exact absurd hbroke (by simp)

/-! `BranchStep` and `BranchStmts` are mutually recursive: an `if`'s arms are
statement lists. (Doc comments inside a `mutual` block break its layout in this
toolchain, hence the section comment here.) -/
mutual

inductive BranchStep (budget : Nat) : HIR.Stmt → Prop where
  | exprStmt (e : HIR.Expr) :
      IsStraight e → SLWeight e < budget → BranchStep budget (.exprStmt e)
  | varDecl (id : HIR.Id) (τ : Typ) (init : HIR.Expr) :
      IsStraight init → SLWeight init < budget → BranchStep budget (.varDecl id τ init)
  | assign (id : HIR.Id) (e : HIR.Expr) :
      IsStraight e → SLWeight e < budget → BranchStep budget (.assign id e)
  | nop : BranchStep budget .nop
  | ifStmt (c : HIR.Expr) (th el : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      ArmStmts budget th → ArmStmts budget el →
      BranchStep budget (.ifStmt c th el)
  | breakStmt : BranchStep budget .break
  | continueStmt : BranchStep budget .continue
  | whileStmt (c : HIR.Expr) (body : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      LoopStmts budget body →
      BranchStep budget (.whileLoop c body)

inductive BranchStmts (budget : Nat) : List HIR.Stmt → Prop where
  | nil : BranchStmts budget []
  | cons {s : HIR.Stmt} {rest : List HIR.Stmt} :
      BranchStep budget s → BranchStmts budget rest → BranchStmts budget (s :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → BranchStmts budget (.returnStmt e :: rest)

/-- Loop bodies: everything `BranchStmts` allows (bindings included — they
become loop-carried registers) plus `break`/`continue`, but no nested `while`
(the lowering refuses nesting, so there is no constructor for it). Arms of an
`if` inside a body stay `ArmStmts` (arm mode still refuses bindings). -/
inductive LoopStmts (budget : Nat) : List HIR.Stmt → Prop where
  | nil : LoopStmts budget []
  | exprStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → LoopStmts budget rest →
      LoopStmts budget (.exprStmt e :: rest)
  | varDecl (id : HIR.Id) (τ : Typ) (init : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight init → SLWeight init < budget → LoopStmts budget rest →
      VarFree init →
      LoopStmts budget (.varDecl id τ init :: rest)
  | assign (id : HIR.Id) (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → LoopStmts budget rest →
      VarFree e →
      LoopStmts budget (.assign id e :: rest)
  | nop (rest : List HIR.Stmt) : LoopStmts budget rest → LoopStmts budget (.nop :: rest)
  | ifStmt (c : HIR.Expr) (th el : List HIR.Stmt) (rest : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      ArmStmts budget th → ArmStmts budget el → LoopStmts budget rest →
      ArmNoBreak th → ArmNoBreak el →
      LoopStmts budget (.ifStmt c th el :: rest)
  | ifStmtBreak (c : HIR.Expr) (th el : List HIR.Stmt) (rest : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      ArmStmts budget th → ArmStmts budget el →
      LoopStmts budget rest → ArmStmts budget rest →
      LoopStmts budget (.ifStmt c th el :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → LoopStmts budget (.returnStmt e :: rest)
  | breakStmt (rest : List HIR.Stmt) :
      LoopStmts budget rest → LoopStmts budget (.break :: rest)
  | continueStmt (rest : List HIR.Stmt) :
      LoopStmts budget rest → LoopStmts budget (.continue :: rest)

end

/-! ## Stage C does not shrink Stage A -/

/-- Every straight-line program is a Stage C program: the new fragment is a
superset, so C3's theorem covers Stage A's programs rather than replacing them. -/
theorem straightStmts_to_branch {budget : Nat} :
    ∀ {ss : List HIR.Stmt}, StraightStmts budget ss → BranchStmts budget ss
  | _, .nil => .nil
  | _, .exprStmt e rest h1 h2 h3 =>
      .cons (.exprStmt e h1 h2) (straightStmts_to_branch h3)
  | _, .varDecl id τ init rest h1 h2 h3 =>
      .cons (.varDecl id τ init h1 h2) (straightStmts_to_branch h3)
  | _, .assign id e rest h1 h2 h3 =>
      .cons (.assign id e h1 h2) (straightStmts_to_branch h3)
  | _, .returnStmt e rest h1 h2 => .returnStmt e rest h1 h2
  | _, .nop rest h => .cons .nop (straightStmts_to_branch h)/-- Loop bodies embed in the branch fragment: every `LoopStmts` constructor maps
to its `BranchStep`/`BranchStmts` counterpart (`break`/`continue` are
constructors on both sides; there is no `while` to map). Structural recursion:
`LoopStmts` lives in the `mutual` block, which the `induction` tactic does not
support. -/
theorem LoopStmts_to_BranchStmts {budget : Nat} :
    ∀ {ss : List HIR.Stmt}, LoopStmts budget ss → BranchStmts budget ss
  | _, .nil => .nil
  | _, .exprStmt e rest h1 h2 h3 =>
      .cons (.exprStmt e h1 h2) (LoopStmts_to_BranchStmts h3)
  | _, .varDecl id τ init rest h1 h2 h3 _ =>
      .cons (.varDecl id τ init h1 h2) (LoopStmts_to_BranchStmts h3)
  | _, .assign id e rest h1 h2 h3 _ =>
      .cons (.assign id e h1 h2) (LoopStmts_to_BranchStmts h3)
  | _, .nop rest h => .cons .nop (LoopStmts_to_BranchStmts h)
  | _, .ifStmt c th el rest h1 h2 hath hael h _ _ =>
      .cons (.ifStmt c th el h1 h2 hath hael) (LoopStmts_to_BranchStmts h)
  | _, .ifStmtBreak c th el rest h1 h2 hath hael h _ =>
      .cons (.ifStmt c th el h1 h2 hath hael)
        (LoopStmts_to_BranchStmts h)
  | _, .returnStmt e rest h1 h2 => .returnStmt e rest h1 h2
  | _, .breakStmt rest h => .cons .breakStmt (LoopStmts_to_BranchStmts h)
  | _, .continueStmt rest h => .cons .continueStmt (LoopStmts_to_BranchStmts h)

end Morph.HIRToMIRCorrect

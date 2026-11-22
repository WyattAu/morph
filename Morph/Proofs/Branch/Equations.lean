/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRLower
import Morph.Frontend.HIRInterp

/-!
# Proof crate `Equations` (L0 leaf): one rewrite equation per runner constructor

Estate-style leaf: depends on `Morph.HIRToMIRLower` (the definitions) and
`Morph.Frontend.HIRInterp` (the HIR runner) only, never on
`Morph.HIRToMIRBranch` or another leaf. Nothing here unfolds a definition
by name: every proof is `rw`/`simp only` with that definition's own
`eq_def`, so downstream proofs rewrite with THESE lemmas and stay immune to
definition-body edits. (The equation compiler's auto-generated `eq_N`
lemmas shift numbering on every edit, which is why they are not cited
directly; `rfl` does not fire because the match compilation is not
`rfl`-reducible — see the `Fuel` leaf note.)

Two families, mirroring the two runners every lookup/preservation induction
cases on:

- `lowerStmtsCFG_*`: one per `HIR.Stmt` constructor. The flag-gated cases
  (`nil`, `varDecl`, `assign`, `break`, `continue`, `whileLoop`) are stated
  with the gating flag instantiated exactly where the definition branches,
  so each equation is a pure rewrite with no residual case split (except
  `break_some`/`continue_some`, which keep the `carryCopies` match on a
  computed value).
- `runHIRStmts_*`: one per fuel/shape case (`zero`, `nil`, plus one per
  statement constructor at `fuel + 1`), each keeping the `evalHIR` match on
  a computed value.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-! ## `lowerStmtsCFG` equations -/

/-- Nil under `arm = false`: the `(false, _)` pair always takes the
catch-all, so `hasVal` and `loop` stay free. -/
@[simp] theorem lowerStmtsCFG_nil_false (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply nextB : Nat)
    (lastVal : ValId) (hasVal : Bool) (loop : Option LoopInfo) :
    lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop [] =
      some ⟨[], (match cont with | none => .return_ lastVal | some t => .goto t),
        [], lastVal, ρ, supply, nextB⟩ := by
  simp only [lowerStmtsCFG.eq_def]
  rfl

/-- Nil under `arm = true` with no value yet: the arm must still deliver
HIR `unit`, so it materializes `const unit` instead of leaking `lastVal`. -/
@[simp] theorem lowerStmtsCFG_nil_true_false (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply nextB : Nat)
    (lastVal : ValId) (loop : Option LoopInfo) :
    lowerStmtsCFG bId cont true ρ supply nextB lastVal false loop [] =
      some ⟨[.const supply .unit],
        (match cont with | none => .return_ supply | some t => .goto t),
        [], supply, ρ, supply + 1, nextB⟩ := by
  simp only [lowerStmtsCFG.eq_def]
  rfl

/-- Nil under `arm = true` with a value: the pass-through record. -/
@[simp] theorem lowerStmtsCFG_nil_true_true (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply nextB : Nat)
    (lastVal : ValId) (loop : Option LoopInfo) :
    lowerStmtsCFG bId cont true ρ supply nextB lastVal true loop [] =
      some ⟨[], (match cont with | none => .return_ lastVal | some t => .goto t),
        [], lastVal, ρ, supply, nextB⟩ := by
  simp only [lowerStmtsCFG.eq_def]
  rfl

@[simp] theorem lowerStmtsCFG_nop (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (loop : Option LoopInfo) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal loop
        (.nop :: rest) =
      lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal loop rest := by
  simp only [lowerStmtsCFG] <;> rfl

@[simp] theorem lowerStmtsCFG_exprStmt (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (loop : Option LoopInfo) (e : HIR.Expr) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal loop
        (.exprStmt e :: rest) =
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerStmtsCFG bId cont arm ρ s1 nextB v true loop rest with
          | some L => some { L with instrs := ie ++ L.instrs }
          | none => none
      | none => none := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `varDecl` under `loop = some`: refused in both arm modes (the `arm`
flag stays free; the equation holds by casing on it). -/
@[simp] theorem lowerStmtsCFG_varDecl_some (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool) (info : LoopInfo)
    (id : HIR.Id) (τ : Typ) (init : HIR.Expr) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal (some info)
        (.varDecl id τ init :: rest) = none := by
  cases arm <;> simp only [lowerStmtsCFG] <;> rfl

/-- `varDecl` under `loop = none`: binds in both arm modes. -/
@[simp] theorem lowerStmtsCFG_varDecl_none (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (id : HIR.Id) (τ : Typ) (init : HIR.Expr) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal none
        (.varDecl id τ init :: rest) =
      match lowerExpr ρ supply init with
      | some (vb, ib, s1) =>
          match lowerStmtsCFG bId cont arm ((id, vb) :: ρ) s1 nextB lastVal
              true none rest with
          | some L => some { L with instrs := ib ++ L.instrs }
          | none => none
      | none => none := by
  cases arm <;> simp only [lowerStmtsCFG] <;> rfl

/-- `assign` under `arm = true`, `loop = some`: refused (the loop-worker
gate). -/
@[simp] theorem lowerStmtsCFG_assign_true_some (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply nextB : Nat)
    (lastVal : ValId) (hasVal : Bool) (info : LoopInfo) (id : HIR.Id)
    (e : HIR.Expr) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal (some info)
        (.assign id e :: rest) = none := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `assign` under `arm = true`, `loop = none`: top-level arms may rebind
(Phase B). -/
@[simp] theorem lowerStmtsCFG_assign_true_none (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply nextB : Nat)
    (lastVal : ValId) (hasVal : Bool) (id : HIR.Id) (e : HIR.Expr)
    (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal none
        (.assign id e :: rest) =
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerStmtsCFG bId cont true (updAssoc ρ id v) s1 nextB lastVal
              true none rest with
          | some L => some { L with instrs := ie ++ L.instrs }
          | none => none
      | none => none := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `assign` under `arm = false`: no loop check (loop bodies rebind carried
registers), so `loop` stays free. -/
@[simp] theorem lowerStmtsCFG_assign_false (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply nextB : Nat)
    (lastVal : ValId) (hasVal : Bool) (loop : Option LoopInfo) (id : HIR.Id)
    (e : HIR.Expr) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
        (.assign id e :: rest) =
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerStmtsCFG bId cont false (updAssoc ρ id v) s1 nextB lastVal
              true loop rest with
          | some L => some { L with instrs := ie ++ L.instrs }
          | none => none
      | none => none := by
  simp only [lowerStmtsCFG] <;> rfl

@[simp] theorem lowerStmtsCFG_returnStmt (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (loop : Option LoopInfo) (e : HIR.Expr) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal loop
        (.returnStmt e :: rest) =
      match lowerExpr ρ supply e with
      | some (v, ie, s1) => some ⟨ie, .return_ v, [], v, ρ, s1, nextB⟩
      | none => none := by
  simp only [lowerStmtsCFG] <;> rfl

@[simp] theorem lowerStmtsCFG_ifStmt (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (loop : Option LoopInfo) (c : HIR.Expr) (th el rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal loop
        (.ifStmt c th el :: rest) =
      match lowerExpr ρ supply c with
      | none => none
      | some (vc, ic, s1) =>
          match lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3)
              lastVal false loop th with
          | none => none
          | some lt =>
              match lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false loop el with
              | none => none
              | some le =>
                  match mergeIds ρ lt.ρ le.ρ with
                  | [] =>
                      match lowerStmtsCFG (nextB + 2) cont arm ρ (le.supply + 1)
                          le.next le.supply true loop rest with
                      | none => none
                      | some lr =>
                          some { instrs := ic
                                 term := .branch vc nextB (nextB + 1)
                                 blocks := lt.blocks ++ [⟨nextB, lt.instrs, lt.term⟩]
                                           ++ le.blocks ++ [⟨nextB + 1, le.instrs, le.term⟩]
                                           ++ [⟨nextB + 2,
                                               [.phi le.supply ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) lt.val,
                                                .phi le.supply ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1)) le.val] ++ lr.instrs,
                                               lr.term⟩] ++ lr.blocks
                                 val := lr.val
                                 ρ := lr.ρ
                                 supply := lr.supply
                                 next := lr.next + 1 }
                  | mids =>
                      match mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                          ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                          ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                          mids with
                      | none => none
                      | some (mphis, s2, ρm) =>
                          match lowerStmtsCFG (nextB + 2) cont arm ρm s2 le.next
                              le.supply true loop rest with
                          | none => none
                          | some lr =>
                              some { instrs := ic
                                     term := .branch vc nextB (nextB + 1)
                                     blocks := lt.blocks ++ [⟨nextB, lt.instrs, lt.term⟩]
                                               ++ le.blocks ++ [⟨nextB + 1, le.instrs, le.term⟩]
                                               ++ [⟨nextB + 2,
                                                   [.phi le.supply ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) lt.val,
                                                    .phi le.supply ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1)) le.val] ++ mphis ++ lr.instrs,
                                                   lr.term⟩] ++ lr.blocks
                                     val := lr.val
                                     ρ := lr.ρ
                                     supply := lr.supply
                                     next := lr.next + 1 } := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `break` outside a loop: refuses. -/
@[simp] theorem lowerStmtsCFG_break_none (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal none
        (.break :: rest) = none := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `break` inside a loop: snapshots carried registers, jumps to the exit. -/
@[simp] theorem lowerStmtsCFG_break_some (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool) (info : LoopInfo)
    (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal (some info)
        (.break :: rest) =
      match carryCopies ρ info.carried with
      | none => none
      | some copies =>
          some ⟨copies, .goto info.exit, [], lastVal, ρ, supply, nextB⟩ := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `continue` outside a loop: refuses. -/
@[simp] theorem lowerStmtsCFG_continue_none (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal none
        (.continue :: rest) = none := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `continue` inside a loop: snapshots carried registers, jumps to the header. -/
@[simp] theorem lowerStmtsCFG_continue_some (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool) (info : LoopInfo)
    (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal (some info)
        (.continue :: rest) =
      match carryCopies ρ info.carried with
      | none => none
      | some copies =>
          some ⟨copies, .goto info.header, [], lastVal, ρ, supply, nextB⟩ := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `while` under `loop = some`: no nesting. -/
@[simp] theorem lowerStmtsCFG_while_some (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool) (info : LoopInfo)
    (c : HIR.Expr) (body rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal (some info)
        (.whileLoop c body :: rest) = none := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `while` under `loop = none`: entry/header/body/exit allocation. -/
@[simp] theorem lowerStmtsCFG_while_none (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool) (c : HIR.Expr)
    (body rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal none
        (.whileLoop c body :: rest) =
      match mkCarried ρ supply
          ((dedupIds (assignedIds body)).filterMap
            (fun id => (rhoLookup ρ id).map (fun _ => id))) with
      | none => none
      | some (carried, sA, ρb) =>
          match lowerExpr ρb sA c with
          | none => none
          | some (vc, ic, s1) =>
              match lowerStmtsCFG (nextB + 2) (some nextB) false ρb (s1 + 1)
                  (nextB + 3) s1 true
                  (loop := some ⟨nextB, nextB + 1, carried⟩) body with
              | none => none
              | some lb =>
                  match lowerStmtsCFG (nextB + 1) cont arm ρb
                      (lb.supply + 1) lb.next lb.supply true none rest with
                  | none => none
                  | some lr =>
                      match mkHeaderPhis ρ bId carried
                          ((lb.blocks.getLast?.map fun b => b.id).getD
                            (nextB + 2))
                          lb.ρ
                          (backEdgePreds lb nextB) with
                      | none => none
                      | some phis =>
                          some { instrs := []
                                 term := .goto nextB
                                 blocks := lb.blocks ++
                                           [⟨nextB + 2,
                                             .const s1 .unit :: lb.instrs,
                                             lb.term⟩] ++
                                           [⟨nextB,
                                             phis ++ ic,
                                             .branch vc (nextB + 2)
                                               (nextB + 1)⟩] ++
                                           [⟨nextB + 1,
                                             .const lb.supply .unit ::
                                               lr.instrs,
                                             lr.term⟩] ++ lr.blocks
                                 val := lr.val
                                 ρ := lr.ρ
                                 supply := lr.supply
                                 next := lr.next } := by
  simp only [lowerStmtsCFG] <;> rfl

/-- `matchStmt` falls in the catch-all: the lowering has no match support. -/
@[simp] theorem lowerStmtsCFG_matchStmt (bId : MIR.BlockId)
    (cont : Option MIR.BlockId) (arm : Bool) (ρ : List (HIR.Id × ValId))
    (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
    (loop : Option LoopInfo) (scrut : HIR.Expr)
    (arms : List (HIR.Pattern × List HIR.Stmt)) (rest : List HIR.Stmt) :
    lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal loop
        (.matchStmt scrut arms :: rest) = none := by
  simp only [lowerStmtsCFG] <;> rfl

/-! ## `runHIRStmts` equations -/

/-- Zero fuel: stuck without touching the environment. -/
@[simp] theorem runHIRStmts_zero (env : HEnv) (ss : List HIR.Stmt)
    (acc : HFlow) :
    runHIRStmts 0 env ss acc = ((.stuck, env) : HRan) := by
  simp only [runHIRStmts] <;> rfl

/-- Successor fuel on the empty list: the accumulator is the outcome. -/
@[simp] theorem runHIRStmts_nil (fuel : Nat) (env : HEnv) (acc : HFlow) :
    runHIRStmts (fuel + 1) env [] acc = (acc, env) := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_nop (fuel : Nat) (env : HEnv)
    (rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.nop :: rest) acc =
      runHIRStmts fuel env rest acc := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_exprStmt (fuel : Nat) (env : HEnv)
    (e : HIR.Expr) (rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.exprStmt e :: rest) acc =
      match evalHIR 256 env e with
      | none => ((.stuck, env) : HRan)
      | some v => runHIRStmts fuel env rest (.value v) := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_varDecl (fuel : Nat) (env : HEnv)
    (id : HIR.Id) (τ : Typ) (init : HIR.Expr) (rest : List HIR.Stmt)
    (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.varDecl id τ init :: rest) acc =
      match evalHIR 256 env init with
      | none => ((.stuck, env) : HRan)
      | some v => runHIRStmts fuel ((id, v) :: env) rest acc := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_assign (fuel : Nat) (env : HEnv)
    (id : HIR.Id) (e : HIR.Expr) (rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.assign id e :: rest) acc =
      match evalHIR 256 env e with
      | none => ((.stuck, env) : HRan)
      | some v => runHIRStmts fuel (updateHEnv env id v) rest acc := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_return (fuel : Nat) (env : HEnv)
    (e : HIR.Expr) (rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.returnStmt e :: rest) acc =
      match evalHIR 256 env e with
      | none => ((.stuck, env) : HRan)
      | some v => ((.returned v, env) : HRan) := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_break (fuel : Nat) (env : HEnv)
    (rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.break :: rest) acc =
      ((.broke, env) : HRan) := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_continue (fuel : Nat) (env : HEnv)
    (rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.continue :: rest) acc =
      ((.continued, env) : HRan) := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_while (fuel : Nat) (env : HEnv)
    (cond : HIR.Expr) (body rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.whileLoop cond body :: rest) acc =
      match runHIRWhile fuel env cond body with
      | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
      | (f, env') => ((f, env') : HRan) := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_if (fuel : Nat) (env : HEnv)
    (cond : HIR.Expr) (th el rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.ifStmt cond th el :: rest) acc =
      match evalHIR 256 env cond with
      | some (.lit (.bool true)) =>
        match runHIRStmts fuel env th (.value (.lit .unit)) with
        | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
        | (f, env') => ((f, env') : HRan)
      | some (.lit (.bool false)) =>
        match runHIRStmts fuel env el (.value (.lit .unit)) with
        | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
        | (f, env') => ((f, env') : HRan)
      | _ => ((.stuck, env) : HRan) := by
  simp only [runHIRStmts] <;> rfl

@[simp] theorem runHIRStmts_match (fuel : Nat) (env : HEnv)
    (scrut : HIR.Expr) (arms : List (HIR.Pattern × List HIR.Stmt))
    (rest : List HIR.Stmt) (acc : HFlow) :
    runHIRStmts (fuel + 1) env (.matchStmt scrut arms :: rest) acc =
      match evalHIR 256 env scrut with
      | none => ((.stuck, env) : HRan)
      | some v =>
        match runHIRMatchArms fuel env v arms with
        | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
        | (f, env') => ((f, env') : HRan) := by
  simp only [runHIRStmts] <;> rfl

end Morph.HIRToMIRCorrect

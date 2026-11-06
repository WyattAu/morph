/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore

namespace Morph.HIRToMIRCorrect

open Morph.HIRToMIR Morph.MIR Morph.Frontend.HIREval Morph.Frontend.HIRInterp
open Morph.Core

/-! ## Totality: the lowered code never stalls

`lower_correct` consumes MIR success, so on its own it says nothing about
whether the emitted code gets stuck. This section proves the other direction
for the straight-line fragment: if the source evaluates, the emitted
instructions run to a final environment.

The HIR hypothesis is stated with an arbitrary result `r` rather than a
literal, because the fragment can still *read* a variable (the lowering emits
no instructions for a read, so there is nothing to stall on). The conclusion
degrades gracefully: the code runs, and when the source value is a literal the
result register holds it. In this fragment that is always the case, which the
second conjunct records.
-/

/-- A successful singleton run, from a successful step. -/
theorem execInstrsFull_singleton (fenv fenv1 : FullEnv) (i : Instr)
    (h : evalInstrFull fenv i = some fenv1) :
    execInstrsFull fenv [i] = some fenv1 := by
  rw [execInstrsFull_cons, h]
  simp [execInstrsFull]

/-- `getLast!` and `getLastD` agree away from the empty list. -/
theorem getLast!_eq_getLastD : ∀ (vs : List HIR.Expr), vs ≠ [] →
    vs.getLast! = vs.getLastD (HIR.Expr.lit Value.unit)
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: w :: rest, _ => getLast!_eq_getLastD (w :: rest) (by simp)

/-- `mapM` on a cons list: the head result and the tail run. -/
theorem mapM_cons_inv {α β : Type} (f : α → Option β) (a : α) (as : List α)
    (ys : List β) (h : List.mapM f (a :: as) = some ys) :
    ∃ (y : β) (ys' : List β), ys = y :: ys' ∧ f a = some y ∧
      List.mapM f as = some ys' := by
  have hlen := mapM_length f (a :: as) ys h
  cases ys with
  | nil => simp at hlen
  | cons y ys' =>
      obtain ⟨h1, h2⟩ := (mapM_cons_eq f a as y ys').mp h
      exact ⟨y, ys', rfl, h1, h2⟩

/-- Successful `unop` evaluation, decomposed. -/
theorem evalHIR_unop_inv (n : Nat) (henv : HEnv) (op : Operator) (e : HIR.Expr)
    (r : HIR.Expr) (h : evalHIR (n + 1) henv (.unop op e) = some r) :
    ∃ (u w : Value), evalHIR n henv e = some (.lit u) ∧
      Morph.Executable.evalUnop op (.lit u) = some (.lit w) ∧ r = .lit w := by
  simp only [evalHIR] at h
  obtain ⟨a, ha, hb⟩ := bind_some_eq h
  cases a with
  | lit u =>
      simp only [] at hb
      cases hc : Morph.Executable.evalUnop op (.lit u) with
      | none => rw [hc] at hb; simp at hb
      | some e' =>
          rw [hc] at hb
          obtain ⟨w, hw⟩ := evalUnop_is_lit hc
          subst hw
          exact ⟨u, w, ha, hc, (Option.some.inj (by simpa using hb)).symm⟩
  | var _ => simp at hb
  | unop _ _ => simp at hb
  | binop _ _ _ => simp at hb
  | «let» _ _ _ => simp at hb
  | block _ => simp at hb
  | app _ _ => simp at hb
  | lam _ _ => simp at hb
  | ifThenElse _ _ _ => simp at hb
  | whileLoop _ _ => simp at hb
  | «match» _ _ => simp at hb
  | infer => simp at hb

/-- Successful `binop` evaluation, decomposed. -/
theorem evalHIR_binop_inv (n : Nat) (henv : HEnv) (op : Operator)
    (a b : HIR.Expr) (r : HIR.Expr)
    (h : evalHIR (n + 1) henv (.binop op a b) = some r) :
    ∃ (va vb w : Value), evalHIR n henv a = some (.lit va) ∧
      evalHIR n henv b = some (.lit vb) ∧
      Morph.Executable.evalBinop op (.lit va) (.lit vb) = some (.lit w) ∧
      r = .lit w := by
  simp only [evalHIR] at h
  obtain ⟨x, hx, h1⟩ := bind_some_eq h
  obtain ⟨y, hy, h2⟩ := bind_some_eq h1
  cases x with
  | lit va =>
      cases y with
      | lit vb =>
          simp only [] at h2
          cases hc : Morph.Executable.evalBinop op (.lit va) (.lit vb) with
          | none => rw [hc] at h2; simp at h2
          | some e' =>
              rw [hc] at h2
              obtain ⟨w, hw⟩ := evalBinop_is_lit hc
              subst hw
              exact ⟨va, vb, w, hx, hy, hc, (Option.some.inj (by simpa using h2)).symm⟩
      | var _ => simp at h2
      | unop _ _ => simp at h2
      | binop _ _ _ => simp at h2
      | «let» _ _ _ => simp at h2
      | block _ => simp at h2
      | app _ _ => simp at h2
      | lam _ _ => simp at h2
      | ifThenElse _ _ _ => simp at h2
      | whileLoop _ _ => simp at h2
      | «match» _ _ => simp at h2
      | infer => simp at h2
  | var _ => simp at h2
  | unop _ _ => simp at h2
  | binop _ _ _ => simp at h2
  | «let» _ _ _ => simp at h2
  | block _ => simp at h2
  | app _ _ => simp at h2
  | lam _ _ => simp at h2
  | ifThenElse _ _ _ => simp at h2
  | whileLoop _ _ => simp at h2
  | «match» _ _ => simp at h2
  | infer => simp at h2

/-- Successful `let` evaluation, decomposed. -/
theorem evalHIR_let_inv (n : Nat) (henv : HEnv) (id : HIR.Id)
    (init body : HIR.Expr) (r : HIR.Expr)
    (h : evalHIR (n + 1) henv (.let id init body) = some r) :
    ∃ v0, evalHIR n henv init = some v0 ∧
      evalHIR n ((id, v0) :: henv) body = some r := by
  simp only [evalHIR] at h
  obtain ⟨v0, hv0, hbody⟩ := bind_some_eq h
  exact ⟨v0, hv0, hbody⟩

/-- Successful `block` evaluation, decomposed. -/
theorem evalHIR_block_inv (n : Nat) (henv : HEnv) (es : List HIR.Expr)
    (r : HIR.Expr) (h : evalHIR (n + 1) henv (.block es) = some r) :
    ∃ vs, es.mapM (evalHIR n henv) = some vs ∧
      ((vs = [] ∧ r = .lit Value.unit) ∨ (vs ≠ [] ∧ r = vs.getLast!)) := by
  simp only [evalHIR] at h
  obtain ⟨vs, hvs, hres⟩ := bind_some_eq h
  refine ⟨vs, hvs, ?_⟩
  cases vs with
  | nil =>
      left
      refine ⟨rfl, ?_⟩
      simp only [] at hres
      exact (Option.some.inj hres).symm
  | cons w rest =>
      right
      refine ⟨by simp, ?_⟩
      simp only [] at hres
      exact (Option.some.inj hres).symm
/-- Totality of the lowered code on the straight-line fragment: whenever the
source evaluates (at any fuel), the emitted instructions run to a final
environment, the store is untouched, and — when the source value is a literal,
which it always is in this fragment — the result register holds it.

Together with `lower_correct` this closes the D-2/D-4 gap *inside* the
fragment: the emitted code neither stalls nor diverges from the source on the
inputs where the source is defined. -/
theorem lower_total :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → IsStraight e →
      FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fuel : Nat) (r : HIR.Expr), evalHIR fuel henv e = some r →
      (∃ w, r = HIR.Expr.lit w) ∧
        ∃ fenv', execInstrsFull fenv is = some fenv' ∧ fenv'.store = fenv.store ∧
          ∃ w, r = HIR.Expr.lit w ∧ fenv'.env v = some w) ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') →
      (∀ x ∈ es, IsStraight x) → FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fuel : Nat) (vs : List HIR.Expr), es.mapM (evalHIR fuel henv) = some vs →
      (∃ w, vs.getLastD (HIR.Expr.lit Value.unit) = HIR.Expr.lit w) ∧
        ∃ fenv', execInstrsFull fenv is = some fenv' ∧ fenv'.store = fenv.store ∧
          ∃ w, vs.getLastD (HIR.Expr.lit Value.unit) = HIR.Expr.lit w ∧
            fenv'.env v = some w) := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → IsStraight e →
      FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fuel : Nat) (r : HIR.Expr), evalHIR fuel henv e = some r →
      (∃ w, r = HIR.Expr.lit w) ∧
        ∃ fenv', execInstrsFull fenv is = some fenv' ∧ fenv'.store = fenv.store ∧
          ∃ w, r = HIR.Expr.lit w ∧ fenv'.env v = some w)
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') →
      (∀ x ∈ es, IsStraight x) → FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fuel : Nat) (vs : List HIR.Expr), es.mapM (evalHIR fuel henv) = some vs →
      (∃ w, vs.getLastD (HIR.Expr.lit Value.unit) = HIR.Expr.lit w) ∧
        ∃ fenv', execInstrsFull fenv is = some fenv' ∧ fenv'.store = fenv.store ∧
          ∃ w, vs.getLastD (HIR.Expr.lit Value.unit) = HIR.Expr.lit w ∧
            fenv'.env v = some w)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- lit
    intro ρ supply v v' is' s' h _hs _hf henv fenv _hrel fuel r heval
    simp only [lowerExpr] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases fuel with
    | zero => simp [evalHIR] at heval
    | succ n =>
        simp only [evalHIR] at heval
        have hr : r = HIR.Expr.lit v := (Option.some.inj heval).symm
        refine ⟨⟨v, hr⟩, ?_⟩
        refine ⟨⟨(fenv.env).update supply v, fenv.store⟩, ?_, rfl, ⟨v, hr, ?_⟩⟩
        · exact execInstrsFull_singleton fenv _ _ (by simp [evalInstrFull])
        · simp [Env.update]
  · -- var
    intro ρ supply id v' is' s' h _hs _hf henv fenv hrel fuel r heval
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some u =>
        simp only [hr] at h
        have hpair := Option.some.inj h
        have hvu : v' = u :=
          (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
        have his : is' = [] :=
          (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
        cases fuel with
        | zero => simp [evalHIR] at heval
        | succ n =>
            simp only [evalHIR] at heval
            obtain ⟨w, hlookH, hreg⟩ := hrel id u hr
            have hrw : r = HIR.Expr.lit w := Option.some.inj (heval.symm.trans hlookH)
            refine ⟨⟨w, hrw⟩, ?_⟩
            rw [his, hvu]
            exact ⟨fenv, by rw [execInstrsFull_nil], rfl, w, hrw, hreg⟩
  · -- unop, success
    intro ρ supply op e u v is s h1 h2 ih v' is' s' h hs hf henv fenv hrel fuel r heval
    simp only [lowerExpr, h1, h2] at h
    have hpair := Option.some.inj h
    have his : is' = is ++ [.unop s u v (unopTyp u)] :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvs : v' = s :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    cases fuel with
    | zero => simp [evalHIR] at heval
    | succ n =>
        obtain ⟨u0, w0, hevalE, hHIR, hrw⟩ := evalHIR_unop_inv n henv op e r heval
        obtain ⟨_, fenv1, hexec1, hstore1, w1, hw1, hreg1⟩ :=
          ih v is s h1 (IsStraight_unop_sub hs) hf henv fenv hrel n (.lit u0) hevalE
        have hu0 : u0 = w1 := by simpa using hw1
        rw [hu0] at hHIR
        have hMir : MIR.evalUnOp u w1 = some w0 := (evalUnop_glue op u w1 w0 h2).mpr hHIR
        have hstep : evalInstrFull fenv1 (.unop s u v (unopTyp u))
            = some ⟨(fenv1.env).update s w0, fenv1.store⟩ := by
          rw [evalInstrFull_unop_step, hreg1]
          simp [hMir]
        have happ : execInstrsFull fenv (is ++ [.unop s u v (unopTyp u)])
            = some ⟨(fenv1.env).update s w0, fenv1.store⟩ := by
          rw [execInstrsFull_append, hexec1]
          exact execInstrsFull_singleton fenv1 _ _ hstep
        refine ⟨⟨w0, hrw⟩, ?_⟩
        rw [his, hvs]
        exact ⟨⟨(fenv1.env).update s w0, fenv1.store⟩, happ, hstore1,
          w0, hrw, by simp [Env.update]⟩
  · -- unop, fail
    intro ρ supply op e hfail ih v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · -- binop, success
    intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 ihA ihB v' is' s' h hs hf henv fenv hrel fuel r heval
    simp only [lowerExpr, h1, h2, h3] at h
    have hpair := Option.some.inj h
    have his : is' = ia ++ ib ++ [.binop s2 bo va vb (binopTyp bo)] :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvs : v' = s2 :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    cases fuel with
    | zero => simp [evalHIR] at heval
    | succ n =>
        obtain ⟨ua, ub, w0, hevalA, hevalB, hHIR, hrw⟩ :=
          evalHIR_binop_inv n henv op a b r heval
        have hsa : IsStraight a := IsStraight_binop_sub_l hs
        have hsb : IsStraight b := IsStraight_binop_sub_r hs
        obtain ⟨_, fenv1, hexecA, hstoreA, wa, hwa, hregA⟩ :=
          ihA va ia s1 h1 hsa hf henv fenv hrel n (.lit ua) hevalA
        have hf' : FreshAbove ρ s1 :=
          FreshAbove.mono ρ supply s1 (lower_mono.1 _ _ _ _ _ _ h1) hf
        have hrel1 : RelEnv henv ρ fenv1.env :=
          RelEnv_exec henv ρ supply a va ia s1 h1 fenv fenv1 hrel hf hexecA
        obtain ⟨_, fenv2, hexecB, hstoreB, wb, hwb, hregB⟩ :=
          ihB vb ib s2 h3 hsb hf' henv fenv1 hrel1 n (.lit ub) hevalB
        have hua : ua = wa := by simpa using hwa
        have hub : ub = wb := by simpa using hwb
        rw [hua, hub] at hHIR
        have hva_lt : va < s1 := lower_result_lt.1 ρ supply a va ia s1 h1 hf
        have hregA' : fenv2.env va = some wa := by
          have heq := lower_preserv_regs ρ s1 b vb ib s2 h3 fenv1 fenv2 hexecB va hva_lt
          rw [heq]
          exact hregA
        have hMir : MIR.evalBinOp bo wa wb = some w0 :=
          (evalBinop_glue op bo wa wb w0 h2).mpr hHIR
        have hstep : evalInstrFull fenv2 (.binop s2 bo va vb (binopTyp bo))
            = some ⟨(fenv2.env).update s2 w0, fenv2.store⟩ := by
          rw [evalInstrFull_binop_step, hregA', hregB]
          simp [hMir]
        have happ1 : execInstrsFull fenv (ia ++ ib) = some fenv2 := by
          rw [execInstrsFull_append, hexecA]
          exact hexecB
        have happ : execInstrsFull fenv (ia ++ ib ++ [.binop s2 bo va vb (binopTyp bo)])
            = some ⟨(fenv2.env).update s2 w0, fenv2.store⟩ := by
          rw [execInstrsFull_append, happ1]
          exact execInstrsFull_singleton fenv2 _ _ hstep
        refine ⟨⟨w0, hrw⟩, ?_⟩
        rw [his, hvs]
        exact ⟨⟨(fenv2.env).update s2 w0, fenv2.store⟩, happ, hstoreB.trans hstoreA,
          w0, hrw, by simp [Env.update]⟩
  · -- binop, body fail
    intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · -- binop, operator fail
    intro ρ supply op a b hfail ihA v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some b =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail b p.1 p.2.1 p.2.2 hto ha)
  · -- let, success
    intro ρ supply id init body va ia s1 h1 vb ib s2 h2 ihI ihB v' is' s' h hs hf henv fenv hrel fuel r heval
    simp only [lowerExpr, h1, h2] at h
    have hpair := Option.some.inj h
    have his : is' = ia ++ ib :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvv : v' = vb :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    cases fuel with
    | zero => simp [evalHIR] at heval
    | succ n =>
        obtain ⟨v0, hevalI, hevalB⟩ := evalHIR_let_inv n henv id init body r heval
        have hsi : IsStraight init := IsStraight_let_init hs
        have hsb : IsStraight body := IsStraight_let_body hs
        obtain ⟨_, fenv1, hexec1, hstore1, w, hw, hreg1⟩ :=
          ihI va ia s1 h1 hsi hf henv fenv hrel n v0 hevalI
        rw [hw] at hevalB
        have hva : va < s1 := lower_result_lt.1 ρ supply init va ia s1 h1 hf
        have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
        have hf' : FreshAbove ((id, va) :: ρ) s1 := by
          intro j u hmem
          rcases List.mem_cons.mp hmem with heq | hmem
          · cases heq
            exact hva
          · exact Nat.lt_of_lt_of_le (hf j u hmem) hle1
        have hrel' : RelEnv ((id, HIR.Expr.lit w) :: henv) ((id, va) :: ρ) fenv1.env := by
          intro j u hlook
          by_cases hid : id = j
          · subst hid
            have hu : u = va := by
              have hh : rhoLookup ((id, va) :: ρ) id = some va :=
                rhoLookup_cons_head id va ρ
              rw [hh] at hlook
              exact (Option.some.inj hlook).symm
            subst hu
            exact ⟨w, by simp [lookupHEnv], hreg1⟩
          · have hlook' : rhoLookup ρ j = some u := by
              rw [rhoLookup_cons_ne hid] at hlook
              exact hlook
            obtain ⟨w', hlookH, hreg⟩ := hrel j u hlook'
            have hu_lt : u < supply := hf j u (rhoLookup_some_mem ρ j u hlook')
            have heq := lower_preserv_regs ρ supply init va ia s1 h1 fenv fenv1 hexec1 u hu_lt
            exact ⟨w', by rw [lookupHEnv_cons_ne hid]; exact hlookH,
              by rw [heq]; exact hreg⟩
        obtain ⟨hval, fenv2, hexec2, hstore2, w2, hw2, hreg2⟩ :=
          ihB vb ib s2 h2 hsb hf' ((id, .lit w) :: henv) fenv1 hrel' n r hevalB
        refine ⟨hval, ?_⟩
        rw [his, hvv]
        exact ⟨fenv2, by rw [execInstrsFull_append, hexec1]; exact hexec2,
          hstore2.trans hstore1, w2, hw2, hreg2⟩
  · -- let, body fail
    intro ρ supply id init body va ia s1 h1 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · -- let, init fail
    intro ρ supply id init body hfail ihI v' is' s' h
    simp only [lowerExpr, hfail] at h
    simp at h
  · -- block delegate
    intro ρ supply es ih v' is' s' h hs hf henv fenv hrel fuel r heval
    simp only [lowerExpr] at h
    have hs' : ∀ x ∈ es, IsStraight x := by
      cases hs with
      | block _ hall => exact hall
    cases fuel with
    | zero => simp [evalHIR] at heval
    | succ n =>
        obtain ⟨vs, hmap, hcase⟩ := evalHIR_block_inv n henv es r heval
        obtain ⟨_, fenv', hexec', hstore', w, hw, hreg⟩ :=
          ih v' is' s' h hs' hf henv fenv hrel n vs hmap
        rcases hcase with ⟨hvs, hr⟩ | ⟨hvsne, hr⟩
        · rw [hvs] at hw
          have hwunit : w = Value.unit := by simpa using hw.symm
          subst hwunit
          exact ⟨⟨Value.unit, hr⟩,
            ⟨fenv', hexec', hstore', Value.unit, hr, hreg⟩⟩
        · have hlast : r = HIR.Expr.lit w := hr.trans ((getLast!_eq_getLastD vs hvsne).trans hw)
          exact ⟨⟨w, hlast⟩, ⟨fenv', hexec', hstore', w, hlast, hreg⟩⟩
  · -- non-lowering constructors
    intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h
    cases t with
    | lit v => exact False.elim (d1 v rfl)
    | var id => exact False.elim (d2 id rfl)
    | unop op e => exact False.elim (d3 op e rfl)
    | binop op a b => exact False.elim (d4 op a b rfl)
    | «let» id a b => exact False.elim (d5 id a b rfl)
    | block es => exact False.elim (d6 es rfl)
    | app f args => simp [lowerExpr] at h
    | lam p b => simp [lowerExpr] at h
    | ifThenElse c t f => simp [lowerExpr] at h
    | whileLoop c b => simp [lowerExpr] at h
    | «match» s a => simp [lowerExpr] at h
    | infer => simp [lowerExpr] at h
  · -- block, empty
    intro ρ supply v' is' s' h _hs _hf henv fenv _hrel fuel vs hmap
    simp only [lowerBlock] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hvs : vs = [] := by
      have hlen := mapM_length (evalHIR fuel henv) ([] : List HIR.Expr) vs hmap
      cases vs with
      | nil => rfl
      | cons y ys => simp at hlen
    rw [hvs]
    refine ⟨⟨Value.unit, rfl⟩, ?_⟩
    refine ⟨⟨(fenv.env).update supply Value.unit, fenv.store⟩, ?_, rfl,
      Value.unit, rfl, ?_⟩
    · exact execInstrsFull_singleton fenv _ _ (by simp [evalInstrFull])
    · simp [Env.update]
  · -- block, singleton
    intro ρ supply e ih v' is' s' h hs hf henv fenv hrel fuel vs hmap
    simp only [lowerBlock] at h
    obtain ⟨y, ys, hvs, hfe, htail⟩ :=
      mapM_cons_inv (evalHIR fuel henv) e [] vs hmap
    have hys : ys = [] := by
      have hlen := mapM_length (evalHIR fuel henv) ([] : List HIR.Expr) ys htail
      cases ys with
      | nil => rfl
      | cons z zs => simp at hlen
    subst hys
    obtain ⟨⟨w1, hw1⟩, fenv, hexec, hstore, w2, hw2, hreg⟩ :=
      ih v' is' s' h (hs e (by simp)) hf henv fenv hrel fuel y hfe
    rw [hvs]
    exact ⟨⟨w1, by simpa using hw1⟩, fenv, hexec, hstore, w2, by simpa using hw2, hreg⟩
  · -- block, cons
    intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' h hs hf henv fenv hrel fuel vs hmap
    simp only [lowerBlock, h1, h2] at h
    have hpair := Option.some.inj h
    have his : is' = ib ++ ib' :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvv : v' = vb' :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    obtain ⟨y, ys, hvs, hfe, htail⟩ :=
      mapM_cons_inv (evalHIR fuel henv) e es vs hmap
    obtain ⟨_, fenv1, hexec1, hstore1, _, _, _⟩ :=
      ihE vb ib s2 h1 (hs e (by simp)) hf henv fenv hrel fuel y hfe
    have hf' : FreshAbove ρ s2 :=
      FreshAbove.mono ρ supply s2 (lower_mono.1 _ _ _ _ _ _ h1) hf
    have hrel1 : RelEnv henv ρ fenv1.env :=
      RelEnv_exec henv ρ supply e vb ib s2 h1 fenv fenv1 hrel hf hexec1
    obtain ⟨_, fenv2, hexec2, hstore2, wT, hwT, hregT⟩ :=
      ihEs vb' ib' s2' h2 (fun x hx => hs x (List.mem_cons_of_mem e hx)) hf'
        henv fenv1 hrel1 fuel ys htail
    have hysne : ys ≠ [] := by
      rintro rfl
      have hlen := mapM_length (evalHIR fuel henv) es ([] : List HIR.Expr) htail
      exact hne (by cases es with | nil => rfl | cons _ _ => simp at hlen)
    have hlast : (y :: ys).getLastD (HIR.Expr.lit Value.unit)
        = ys.getLastD (HIR.Expr.lit Value.unit) := by
      cases ys with
      | nil => exact absurd rfl hysne
      | cons _ _ => rfl
    rw [hvv, his, hvs]
    refine ⟨⟨wT, by rw [hlast]; exact hwT⟩, ?_⟩
    exact ⟨fenv2, by rw [execInstrsFull_append, hexec1]; exact hexec2,
      hstore2.trans hstore1, wT, by rw [hlast]; exact hwT, hregT⟩
  · -- block, tail fail
    intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · -- block, head fail
    intro ρ supply e es hne hfail ihE v' is' s' h
    simp only [lowerBlock, hfail] at h
    simp at h

/-- `lower_total` with the source value pinned: when the source evaluates to
the literal `w`, the emitted code runs to an environment holding `w` in the
result register and leaves the store untouched. A derived corollary — the
statement layer ends up using the existential form, because an intermediate
`exprStmt` in a fragment sequence may evaluate to a non-literal that a later
statement overwrites via the runner's accumulator. -/
theorem lower_total_lit (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
    (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerExpr ρ supply e = some (v, is, s')) (hs : IsStraight e)
    (hf : FreshAbove ρ supply) (henv : HEnv) (fenv : FullEnv)
    (hrel : RelEnv henv ρ fenv.env) (fuel : Nat) (w : Value)
    (heval : evalHIR fuel henv e = some (HIR.Expr.lit w)) :
    ∃ fenv', execInstrsFull fenv is = some fenv' ∧ fenv'.env v = some w ∧
      fenv'.store = fenv.store := by
  obtain ⟨-, fenv', hexec, hstore, w', hr, hreg⟩ :=
    lower_total.1 ρ supply e v is s' h hs hf henv fenv hrel fuel (.lit w) heval
  have hw : w' = w := (HIR.Expr.lit.inj hr).symm
  subst hw
  exact ⟨fenv', hexec, hreg, hstore⟩

/-! ## Statement-level totality

`lowerStmts_correct` consumes MIR success. This section supplies it: when the
HIR statement machine reaches a value on the straight-line fragment, the
emitted instruction sequence *runs*, and the resulting register file still
agrees with the source environment.

The statement carries the source run as a hypothesis rather than concluding
machine totality unconditionally, and that is not a convenience. `MIR.evalUnOp`
and `MIR.evalBinOp` are partial in exactly the way their HIR counterparts are
(`evalUnop_glue`/`evalBinop_glue`): applying `unop` to a mistyped literal
stalls on both sides, and no typing hypothesis is available here to exclude it.
So "the emitted code always runs" is false as stated, while "the emitted code
runs whenever the source does" is both true and the direction the D-2/D-4
contract requires. Machine failure still carries no claim about the source,
per the `ERA2-UNFREEZE` guardrail.
-/

/-- The runner never produces a value at zero fuel: its first equation is the
stuck case, whatever the statement list is. -/
theorem runHIRStmts_zero_stuck (henv : HEnv) (ss : List HIR.Stmt) (acc : HFlow)
    (henv' : HEnv) (out : HFlow)
    (hrun : runHIRStmts 0 henv ss acc = (out, henv')) : out = .stuck := by
  have hz : runHIRStmts 0 henv ss acc = (.stuck, henv) := rfl
  rw [hz] at hrun
  exact (Prod.mk.inj hrun).1.symm

/-- Statement-level totality: when `lowerStmts` succeeds on the fragment and
the HIR statement machine reaches a value, the emitted instructions run to a
final environment that holds that value in the result register, leaves the
store alone, and still agrees with the source environment. -/
theorem lowerStmts_total :
    ∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (lastVal : ValId)
      (ss : List HIR.Stmt) (ρ' : List (HIR.Id × ValId)) (v : ValId)
      (is : List Instr) (s' : Nat),
      lowerStmts ρ supply lastVal ss = some (ρ', v, is, s') →
      StraightStmts 256 ss → FreshAbove ρ supply → lastVal < supply →
      ∀ (acc : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env → fenv.env lastVal = some acc →
      ∀ (fuel : Nat) (henv' : HEnv) (out : HFlow) (w : Value),
      runHIRStmts fuel henv ss (.value (.lit acc)) = (out, henv') →
      runValue? out = some (.lit w) →
      ∃ fenv', execInstrsFull fenv is = some fenv' ∧ fenv'.env v = some w ∧
        fenv'.store = fenv.store ∧ RelEnv henv' ρ' fenv'.env := by
  intro ρ supply lastVal ss
  induction ss generalizing ρ supply lastVal with
  | nil =>
    intro ρ' v is s' h _hss _hf _hlast acc henv fenv hrel hacc fuel henv' out w hrun hval
    simp only [lowerStmts] at h
    have hp : (ρ, lastVal, ([] : List Instr), supply) = (ρ', v, is, s') :=
      Option.some.inj h
    have hρ' : ρ' = ρ :=
      (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
    have hv : v = lastVal :=
      (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
    have his : is = [] :=
      (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
    cases fuel with
    | zero =>
      have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
      rw [hout] at hval
      simp [runValue?] at hval
    | succ f =>
      have hstep : runHIRStmts (Nat.succ f) henv ([] : List HIR.Stmt) (.value (.lit acc))
          = (.value (.lit acc), henv) := rfl
      rw [hstep] at hrun
      have hout : out = .value (.lit acc) := (congrArg Prod.fst hrun).symm
      have hhenv : henv' = henv := (congrArg Prod.snd hrun).symm
      subst hout
      have hw : w = acc := (HIR.Expr.lit.inj (Option.some.inj hval)).symm
      refine ⟨fenv, ?_, ?_, rfl, ?_⟩
      · rw [his]; exact execInstrsFull_nil fenv
      · rw [hv, hw]; exact hacc
      · rw [hρ', hhenv]; exact hrel
  | cons st rest ih =>
    cases st with
    | exprStmt e =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fuel henv' out w hrun hval
      obtain ⟨hstr, _hb, hss'⟩ := StraightStmts_exprStmt hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨v0, ie, s1⟩ := p
        rw [he] at h
        simp only [] at h
        cases hr : lowerStmts ρ s1 v0 rest with
        | none => rw [hr] at h; simp at h
        | some q =>
          obtain ⟨ρ'', v', ie', s2⟩ := q
          rw [hr] at h
          simp only [] at h
          have hp : (ρ'', v', ie ++ ie', s2) = (ρ', v, is, s') := Option.some.inj h
          have hρ' : ρ' = ρ'' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
          have hv : v = v' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
          have his : is = ie ++ ie' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
          cases fuel with
          | zero =>
            have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
            rw [hout] at hval
            simp [runValue?] at hval
          | succ f =>
            have hstep : runHIRStmts (Nat.succ f) henv (.exprStmt e :: rest)
                (.value (.lit acc)) =
                (match evalHIR 256 henv e with
                  | none => (HFlow.stuck, henv)
                  | some v => runHIRStmts f henv rest (.value v)) := rfl
            rw [hstep] at hrun
            cases hev : evalHIR 256 henv e with
            | none =>
              rw [hev] at hrun
              have hout : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hout] at hval
              simp [runValue?] at hval
            | some r =>
              rw [hev] at hrun
              obtain ⟨fenv1, hexec1, hstore1, wE, hrE, hregE⟩ :=
                (lower_total.1 ρ supply e v0 ie s1 he hstr hf henv fenv hrel 256 r hev).2
              rw [hrE] at hrun
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              have hf1 : FreshAbove ρ s1 := FreshAbove.mono ρ supply s1 hs1 hf
              have hrel1 : RelEnv henv ρ fenv1.env :=
                RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1 hrel hf hexec1
              have hlast1 : v0 < s1 := lower_result_lt.1 ρ supply e v0 ie s1 he hf
              obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                ih ρ s1 v0 ρ'' v' ie' s2 hr hss' hf1 hlast1 wE henv fenv1 hrel1 hregE
                  f henv' out w hrun hval
              refine ⟨fenv', ?_, ?_, ?_, ?_⟩
              · rw [his, execInstrsFull_append, hexec1]; exact hexec'
              · rw [hv]; exact hreg'
              · rw [hstore', hstore1]
              · rw [hρ']; exact hrel'
    | varDecl id τ init =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fuel henv' out w hrun hval
      obtain ⟨hstr, _hb, hss'⟩ := StraightStmts_varDecl hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply init with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨va, ia, s1⟩ := p
        rw [he] at h
        simp only [] at h
        cases hr : lowerStmts ((id, va) :: ρ) s1 lastVal rest with
        | none => rw [hr] at h; simp at h
        | some q =>
          obtain ⟨ρ'', v', ia', s2⟩ := q
          rw [hr] at h
          simp only [] at h
          have hp : (ρ'', v', ia ++ ia', s2) = (ρ', v, is, s') := Option.some.inj h
          have hρ' : ρ' = ρ'' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
          have hv : v = v' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
          have his : is = ia ++ ia' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
          cases fuel with
          | zero =>
            have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
            rw [hout] at hval
            simp [runValue?] at hval
          | succ f =>
            have hstep : runHIRStmts (Nat.succ f) henv (.varDecl id τ init :: rest)
                (.value (.lit acc)) =
                (match evalHIR 256 henv init with
                  | none => (HFlow.stuck, henv)
                  | some v => runHIRStmts f ((id, v) :: henv) rest (.value (.lit acc))) := rfl
            rw [hstep] at hrun
            cases hev : evalHIR 256 henv init with
            | none =>
              rw [hev] at hrun
              have hout : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hout] at hval
              simp [runValue?] at hval
            | some r =>
              rw [hev] at hrun
              obtain ⟨fenv1, hexec1, hstore1, wE, hrE, hregE⟩ :=
                (lower_total.1 ρ supply init va ia s1 he hstr hf henv fenv hrel 256 r hev).2
              rw [hrE] at hrun
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              have hva : va < s1 := lower_result_lt.1 ρ supply init va ia s1 he hf
              have hf1 : FreshAbove ((id, va) :: ρ) s1 := by
                intro j u hmem
                rcases List.mem_cons.mp hmem with heq | hmem
                · cases heq
                  exact hva
                · exact Nat.lt_of_lt_of_le (hf j u hmem) hs1
              have hrel1 : RelEnv henv ρ fenv1.env :=
                RelEnv_exec henv ρ supply init va ia s1 he fenv fenv1 hrel hf hexec1
              have hrel2 : RelEnv ((id, .lit wE) :: henv) ((id, va) :: ρ) fenv1.env := by
                intro j u hlook
                by_cases hid : id = j
                · subst hid
                  have hu : u = va := by
                    have hh : rhoLookup ((id, va) :: ρ) id = some va :=
                      rhoLookup_cons_head id va ρ
                    rw [hh] at hlook
                    exact (Option.some.inj hlook).symm
                  subst hu
                  exact ⟨wE, by simp [lookupHEnv], hregE⟩
                · have hlook' : rhoLookup ρ j = some u := by
                    rw [rhoLookup_cons_ne hid] at hlook
                    exact hlook
                  obtain ⟨w', hlookH, hreg⟩ := hrel1 j u hlook'
                  exact ⟨w', by rw [lookupHEnv_cons_ne hid]; exact hlookH, hreg⟩
              have hacc1 : fenv1.env lastVal = some acc := by
                rw [lower_preserv_regs ρ supply init va ia s1 he fenv fenv1 hexec1 lastVal hlast]
                exact hacc
              have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
              obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                ih ((id, va) :: ρ) s1 lastVal ρ'' v' ia' s2 hr hss' hf1 hlast1 acc
                  ((id, .lit wE) :: henv) fenv1 hrel2 hacc1 f henv' out w hrun hval
              refine ⟨fenv', ?_, ?_, ?_, ?_⟩
              · rw [his, execInstrsFull_append, hexec1]; exact hexec'
              · rw [hv]; exact hreg'
              · rw [hstore', hstore1]
              · rw [hρ']; exact hrel'
    | assign id e =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fuel henv' out w hrun hval
      obtain ⟨hstr, _hb, hss'⟩ := StraightStmts_assign hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨v0, ie, s1⟩ := p
        rw [he] at h
        simp only [] at h
        cases hr : lowerStmts (updAssoc ρ id v0) s1 lastVal rest with
        | none => rw [hr] at h; simp at h
        | some q =>
          obtain ⟨ρ'', v', ie', s2⟩ := q
          rw [hr] at h
          simp only [] at h
          have hp : (ρ'', v', ie ++ ie', s2) = (ρ', v, is, s') := Option.some.inj h
          have hρ' : ρ' = ρ'' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
          have hv : v = v' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
          have his : is = ie ++ ie' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
          cases fuel with
          | zero =>
            have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
            rw [hout] at hval
            simp [runValue?] at hval
          | succ f =>
            have hstep : runHIRStmts (Nat.succ f) henv (.assign id e :: rest)
                (.value (.lit acc)) =
                (match evalHIR 256 henv e with
                  | none => (HFlow.stuck, henv)
                  | some v => runHIRStmts f (updateHEnv henv id v) rest
                      (.value (.lit acc))) := rfl
            rw [hstep] at hrun
            cases hev : evalHIR 256 henv e with
            | none =>
              rw [hev] at hrun
              have hout : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hout] at hval
              simp [runValue?] at hval
            | some r =>
              rw [hev] at hrun
              obtain ⟨fenv1, hexec1, hstore1, wE, hrE, hregE⟩ :=
                (lower_total.1 ρ supply e v0 ie s1 he hstr hf henv fenv hrel 256 r hev).2
              rw [hrE] at hrun
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              have hva : v0 < s1 := lower_result_lt.1 ρ supply e v0 ie s1 he hf
              have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
                intro j u hmem
                rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ | hmem
                · rw [hwu]
                  exact hva
                · exact Nat.lt_of_lt_of_le (hf j u hmem) hs1
              have hrel1 : RelEnv henv ρ fenv1.env :=
                RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1 hrel hf hexec1
              have hrel2 : RelEnv (updateHEnv henv id (.lit wE)) (updAssoc ρ id v0) fenv1.env :=
                RelEnv_update ρ henv fenv1.env id v0 wE hrel1 hregE
              have hacc1 : fenv1.env lastVal = some acc := by
                rw [lower_preserv_regs ρ supply e v0 ie s1 he fenv fenv1 hexec1 lastVal hlast]
                exact hacc
              have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
              obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                ih (updAssoc ρ id v0) s1 lastVal ρ'' v' ie' s2 hr hss' hf1 hlast1 acc
                  (updateHEnv henv id (.lit wE)) fenv1 hrel2 hacc1 f henv' out w hrun hval
              refine ⟨fenv', ?_, ?_, ?_, ?_⟩
              · rw [his, execInstrsFull_append, hexec1]; exact hexec'
              · rw [hv]; exact hreg'
              · rw [hstore', hstore1]
              · rw [hρ']; exact hrel'
    | returnStmt e =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fuel henv' out w hrun hval
      obtain ⟨hstr, _hb⟩ := StraightStmts_returnStmt hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨ve, ie, s1⟩ := p
        rw [he] at h
        have hp : (ρ, ve, ie, s1) = (ρ', v, is, s') := Option.some.inj h
        have hρ' : ρ' = ρ :=
          (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
        have hv : v = ve :=
          (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
        have his : is = ie :=
          (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
        cases fuel with
        | zero =>
          have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
          rw [hout] at hval
          simp [runValue?] at hval
        | succ f =>
          have hstep : runHIRStmts (Nat.succ f) henv (.returnStmt e :: rest)
              (.value (.lit acc)) =
              (match evalHIR 256 henv e with
                | none => (HFlow.stuck, henv)
                | some v => (HFlow.returned v, henv)) := rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
            rw [hev] at hrun
            have hout : out = .stuck := (congrArg Prod.fst hrun).symm
            rw [hout] at hval
            simp [runValue?] at hval
          | some r =>
            rw [hev] at hrun
            have hout : out = .returned r := (congrArg Prod.fst hrun).symm
            have hhenv : henv' = henv := (congrArg Prod.snd hrun).symm
            subst hout
            have hrl : r = .lit w := Option.some.inj hval
            obtain ⟨fenv', hexec', hstore', wE, hrE, hregE⟩ :=
              (lower_total.1 ρ supply e ve ie s1 he hstr hf henv fenv hrel 256 r hev).2
            have hwE : w = wE := by
              rw [hrl] at hrE
              exact HIR.Expr.lit.inj hrE
            subst hwE
            refine ⟨fenv', ?_, ?_, hstore', ?_⟩
            · rw [his]; exact hexec'
            · rw [hv]; exact hregE
            · rw [hρ', hhenv]
              exact RelEnv_exec henv ρ supply e ve ie s1 he fenv fenv' hrel hf hexec'
    | nop =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fuel henv' out w hrun hval
      have hss' := StraightStmts_nop hss
      simp only [lowerStmts] at h
      cases fuel with
      | zero =>
        have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
        rw [hout] at hval
        simp [runValue?] at hval
      | succ f =>
        have hstep : runHIRStmts (Nat.succ f) henv (.nop :: rest) (.value (.lit acc))
            = runHIRStmts f henv rest (.value (.lit acc)) := rfl
        rw [hstep] at hrun
        exact ih ρ supply lastVal ρ' v is s' h hss' hf hlast acc henv fenv hrel hacc
          f henv' out w hrun hval
    | «break» =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _ _ _ _ _
      nomatch hss
    | «continue» =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _ _ _ _ _
      nomatch hss
    | whileLoop cond body =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _ _ _ _ _
      nomatch hss
    | ifStmt cond th el =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _ _ _ _ _
      nomatch hss
    | matchStmt scrut arms =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _ _ _ _ _
      nomatch hss

/-- Program-level totality (A2's exit statement): when `lowerProgram` accepts a
straight-line program and the HIR statement machine reaches a literal value,
the emitted single-block function *runs* and returns that same value.

Together with `compile_correct_env` this closes the gap in both halves: the
source run implies a matching machine run (here), and a machine run implies a
matching source run (`lower_correct`, `compile_correct`). Nothing is claimed
about machine failure. -/
theorem compile_total (prog : HIR.Program) (func : Func) (store : Store)
    (h : lowerProgram prog = some func) (hss : StraightStmts 256 prog.stmts)
    (fuelH : Nat) (henv' : HEnv) (out : HFlow) (w : Value)
    (hrun : runHIRStmts fuelH [] prog.stmts (.value (.lit .unit)) = (out, henv'))
    (hval : runValue? out = some (.lit w)) :
    execFunc 2 func ⟨fun _ => none, store⟩ = some w := by
  simp only [lowerProgram] at h
  cases hs : lowerStmts [] 1 0 prog.stmts with
  | none => rw [hs] at h; simp at h
  | some p =>
    obtain ⟨ρ', v, is, s'⟩ := p
    rw [hs] at h
    simp only [] at h
    have hfunc : func = ⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0, .unitType⟩ :=
      (Option.some.inj h).symm
    have hlt : (0 : ValId) < 1 := Nat.zero_lt_one
    obtain ⟨fenv'', hexec, hreg, -, -⟩ :=
      lowerStmts_total [] 1 0 prog.stmts ρ' v is s' hs hss (FreshAbove_nil 1) hlt
        (.unit) [] ⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩
        (RelEnv_nil [] _) (prologue_env_zero store) fuelH henv' out w hrun hval
    have hall : execInstrsFull ⟨fun _ => none, store⟩ ([.const 0 .unit] ++ is) = some fenv'' :=
      execInstrsFull_prologue store is fenv'' hexec
    rw [hfunc]
    rw [execFunc_single_block (fuel := 0) _ ⟨0, [.const 0 .unit] ++ is, .return_ v⟩ _ v
      rfl rfl rfl]
    rw [hall]
    exact hreg

end Morph.HIRToMIRCorrect

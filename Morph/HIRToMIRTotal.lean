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

/-- The usable form of `lower_total`, with the source value already known to be
`w`: the emitted code runs to an environment holding `w` in the result register
and leaves the store untouched. This is the shape the statement layer needs,
where the value is pinned by the surrounding run rather than existentially
quantified. -/
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


end Morph.HIRToMIRCorrect

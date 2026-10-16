/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TaintFlow.Spec

namespace Morph.Specs.TaintFlow

/-!
## The typing judgment

`Flows ρ pc e l` states that under environment `ρ` and program-counter label
`pc`, the expression `e` may be evaluated and everything it influences is at
most `l`. The `ite` rule joins in `pc`: branching on a secret is an *implicit*
flow, and a rule that ignored the pc would let `if secret then () else ()`
declassify by control.
-/

inductive Flows (ρ : TEnv) (pc : Label) : TExpr → Label → Prop where
  | lit : Flows ρ pc .lit .pub
  | var : Flows ρ pc (.var x) (ρ x)
  | add : Flows ρ pc a la → Flows ρ pc b lb →
      Flows ρ pc (.add a b) (Label.join la lb)
  | ite : Flows ρ pc c lc → Flows ρ pc t lt → Flows ρ pc f lf →
      Flows ρ pc (.ite c t f) (Label.join pc (Label.join (Label.join lc lt) lf))
  | decl : Flows ρ pc e l → Flows ρ pc (.decl e) .pub

/-! ## SG-003: taint survives the dialect boundary -/

theorem taint_preserved (ρ : TEnv) (to : Dialect) (pc : Label) (e e' : TExpr)
    (h : translate to pc e = some e') : taint ρ e' = taint ρ e := by
  induction e generalizing e' with
  | lit => simp [translate] at h; subst h; rfl
  | var x => simp [translate] at h; subst h; rfl
  | add a b iha ihb =>
      generalize ha : translate to pc a = oa
      generalize hb : translate to pc b = ob
      cases oa with
      | none => simp [translate, ha] at h
      | some a' =>
          cases ob with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              simp [translate, ha, hb] at h
              subst e'
              simp only [taint]
              rw [iha a' ha, ihb b' hb]
  | ite c t f ihc iht ihf =>
      generalize hc : translate to pc c = oc
      generalize ht : translate to pc t = ot
      generalize hf : translate to pc f = of
      cases oc with
      | none => simp [translate, hc] at h
      | some c' =>
          cases ot with
          | none => simp [translate, hc, ht] at h
          | some t' =>
              cases of with
              | none => simp [translate, hc, ht, hf] at h
              | some f' =>
                  simp [translate, hc, ht, hf] at h
                  subst e'
                  simp only [taint]
                  rw [ihc c' hc, iht t' ht, ihf f' hf]
  | decl e ih =>
      simp only [translate] at h
      split at h
      · cases h
      · generalize he : translate to pc e = oe
        cases oe with
        | none => simp [he] at h
        | some e' =>
            simp [he] at h
            subst h
            exact rfl

/-- **Robustness.** An untrusted program counter cannot carry a
declassification into the strict dialect: the translation is *rejected*.
This is the dialect-boundary instance of Zdancewic & Myers' robust
declassification — an attacker who controls the decision to declassify must not
control the release. -/
theorem reject_untrusted_decl (pc : Label) (e : TExpr) (huntrusted : pc = .pub) :
    translate .strict pc (.decl e) = none := by
  simp [translate, huntrusted]

/-- Conversely a trusted pc may declassify into the strict dialect. -/
theorem allow_trusted_decl (e e' : TExpr) (he : translate .strict .sec e = some e') :
    translate .strict .sec (.decl e) = some (.decl e') := by
  simp only [translate]
  rw [he]
  rfl

theorem no_decl_after_translation (pc : Label) (e e' : TExpr)
    (h : translate .strict pc e = some e') : NoDecl e' ∨ pc = .sec := by
  induction e generalizing e' with
  | lit => simp [translate] at h; subst h; exact Or.inl NoDecl.lit
  | var x => simp [translate] at h; subst h; exact Or.inl (NoDecl.var)
  | add a b iha ihb =>
      generalize ha : translate .strict pc a = oa
      generalize hb : translate .strict pc b = ob
      cases oa with
      | none => simp [translate, ha] at h
      | some a' =>
          cases ob with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              simp [translate, ha, hb] at h
              subst e'
              rcases iha a' ha with hna | hp
              · rcases ihb b' hb with hnb | hp
                · exact Or.inl (NoDecl.add hna hnb)
                · exact Or.inr hp
              · exact Or.inr hp
  | ite c t f ihc iht ihf =>
      generalize hc : translate .strict pc c = oc
      generalize ht : translate .strict pc t = ot
      generalize hf : translate .strict pc f = of
      cases oc with
      | none => simp [translate, hc] at h
      | some c' =>
          cases ot with
          | none => simp [translate, hc, ht] at h
          | some t' =>
              cases of with
              | none => simp [translate, hc, ht, hf] at h
              | some f' =>
                  simp [translate, hc, ht, hf] at h
                  subst e'
                  rcases ihc c' hc with hnc | hp
                  · rcases iht t' ht with hnt | hp
                    · rcases ihf f' hf with hnf | hp
                      · exact Or.inl (NoDecl.ite hnc hnt hnf)
                      · exact Or.inr hp
                    · exact Or.inr hp
                  · exact Or.inr hp
  | decl e ih =>
      by_cases hpc : pc = .sec
      · exact Or.inr hpc
      · simp only [translate, hpc, Ne.symm hpc, and_false] at h
        generalize hde : translate .strict pc e = ode at h
        cases ode with
        | none => simp [hde] at h
        | some e₁ => simp [hde] at h; exact Or.inr h.1

theorem flows_translation (ρ : TEnv) (to : Dialect) (pc : Label)
    (e e' : TExpr) (l : Label) (hflow : Flows ρ pc e l)
    (htr : translate to pc e = some e') : Flows ρ pc e' l := by
  revert e'
  induction hflow
  case lit => intro e' htr; rw [translate] at htr; injection htr with h; subst h; exact Flows.lit
  case var x => intro e' htr; rw [translate] at htr; injection htr with h; subst h; exact Flows.var
  case add a la b lb ha hb iha ihb =>
      intro e' htr
      generalize hca : translate to pc a = oa
      generalize hcb : translate to pc b = ob
      cases oa with
      | none => simp [translate, hca] at htr
      | some a' =>
          cases ob with
          | none => simp [translate, hca, hcb] at htr
          | some b' =>
              simp [translate, hca, hcb] at htr
              subst e'
              exact Flows.add (iha a' hca) (ihb b' hcb)
  case ite c lc t lt f lf hc ht hf ihc iht ihf =>
      intro e' htr
      generalize hcc : translate to pc c = oc
      generalize hct : translate to pc t = ot
      generalize hcf : translate to pc f = of
      cases oc with
      | none => simp [translate, hcc] at htr
      | some c' =>
          cases ot with
          | none => simp [translate, hcc, hct] at htr
          | some t' =>
              cases of with
              | none => simp [translate, hcc, hct, hcf] at htr
              | some f' =>
                  simp [translate, hcc, hct, hcf] at htr
                  subst e'
                  exact Flows.ite (ihc c' hcc) (iht t' hct) (ihf f' hcf)
  case decl e l he ihe =>
      intro e' htr
      simp only [translate] at htr
      split at htr
      · cases htr
      · generalize hde : translate to pc e = ode
        cases ode with
        | none => simp [hde] at htr
        | some e₁ =>
            simp [hde] at htr
            subst htr
            exact Flows.decl (ihe e₁ hde)

/-! ## Noninterference

Noninterference is a statement about *programs*, not about single
expressions: reading a secret is fine, writing one into a public variable is
not. A program is a list of assignments; an assignment `x := e` is allowed
only when the label it writes does not exceed what `x` may already hold.
-/

/-- Assign `x := e`; `x` now holds `e`'s taint. -/
def assign (ρ : TEnv) (x : String) (e : TExpr) : TEnv :=
  fun y => if y = x then taint ρ e else ρ y

/-- Run a list of assignments. -/
def run (ρ : TEnv) : List (String × TExpr) → TEnv
  | [] => ρ
  | (x, e) :: rest => run (assign ρ x e) rest

/-- Translate a whole program; rejects if any statement is rejected. -/
def translateProg (to : Dialect) (pc : Label) : List (String × TExpr) →
    Option (List (String × TExpr))
  | [] => some []
  | (x, e) :: rest =>
      match translate to pc e, translateProg to pc rest with
      | some e', some rest' => some ((x, e') :: rest')
      | _, _ => none

/-- An assignment `x := e` is allowed only if the label written does not
exceed the label `x` already has. This is the sink check. -/
def AllowedAssign (ρ : TEnv) (x : String) (e : TExpr) : Prop :=
  Label.le (taint ρ e) (ρ x)

/-- Every assignment of the program passes the sink check. -/
def Allowed (ρ : TEnv) : List (String × TExpr) → Prop
  | [] => True
  | (x, e) :: rest => AllowedAssign ρ x e ∧ Allowed (assign ρ x e) rest

theorem allowed_no_leak : ∀ (ρ : TEnv) (prog : List (String × TExpr)),
    Allowed ρ prog → ∀ y, (run ρ prog) y = .sec → ρ y = .sec := by
  intro ρ prog
  revert ρ
  induction prog with
  | nil =>
      intro ρ _ y hy
      exact hy
  | cons stmt rest ih =>
      rcases stmt with ⟨x, e⟩
      intro ρ h y hy
      simp only [Allowed] at h
      obtain ⟨hassign, hrest⟩ := h
      simp only [run] at hy
      by_cases hxy : y = x
      · subst hxy
        have hsec := ih (assign ρ y e) hrest y hy
        simp only [assign, if_pos] at hsec
        cases hρy : ρ y with
        | sec => rfl
        | pub =>
            have hbad : Label.le (taint ρ e) .pub := by
              simpa only [AllowedAssign, hρy] using hassign
            rw [hsec] at hbad
            simp [Label.le] at hbad
      · have h' := ih (assign ρ x e) hrest y hy
        simpa only [assign, hxy, if_neg] using h'

/-- **The dialect boundary preserves the sink check.** `taint_preserved` makes
each translated statement label-identical, so the environment after each
assignment is literally unchanged and the allowedness proof transfers
verbatim. -/
theorem allowed_preserved : ∀ (ρ : TEnv) (prog prog' : List (String × TExpr)),
    Allowed ρ prog → translateProg .strict .sec prog = some prog' →
    Allowed ρ prog' := by
  intro ρ prog
  revert ρ
  induction prog with
  | nil =>
      intro ρ prog' _ htr
      simp only [translateProg] at htr
      injection htr with htr
      subst prog'
      exact trivial
  | cons stmt rest ih =>
      rcases stmt with ⟨x, e⟩
      intro ρ prog' h htr
      obtain ⟨ha, hrest⟩ := h
      generalize hde : translate .strict .sec e = oe at htr
      cases oe with
      | none =>
          simp only [translateProg, hde] at htr
          cases htr
      | some e' =>
          generalize hrp : translateProg .strict .sec rest = orp at htr
          cases orp with
          | none =>
              simp only [translateProg, hde, hrp] at htr
              cases htr
          | some rest' =>
              simp only [translateProg, hde, hrp] at htr
              injection htr with htr
              subst prog'
              simp only [Allowed]
              have henv : assign ρ x e' = assign ρ x e := by
                funext y
                by_cases hxy : y = x
                · simp only [assign, if_pos hxy,
                    taint_preserved ρ .strict .sec e e' hde]
                · simp only [assign, if_neg hxy]
              refine ⟨?_, ?_⟩
              · simp only [AllowedAssign]
                rw [taint_preserved ρ .strict .sec e e' hde]
                exact ha
              · rw [henv]
                exact ih (assign ρ x e) rest' hrest hrp

/-- **SG-003, end to end.** A program that is noninterfering stays
noninterfering after translation into the strict dialect: crossing a dialect
boundary cannot create a leak. -/
theorem boundary_preserves_noninterference (ρ : TEnv)
    (prog prog' : List (String × TExpr)) (h : Allowed ρ prog)
    (htr : translateProg .strict .sec prog = some prog') :
    ∀ y, (run ρ prog') y = .sec → ρ y = .sec :=
  allowed_no_leak ρ prog' (allowed_preserved ρ prog prog' h htr)

end Morph.Specs.TaintFlow

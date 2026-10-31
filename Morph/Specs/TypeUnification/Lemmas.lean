/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.TypeUnification.Spec

/-!
# Unification soundness (loop 101)

`unifyF` is Robinson's algorithm in fuel-recursion form, over the fragment of
`spec/type/type_unification_spec.md`'s type algebra (variables, base types,
arrows). `unifyF_sound` is the spec's soundness requirement: whatever the
unifier returns really makes the two terms equal. Composition (`comp`) is
proved compatible with application (`apply_comp`), which is what the arrow
case needs.
-/

namespace Morph.Specs.TypeUnification

/-- The identity substitution applies as the identity. -/
theorem apply_id : ∀ t, apply Subst.id t = t := by
  intro t
  induction t with
  | v _ => rfl
  | c _ => rfl
  | arrow a b ihp ihb =>
      show UTerm.arrow (apply Subst.id a) (apply Subst.id b) = UTerm.arrow a b
      rw [ihp, ihb]

/-- Substitution composition is compatible with application. -/
theorem apply_comp (τ σ : Subst) :
    ∀ t, apply (comp τ σ) t = apply τ (apply σ t) := by
  intro t
  induction t with
  | v _ => rfl
  | c _ => rfl
  | arrow a b ihp ihb =>
      show UTerm.arrow (apply (comp τ σ) a) (apply (comp τ σ) b) =
        apply τ (apply σ (UTerm.arrow a b))
      rw [ihp, ihb, apply, apply]

/-- The unifier: fuel-recursion form of Robinson's algorithm. The occurs
check fires before every variable binding; variable–variable unification
binds left to right; every mismatched constructor pair has an explicit
failure arm. -/
def unifyF : Nat → UTerm → UTerm → Option Subst
  | 0, _, _ => none
  | _ + 1, .v x, .v y => if x = y then some Subst.id else some (update Subst.id x (.v y))
  | _ + 1, .v x, t => if occurs x t then none else some (update Subst.id x t)
  | _ + 1, .c s, .c t => if s = t then some Subst.id else none
  | (fuel + 1), .arrow a b, .arrow a' b' =>
      match unifyF fuel a a' with
      | none => none
      | some σ =>
          match unifyF fuel (apply σ b) (apply σ b') with
          | none => none
          | some τ => some (comp τ σ)
  | _ + 1, .c _, .v _ => none
  | _ + 1, .c _, .arrow _ _ => none
  | _ + 1, .arrow _ _, .v _ => none
  | _ + 1, .arrow _ _, .c _ => none

/-- Shape equations: `unifyF` reduces on constructor patterns, so each
shape of the soundness proof gets a plain `rfl` equation to rewrite with —
no equation-compiler side conditions. -/

theorem unifyF_vv (fuel : Nat) (x y : Nat) :
    unifyF (fuel + 1) (.v x) (.v y) =
      if x = y then some Subst.id else some (update Subst.id x (.v y)) := rfl

theorem unifyF_vc (fuel : Nat) (x : Nat) (s : String) :
    unifyF (fuel + 1) (.v x) (.c s) =
      if occurs x (.c s) then none else some (update Subst.id x (.c s)) := rfl

theorem unifyF_varr (fuel : Nat) (x : Nat) (p q : UTerm) :
    unifyF (fuel + 1) (.v x) (.arrow p q) =
      if occurs x (.arrow p q) then none else some (update Subst.id x (.arrow p q)) := rfl

theorem unifyF_cc (fuel : Nat) (s t : String) :
    unifyF (fuel + 1) (.c s) (.c t) = if s = t then some Subst.id else none := rfl

theorem unifyF_arrv (fuel : Nat) (p q : UTerm) (x : Nat) :
    unifyF (fuel + 1) (.arrow p q) (.v x) = none := rfl

theorem unifyF_arrc (fuel : Nat) (p q : UTerm) (s : String) :
    unifyF (fuel + 1) (.arrow p q) (.c s) = none := rfl

theorem unifyF_cv (fuel : Nat) (s : String) (x : Nat) :
    unifyF (fuel + 1) (.c s) (.v x) = none := rfl

theorem unifyF_carr (fuel : Nat) (s : String) (p q : UTerm) :
    unifyF (fuel + 1) (.c s) (.arrow p q) = none := rfl

theorem unifyF_arrarr (fuel : Nat) (a b a' b' : UTerm) :
    unifyF (fuel + 1) (.arrow a b) (.arrow a' b') =
      match unifyF fuel a a' with
      | none => none
      | some σ =>
          match unifyF fuel (apply σ b) (apply σ b') with
          | none => none
          | some τ => some (comp τ σ) := rfl

/-- **Unification soundness** — the spec's core requirement: whatever
`unifyF` returns makes the two terms equal. -/
theorem unifyF_sound : ∀ (fuel : Nat) (a b : UTerm) (σ : Subst),
    unifyF fuel a b = some σ → apply σ a = apply σ b := by
  intro fuel
  induction fuel with
  | zero => intro a b σ h; simp [unifyF] at h
  | succ fuel ih =>
      intro a b σ h
      cases a with
      | v x =>
          cases b with
          | v y =>
              rw [unifyF_vv] at h
              split at h
              · next hxy =>
                  simp only [Option.some.injEq] at h
                  subst h
                  rw [hxy]
              · next hne =>
                  simp only [Option.some.injEq] at h
                  have hσ : σ = update Subst.id x (.v y) := h.symm
                  subst hσ
                  show (if x = x then UTerm.v y else Subst.id x) =
                    (if y = x then UTerm.v y else Subst.id y)
                  rw [if_pos rfl, if_neg (fun he => hne he.symm)]
                  rfl
          | c s =>
              rw [unifyF_vc] at h
              simp only [occurs, Bool.false_eq_true, if_false, Option.some.injEq] at h
              have hσ : σ = update Subst.id x (.c s) := h.symm
              subst hσ
              have hl : apply (update Subst.id x (.c s)) (.v x) = .c s := by
                simp [apply, update]
              rw [hl, apply_update_of_not_occurs Subst.id x (.c s) rfl, apply_id]
          | arrow p q =>
              rw [unifyF_varr] at h
              split at h
              · cases h
              · next hocc =>
                  have hf : occurs x (UTerm.arrow p q) = false := by simp [hocc]
                  simp only [Option.some.injEq] at h
                  have hσ : σ = update Subst.id x (.arrow p q) := h.symm
                  subst hσ
                  have hl : apply (update Subst.id x (.arrow p q)) (.v x) = .arrow p q := by
                    simp [apply, update]
                  rw [hl, apply_update_of_not_occurs Subst.id x (.arrow p q) hf, apply_id]
      | c s =>
          cases b with
          | v x => simp [unifyF] at h
          | c t =>
              rw [unifyF_cc] at h
              split at h
              · next heq =>
                  simp only [Option.some.injEq] at h
                  subst h
                  rw [heq]
              · cases h
          | arrow p q => simp [unifyF] at h
      | arrow p q =>
          cases b with
          | v x => simp [unifyF] at h
          | c s' => simp [unifyF] at h
          | arrow p' q' =>
              rw [unifyF_arrarr] at h
              split at h
              · cases h
              · next σ₁ hσ₁ =>
                  have hps : apply σ₁ p = apply σ₁ p' := ih _ _ _ hσ₁
                  split at h
                  · cases h
                  · next τ hτ =>
                      simp only [Option.some.injEq] at h
                      have hσ : σ = comp τ σ₁ := h.symm
                      subst hσ
                      rw [apply_comp, apply_comp]
                      simp only [apply]
                      rw [hps, ih _ _ _ hτ]

end Morph.Specs.TypeUnification

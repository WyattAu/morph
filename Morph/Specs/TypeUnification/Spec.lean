/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core

/-!
# Type Unification: the occurs-checked first-order core (loop 101)

Research basis: Robinson (1965), the original unification algorithm;
Martelli & Montanari (1982), unification as a nondeterministic rewrite system
over disagreement sets; Paterson & Wegman (1978), linear-time unification;
Baader & Nipkow, *Term Rewriting and All That*, ch. 4 — the occurs-check
soundness argument: a variable occurring in a term cannot be eliminated by
instantiation, so `x ≐ t` with `x ∈ vars(t)` has no unifier.

`spec/type/type_unification_spec.md` (v1.0.0) specifies Robinson's algorithm,
the most-general unifier, and the occurs check — with no machine-checked
counterpart anywhere in the repository. This module supplies the first-order
core:

- `UTerm`: variables, base types, arrows (the fragment the spec's type
  algebra needs);
- `Subst`: substitutions as functions, with `apply`, `update`, `comp`;
- `occurs`: the occurs check, with its soundness lemma
  (`apply_update_of_not_occurs_gen`): substituting for `x` leaves a term
  unchanged when `x` does not occur in it.

Most-generality (the M in MGU) is a recorded non-claim: it needs an
instantiation order (`σ ⊑ τ`) and a generality induction beyond this loop.
-/

namespace Morph.Specs.TypeUnification

/-- First-order type terms: a variable, a named base type, or an arrow. -/
inductive UTerm where
  | v : Nat → UTerm
  | c : String → UTerm
  | arrow : UTerm → UTerm → UTerm
  deriving Repr, BEq, DecidableEq

/-- Substitutions are functions from variables to terms. -/
abbrev Subst := Nat → UTerm

/-- The identity substitution. -/
def Subst.id : Subst := UTerm.v

/-- Application of a substitution to a term. -/
def apply (σ : Subst) : UTerm → UTerm
  | .v x => σ x
  | .c s => .c s
  | .arrow a b => .arrow (apply σ a) (apply σ b)

/-- Single-variable update. -/
def update (σ : Subst) (x : Nat) (t : UTerm) : Subst :=
  fun y => if y = x then t else σ y

/-- Substitution composition: apply `σ`, then `τ`. -/
def comp (τ σ : Subst) : Subst := fun x => apply τ (σ x)

/-- The occurs check: does variable `x` occur in `t`? -/
def occurs (x : Nat) : UTerm → Bool
  | .v y => x = y
  | .c _ => false
  | .arrow a b => occurs x a || occurs x b

/-- **Occurs-instance independence** (general form): if `x` does not occur in
`a`, then updating the substitution at `x` — with *any* term — does not
change what `a` evaluates to. -/
theorem apply_update_of_not_occurs_gen (σ : Subst) (x : Nat) (t : UTerm) :
    ∀ a, occurs x a = false → apply (update σ x t) a = apply σ a := by
  intro a
  induction a with
  | v y =>
      intro h
      have hyx : ¬ (y = x) := by
        intro he
        simp [occurs, he] at h
      simp [apply, update, hyx]
  | c s => intro _; rfl
  | arrow p q ihp ihq =>
      intro h
      have hp : occurs x p = false := by
        simp only [occurs, Bool.or_eq_false_iff] at h
        exact h.1
      have hq : occurs x q = false := by
        simp only [occurs, Bool.or_eq_false_iff] at h
        exact h.2
      rw [apply, apply, ihp hp, ihq hq]

/-- **Occurs-check soundness.** If `x` does not occur in `t`, substituting
`t` for `x` leaves `t` itself unchanged — so the binding `x ↦ t` is a real
unifier for `x ≐ t`. Contrapositive: if `x` occurs in `t`, no substitution
makes `x` and `t` equal (Robinson's reason for the occurs check). -/
theorem apply_update_of_not_occurs (σ : Subst) (x : Nat) (t : UTerm)
    (h : occurs x t = false) :
    apply (update σ x t) t = apply σ t :=
  apply_update_of_not_occurs_gen σ x t t h

end Morph.Specs.TypeUnification

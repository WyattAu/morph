/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.DialectSemantics.Spec
import Morph.Syntax

/-!
# Translation validation for cross-dialect translation

Discharges SG-001. Each theorem is an Alive2-style obligation: a *single*
accepted translation preserves the denotation.
-/

namespace Morph.Specs.DialectSemantics

open Morph.Specs.DialectProjection

/-- **Translation validation.** An accepted translation preserves the
denotation: source and target evaluate to the same value, or to the same absence
of one. This is the obligation Alive2 discharges per pass, here proved once for
the whole dialect system. -/
theorem translate_preserves_eval {target : Dialect} {e e' : Term}
    (h : translate target e = some e') : eval target e = eval target e' := by
  induction e generalizing e' with
  | val r d => simp [translate] at h; cases h; rfl
  | add a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .add a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp only [eval, iha ha, ihb hb]
  | mul a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .mul a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp only [eval, iha ha, ihb hb]
  | sub a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .sub a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp only [eval, iha ha, ihb hb]
  | neg a iha =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          have he' : e' = .neg a' := by simpa [translate, ha] using h.symm
          subst he'
          simp only [eval, iha ha]
  | rawptr a iha =>
      by_cases hp : permits target (.rawptr a) = true
      · cases ha : translate target a with
        | none => simp [translate, hp, ha] at h
        | some a' =>
            have he' : e' = .rawptr a' := by simpa [translate, hp, ha] using h.symm
            subst he'
            simp only [eval]
      · simp [translate, hp] at h
  | inlineAsm a iha =>
      by_cases hp : permits target (.inlineAsm a) = true
      · cases ha : translate target a with
        | none => simp [translate, hp, ha] at h
        | some a' =>
            have he' : e' = .inlineAsm a' := by simpa [translate, hp, ha] using h.symm
            subst he'
            simp only [eval]
      · simp [translate, hp] at h

/-- **An accepted translation is entirely in the target dialect.** -/
theorem translate_in_target {target : Dialect} {e e' : Term}
    (h : translate target e = some e') : dialectOf e' = target := by
  induction e generalizing e' with
  | val r d => simp [translate] at h; cases h; rfl
  | add a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .add a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp [dialectOf, iha ha]
  | mul a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .mul a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp [dialectOf, iha ha]
  | sub a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .sub a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp [dialectOf, iha ha]
  | neg a iha =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          have he' : e' = .neg a' := by simpa [translate, ha] using h.symm
          subst he'
          simp [dialectOf, iha ha]
  | rawptr a iha =>
      by_cases hp : permits target (.rawptr a) = true
      · cases ha : translate target a with
        | none => simp [translate, hp, ha] at h
        | some a' =>
            have he' : e' = .rawptr a' := by simpa [translate, hp, ha] using h.symm
            subst he'
            simp [dialectOf, iha ha]
      · simp [translate, hp] at h
  | inlineAsm a iha =>
      by_cases hp : permits target (.inlineAsm a) = true
      · cases ha : translate target a with
        | none => simp [translate, hp, ha] at h
        | some a' =>
            have he' : e' = .inlineAsm a' := by simpa [translate, hp, ha] using h.symm
            subst he'
            simp [dialectOf, iha ha]
      · simp [translate, hp] at h

/-! ### Refusal is total on forbidden operations

The counterpart of preservation: a translation that *could* change meaning must
not exist. -/

/-- **`unsafe` is the permissive endpoint.** Every term translates into it: no
term is refused, because it permits every primitive. -/
theorem translate_unsafe_total : ∀ (e : Term), ∃ e', translate .«unsafe» e = some e' := by
  intro e
  induction e with
  | val r d => exact ⟨.val r .«unsafe», by simp [translate]⟩
  | add a b iha ihb =>
      obtain ⟨a', ha⟩ := iha
      obtain ⟨b', hb⟩ := ihb
      exact ⟨.add a' b', by simp [translate, ha, hb]⟩
  | mul a b iha ihb =>
      obtain ⟨a', ha⟩ := iha
      obtain ⟨b', hb⟩ := ihb
      exact ⟨.mul a' b', by simp [translate, ha, hb]⟩
  | sub a b iha ihb =>
      obtain ⟨a', ha⟩ := iha
      obtain ⟨b', hb⟩ := ihb
      exact ⟨.sub a' b', by simp [translate, ha, hb]⟩
  | neg a iha =>
      obtain ⟨a', ha⟩ := iha
      exact ⟨.neg a', by simp [translate, ha]⟩
  | rawptr a iha =>
      obtain ⟨a', ha⟩ := iha
      exact ⟨.rawptr a', by simp [translate, ha, permits]⟩
  | inlineAsm a iha =>
      obtain ⟨a', ha⟩ := iha
      exact ⟨.inlineAsm a', by simp [translate, ha, permits]⟩

/-- **`core` refuses what `unsafe` accepts.** An authority-requiring primitive
does not survive translation into `core`. This asymmetry is the point of the
dialect system: the same program is accepted at one stage and refused at another,
and the refusal is total rather than best-effort. -/
theorem translate_core_refuses_rawptr :
    translate .core (.rawptr (.val 0 .«unsafe»)) = none := by
  rw [translate]
  simp [permits]

/-- A safe primitive does survive. -/
theorem translate_core_accepts_arith :
    translate .core (.add (.val 1 .core) (.val 2 .core)) =
      some (.add (.val 1 .core) (.val 2 .core)) := by
  simp [translate]

/-- **Refusal is exactly what `safe` forbids, in one direction.** An unsafe
term — one performing an authority-requiring primitive — is always refused by
`core`, at any depth. -/
theorem translate_core_refuses_unsafe : ∀ (e : Term), ¬ safe e → translate .core e = none := by
  intro e
  induction e with
  | val r d => intro h; simp [safe] at h
  | add a b iha ihb =>
      intro h
      simp only [safe] at h
      by_cases ha : safe a
      · by_cases hb : safe b
        · simp [ha, hb] at h
        · rw [translate]
          simp [ihb hb]
      · rw [translate]
        simp [iha ha]
  | mul a b iha ihb =>
      intro h
      simp only [safe] at h
      by_cases ha : safe a
      · by_cases hb : safe b
        · simp [ha, hb] at h
        · rw [translate]
          simp [ihb hb]
      · rw [translate]
        simp [iha ha]
  | sub a b iha ihb =>
      intro h
      simp only [safe] at h
      by_cases ha : safe a
      · by_cases hb : safe b
        · simp [ha, hb] at h
        · rw [translate]
          simp [ihb hb]
      · rw [translate]
        simp [iha ha]
  | neg a iha =>
      intro h
      simp only [safe] at h
      rw [translate]
      simp [iha h]
  | rawptr a iha => intro _; rw [translate]; simp [permits]
  | inlineAsm a iha => intro _; rw [translate]; simp [permits]

/-- **Refusal is exactly what `safe` forbids, in the other direction.** A safe
term always translates into `core`. So the `core` capability check is not
heuristic: it accepts exactly the safe terms. -/
theorem translate_core_accepts_safe : ∀ (e : Term), safe e → ∃ e', translate .core e = some e' := by
  intro e
  induction e with
  | val r d => intro _; exact ⟨.val r .core, by simp [translate]⟩
  | add a b iha ihb =>
      intro h
      obtain ⟨a', ha⟩ := iha h.1
      obtain ⟨b', hb⟩ := ihb h.2
      exact ⟨.add a' b', by simp [translate, ha, hb]⟩
  | mul a b iha ihb =>
      intro h
      obtain ⟨a', ha⟩ := iha h.1
      obtain ⟨b', hb⟩ := ihb h.2
      exact ⟨.mul a' b', by simp [translate, ha, hb]⟩
  | sub a b iha ihb =>
      intro h
      obtain ⟨a', ha⟩ := iha h.1
      obtain ⟨b', hb⟩ := ihb h.2
      exact ⟨.sub a' b', by simp [translate, ha, hb]⟩
  | neg a iha =>
      intro h
      obtain ⟨a', ha⟩ := iha h
      exact ⟨.neg a', by simp [translate, ha]⟩
  | rawptr a iha => intro h; exact absurd h (by simp [safe])
  | inlineAsm a iha => intro h; exact absurd h (by simp [safe])

/-- **The `core` capability check is exact:** translation into `core` succeeds
iff the term is safe. -/
theorem translate_core_iff_safe (e : Term) :
    (∃ e', translate .core e = some e') ↔ safe e := by
  constructor
  · rintro ⟨e', ht⟩
    refine Classical.byContradiction ?_
    intro hn
    rw [translate_core_refuses_unsafe e hn] at ht
    cases ht
  · intro h
    exact translate_core_accepts_safe e h

/-- **The old pass-through is unsound where translation is not.** `lower`
retags into `core` a term containing an operation `core` does not permit: the
result is an accepted translation into a dialect that may not perform it.
`translate` refuses instead. -/
theorem lower_smuggles :
    lower { source := .«unsafe», target := .core, name := "bad" }
      (.op "raw-ptr" [.val ⟨.«unsafe», 0⟩]) = .op "raw-ptr" [.val ⟨.core, 0⟩] := by
  simp [lower]

/-! ### Loop 63: bridge to `Morph.Syntax.Expr` (refinement)

Research: CompCert (Leroy 2009 — forward simulation between source and
target languages as the refinement obligation; each pass proves
`src ⇓ v → tgt ⇓ v`); CakeML (verified lowering with per-pass simulations);
Alive2 (translation validation per pass); MLIR (dialect lowering with
declarative verifiers — the industrial analogue of `permits`).

Language comparison: CompCert (Cminor→RTL→assembly, simulation diagrams);
Cranelift (legalization expands unsupported ops or refuses — same shape as
`translate` refusing); Rust MIR (unsized/embeddings are total on the safe
fragment); MLIR (dialect conversion is partial and verifier-checked).

The move: embed the dialect `Term` language into the real surface syntax
`Morph.Syntax.Expr`. The embedding is partial (`Option`) — authority
operations have no surface counterpart, which is exactly the honesty the old
`lower` lacked. On the safe fragment it is total, and it commutes with
`translate`: embedding factors through translation (the refinement square),
since `translate` only retags and `toExpr` erases tags.

Boundary (named, not approximated): denotational correspondence
(`eval` vs an `Expr` evaluator) is deferred — `Morph/Semantics.lean` has a
small-step relation but no big-step evaluator to state it against. What is
proved here is the structural refinement: totality on `safe`, refusal on
`¬safe`, and commutation with every accepted translation.
-/

/-- Embed a dialect term into surface syntax. Partial: `rawptr`/`inlineAsm`
have no surface counterpart and map to `none`. Tags are erased. -/
def toExpr : Term → Option Morph.Syntax.Expr
  | .val r _ => some (Morph.Syntax.Expr.lit (Morph.Core.Value.int (r : Int)))
  | .add a b =>
      match toExpr a, toExpr b with
      | some a', some b' =>
          some (Morph.Syntax.Expr.binop Morph.Core.Operator.add a' b')
      | _, _ => none
  | .mul a b =>
      match toExpr a, toExpr b with
      | some a', some b' =>
          some (Morph.Syntax.Expr.binop Morph.Core.Operator.mul a' b')
      | _, _ => none
  | .sub a b =>
      match toExpr a, toExpr b with
      | some a', some b' =>
          some (Morph.Syntax.Expr.binop Morph.Core.Operator.sub a' b')
      | _, _ => none
  | .neg a =>
      (toExpr a).map (fun a' => Morph.Syntax.Expr.binop
        Morph.Core.Operator.sub
        (Morph.Syntax.Expr.lit (Morph.Core.Value.int 0)) a')
  | .rawptr _ => none
  | .inlineAsm _ => none

/-- The embedding is total on the safe fragment. -/
theorem toExpr_safe_total : ∀ (e : Term), safe e → ∃ e', toExpr e = some e' := by
  intro e
  induction e with
  | val r d =>
      intro _
      exact ⟨Morph.Syntax.Expr.lit (Morph.Core.Value.int (r : Int)), by simp [toExpr]⟩
  | add a b iha ihb =>
      intro h
      obtain ⟨a', ha⟩ := iha h.1
      obtain ⟨b', hb⟩ := ihb h.2
      exact ⟨Morph.Syntax.Expr.binop Morph.Core.Operator.add a' b',
        by simp [toExpr, ha, hb]⟩
  | mul a b iha ihb =>
      intro h
      obtain ⟨a', ha⟩ := iha h.1
      obtain ⟨b', hb⟩ := ihb h.2
      exact ⟨Morph.Syntax.Expr.binop Morph.Core.Operator.mul a' b',
        by simp [toExpr, ha, hb]⟩
  | sub a b iha ihb =>
      intro h
      obtain ⟨a', ha⟩ := iha h.1
      obtain ⟨b', hb⟩ := ihb h.2
      exact ⟨Morph.Syntax.Expr.binop Morph.Core.Operator.sub a' b',
        by simp [toExpr, ha, hb]⟩
  | neg a iha =>
      intro h
      obtain ⟨a', ha⟩ := iha h
      exact ⟨Morph.Syntax.Expr.binop Morph.Core.Operator.sub
          (Morph.Syntax.Expr.lit (Morph.Core.Value.int 0)) a',
        by simp [toExpr, ha]⟩
  | rawptr a iha => intro h; exact absurd h (by simp [safe])
  | inlineAsm a iha => intro h; exact absurd h (by simp [safe])

/-- The embedding refuses exactly what `safe` forbids. -/
theorem toExpr_refuses_unsafe : ∀ (e : Term), ¬ safe e → toExpr e = none := by
  intro e
  induction e with
  | val r d => intro h; simp [safe] at h
  | add a b iha ihb =>
      intro h
      simp only [safe] at h
      by_cases ha : safe a
      · by_cases hb : safe b
        · simp [ha, hb] at h
        · rw [toExpr]
          simp [ihb hb]
      · rw [toExpr]
        simp [iha ha]
  | mul a b iha ihb =>
      intro h
      simp only [safe] at h
      by_cases ha : safe a
      · by_cases hb : safe b
        · simp [ha, hb] at h
        · rw [toExpr]
          simp [ihb hb]
      · rw [toExpr]
        simp [iha ha]
  | sub a b iha ihb =>
      intro h
      simp only [safe] at h
      by_cases ha : safe a
      · by_cases hb : safe b
        · simp [ha, hb] at h
        · rw [toExpr]
          simp [ihb hb]
      · rw [toExpr]
        simp [iha ha]
  | neg a iha =>
      intro h
      simp only [safe] at h
      rw [toExpr]
      simp [iha h]
  | rawptr a iha => intro _; rfl
  | inlineAsm a iha => intro _; rfl

/-- **Refinement square.** Embedding factors through translation: an accepted
translation does not change the embedded program, because translation only
retags (which embedding erases) and preserves structure. Authority
operations embed to `none` on both sides. -/
theorem embed_translate_commute {target : Dialect} {e e' : Term}
    (h : translate target e = some e') : toExpr e = toExpr e' := by
  induction e generalizing e' with
  | val r d => simp [translate] at h; cases h; rfl
  | add a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .add a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp only [toExpr, iha ha, ihb hb]
  | mul a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .mul a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp only [toExpr, iha ha, ihb hb]
  | sub a b iha ihb =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          cases hb : translate target b with
          | none => simp [translate, ha, hb] at h
          | some b' =>
              have he' : e' = .sub a' b' := by simpa [translate, ha, hb] using h.symm
              subst he'
              simp only [toExpr, iha ha, ihb hb]
  | neg a iha =>
      cases ha : translate target a with
      | none => simp [translate, ha] at h
      | some a' =>
          have he' : e' = .neg a' := by simpa [translate, ha] using h.symm
          subst he'
          simp only [toExpr, iha ha]
  | rawptr a iha =>
      by_cases hp : permits target (.rawptr a) = true
      · cases ha : translate target a with
        | none => simp [translate, hp, ha] at h
        | some a' =>
            have he' : e' = .rawptr a' := by simpa [translate, hp, ha] using h.symm
            subst he'
            simp [toExpr]
      · simp [translate, hp] at h
  | inlineAsm a iha =>
      by_cases hp : permits target (.inlineAsm a) = true
      · cases ha : translate target a with
        | none => simp [translate, hp, ha] at h
        | some a' =>
            have he' : e' = .inlineAsm a' := by simpa [translate, hp, ha] using h.symm
            subst he'
            simp [toExpr]
      · simp [translate, hp] at h

/-- The bridge is exact: a term embeds iff it is safe. -/
theorem toExpr_iff_safe (e : Term) :
    (∃ e', toExpr e = some e') ↔ safe e := by
  constructor
  · rintro ⟨e', ht⟩
    refine Classical.byContradiction ?_
    intro hn
    rw [toExpr_refuses_unsafe e hn] at ht
    cases ht
  · intro h
    exact toExpr_safe_total e h

end Morph.Specs.DialectSemantics

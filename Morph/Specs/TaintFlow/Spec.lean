/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core

/-!
# Taint Tracking Across Dialect Boundaries (ADR-019, research loop 4)

SG-003 asked for taint tracking *across dialect boundaries*: what happens to a
security label when a program crosses from one dialect to another. The
existing `SecurityFlow` module does not answer this — its `NonInterference` is
stated over *labels* as though labels were program states, and its theorems
all have the form `h → h`.

This module states the property properly, in the form the literature uses:

- **Zdancewic & Myers (POPL 2001), Myers & Liskov (CSFW 2004), Zdancewic
  (TOPLAS 2003)**: robust declassification — the *decision* to downgrade must
  be made by code with sufficient integrity, otherwise an attacker who controls
  the decision controls the release.
- **Köpf et al. (CCS 2017/2021)**: nonmalleable information flow subsumes
  robust declassification and transparent endorsement; the first formulation of
  robustness as a 4-safety hyperproperty.
- **Costa, Köpf, Kolluri, Paverd, Russinovich et al. (arXiv:2505.23643, 2025)**,
  *Securing AI Agents with Information-Flow Control* — Fides. This is the
  closest work to Morph: it characterises **the class of properties enforceable
  by dynamic taint-tracking** for agent planners, and tracks confidentiality
  *and* integrity labels. Its conclusion for us: a taint label must survive
  every transformation the planner performs, including dialect projection.

## The model

* A two-point confidentiality lattice: `pub ⊑ sec`.
* Labelled expressions with an explicit `decl` (declassify) node. The taint of
  an expression is computed structurally; `ite` contributes an **implicit
  flow**, so the program counter's label is joined in — the reason a naive
  "check the sink" rule is unsound.
* Two **dialects**: `strict` (no declassification) and `permissive`.
  Translation between dialects either *rejects* a program or leaves it
  unchanged.
* An **authority** condition: a program counter that is not trusted (`pub`)
  may not have its declassifications carried into the strict dialect. This is
  robust declassification, with the pc's confidentiality label standing in for
  the integrity of the deciding context.

## Results (Lemmas.lean)

- `taint_preserved` — a successful translation preserves the taint label
  *exactly*. Translation can fail; it can never quietly downgrade.
- `reject_untrusted_decl` — **robustness**: an untrusted pc cannot smuggle a
  declassify into the strict dialect (`translate = none`).
- `no_decl_after_translation` — whatever *does* cross into the strict dialect
  is declassification-free.
- `flows_pub_without_decl` — **noninterference**: a program running at public
  pc that contains no declassify can only ever taint public.
- `flows_translation` — **SG-003**: typing survives the dialect boundary, so
  the noninterference argument is preserved across translation.
-/

namespace Morph.Specs.TaintFlow

/-! ## The confidentiality lattice -/

/-- Confidentiality labels: `pub` flows to `sec`, never back. -/
inductive Label where
  | pub | sec
  deriving Repr, DecidableEq, BEq

/-- The security order: information may flow from `a` to `b`. -/
def Label.le : Label → Label → Prop
  | .pub, .pub => True
  | .pub, .sec => True
  | .sec, .sec => True
  | .sec, .pub => False

instance instDecidableLe : Decidable (Label.le a b) :=
  match a, b with
  | .pub, .pub => isTrue trivial
  | .pub, .sec => isTrue trivial
  | .sec, .sec => isTrue trivial
  | .sec, .pub => isFalse (by simp [Label.le])

theorem le_refl (a : Label) : Label.le a a := by
  cases a <;> trivial

theorem le_trans {a b c : Label} (h₁ : Label.le a b) (h₂ : Label.le b c) :
    Label.le a c := by
  cases a <;> cases b <;> cases c <;> simp [Label.le] at h₁ h₂ ⊢

theorem le_antisymm {a b : Label} (h₁ : Label.le a b) (h₂ : Label.le b a) :
    a = b := by
  cases a <;> cases b <;> simp [Label.le] at h₁ h₂
  · rfl
  · rfl

/-- The join of two labels (least upper bound). -/
def Label.join (a b : Label) : Label :=
  match a, b with
  | .sec, _ => .sec
  | _, .sec => .sec
  | _, _ => .pub

theorem join_le_iff {a b c : Label} : Label.le (Label.join a b) c ↔
    Label.le a c ∧ Label.le b c := by
  cases a <;> cases b <;> cases c <;> simp [Label.le, Label.join]

theorem le_join_left (a b : Label) : Label.le a (Label.join a b) := by
  cases a <;> cases b <;> trivial

theorem le_join_right (a b : Label) : Label.le b (Label.join a b) := by
  cases a <;> cases b <;> trivial

/-! ## Labelled expressions -/

/-- Expressions, with an explicit `decl` node standing for declassification. -/
inductive TExpr where
  | lit
  | var (name : String)
  | add (a b : TExpr)
  | ite (c t f : TExpr)
  | decl (e : TExpr)
  deriving Repr

/-- Variable labels. -/
abbrev TEnv := String → Label

/-- The taint of an expression under an environment. `decl` erases the label;
`ite` contributes an implicit flow, which is why the program counter has to be
joined in below. -/
def taint (ρ : TEnv) : TExpr → Label
  | .lit => .pub
  | .var x => ρ x
  | .add a b => Label.join (taint ρ a) (taint ρ b)
  | .ite c t f => Label.join (Label.join (taint ρ c) (taint ρ t)) (taint ρ f)
  | .decl _e => .pub

/-- `NoDecl e`: the expression contains no declassification anywhere. -/
inductive NoDecl : TExpr → Prop where
  | lit : NoDecl .lit
  | var : NoDecl (.var x)
  | add : NoDecl a → NoDecl b → NoDecl (.add a b)
  | ite : NoDecl c → NoDecl t → NoDecl f → NoDecl (.ite c t f)

/-- `UsesDecl e`: the expression *does* declassify something. -/
inductive UsesDecl : TExpr → Prop where
  | decl : UsesDecl (.decl e)
  | add_l : UsesDecl a → UsesDecl (.add a b)
  | add_r : UsesDecl b → UsesDecl (.add a b)
  | ite_c : UsesDecl c → UsesDecl (.ite c t f)
  | ite_t : UsesDecl t → UsesDecl (.ite c t f)
  | ite_f : UsesDecl f → UsesDecl (.ite c t f)

/-! ## Dialects and the authority condition -/

/-- Morph has a `strict` dialect (declassification requires authority) and a
`permissive` one (declassification is available to anyone). -/
inductive Dialect where
  | strict | permissive
  deriving Repr, DecidableEq, BEq

/-- **Authority (robust declassification).** A program counter is trusted when
its label is `sec`; an untrusted (`pub`) pc may not introduce a
declassification when the target dialect is `strict`. Zdancewic's rule is
`I(pc) ⊑ auth(ℓ, ℓ′)`; here the pc's label stands in for the integrity of the
deciding context. -/
def Trusted (pc : Label) : Prop := pc = .sec

/-- A program counter is trusted exactly when it is not `pub`. -/
theorem trusted_iff (pc : Label) : Trusted pc ↔ pc = .sec := Iff.rfl

/-- Translate an expression between dialects. Translation never rewrites an
expression: it either returns it unchanged or *rejects* it, which is what makes
`taint_preserved` (below) a theorem rather than an approximation. -/
def translate (to : Dialect) (pc : Label) : TExpr → Option TExpr
  | .lit => some .lit
  | .var x => some (.var x)
  | .add a b =>
      match translate to pc a, translate to pc b with
      | some a', some b' => some (.add a' b')
      | _, _ => none
  | .ite c t f =>
      match translate to pc c, translate to pc t, translate to pc f with
      | some c', some t', some f' => some (.ite c' t' f')
      | _, _, _ => none
  | .decl e =>
      if to = .strict ∧ pc ≠ .sec then none
      else match translate to pc e with
        | some e' => some (.decl e')
        | none => none

end Morph.Specs.TaintFlow
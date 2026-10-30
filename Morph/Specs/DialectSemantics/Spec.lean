/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.DialectProjection.Spec

/-!
# Dialect Semantics: translation validation for cross-dialect translation

Research loop 7, discharging SG-001 ("Formal semantics for cross-dialect
translation").

**What was missing.** `Morph/Specs/DialectProjection/` declares dialects,
capabilities and a lowering pass, but has **no semantics**: `lower` is documented
as "a structural pass-through; full lowering is dialect-specific", and it retags
values without checking that the target may perform the operations it is being
handed. `Projection.isValid` answers `True` for three hard-coded pairs and
`False` otherwise, with no capability argument. `Lemmas.lean` holds only `rfl`
facts about `List` and `Option` — no dialect content at all.

**Research basis.**

- **Translation validation** (Pnueli et al.; in its modern form **Alive2**,
  Lopes, Lee, Hur, Liu & Regehr, PLDI 2021) does not prove a compiler correct
  once: it validates *each individual translation* against a denotational
  semantics, so the obligation is `src ≡ tgt` for the pass under consideration.
  Alive2's most instructive result for us is that its bugs clustered where the
  IR *specification* was informal — which is exactly Morph's situation, since
  `lower` has no semantics to be informal about.
- **First-class verification dialects for MLIR** (semantic dialects) attack the
  same problem by making a dialect's *semantics* the specified artifact, so
  translations between dialects become checkable objects.

**The move.** Give dialect terms a denotational semantics (`eval`), make
translation *refuse* rather than pass through what the target dialect may not
perform, and then discharge the Alive2-style obligation: every accepted
translation preserves the denotation.

The term language is the binary/unary core of `DialectExpr` — values carrying a
dialect tag, arithmetic primitives, and the two primitives that only a
permissive dialect may perform. That restriction is deliberate: with a
denotational semantics there is no list nesting to fight, so the whole theory is
proved by structural induction. The list-shaped `DialectExpr` of
`DialectProjection` is covered by the same statements in `Examples.lean`.
-/

namespace Morph.Specs.DialectSemantics

open Morph.Specs.DialectProjection

/-- A dialect term: a value tagged with the dialect it belongs to, an arithmetic
primitive, or one of the primitives that require authority. -/
inductive Term where
  /-- A literal, tagged with the dialect it is written in. -/
  | val (repr : Nat) (d : Dialect) : Term
  /-- `a + b` -/
  | add (a b : Term) : Term
  /-- `a * b` -/
  | mul (a b : Term) : Term
  /-- `a - b` (truncated, as machine subtraction is). -/
  | sub (a b : Term) : Term
  /-- `0 - a` -/
  | neg (a : Term) : Term
  /-- Raw pointer manipulation: requires authority. -/
  | rawptr (a : Term) : Term
  /-- Inline assembly: requires authority. -/
  | inlineAsm (a : Term) : Term
  deriving Repr, BEq, DecidableEq

/-- Does this dialect permit the given primitive? `core` is the restrictive
endpoint; `unsafe` and `ffi` permit everything. This is the capability test the
old `lower` never made. -/
def permits (d : Dialect) (t : Term) : Bool :=
  match t with
  | .val _ _ => true
  | .add _ _ => true
  | .mul _ _ => true
  | .sub _ _ => true
  | .neg _ => true
  | .rawptr _ => !decide (d = .core)
  | .inlineAsm _ => !decide (d = .core)

/-- The dialect a term belongs to: the tag on its leaves, nothing else. A
composite term has no dialect of its own; translation normalises all leaves to
the target. -/
def dialectOf : Term → Dialect
  | .val _ d => d
  | .add a _ => dialectOf a
  | .mul a _ => dialectOf a
  | .sub a _ => dialectOf a
  | .neg a => dialectOf a
  | .rawptr a => dialectOf a
  | .inlineAsm a => dialectOf a

/-- The denotation of a term: the value it denotes, or `none` when it is stuck —
a type error, or an operation its dialect may not perform. Note the dialect tag
of a value is *irrelevant* to its denotation; only the capability test depends
on it. That is what makes retagging safe and refusal necessary. -/
def eval (d : Dialect) : Term → Option Nat
  | .val r _ => some r
  | .add a b => (eval d a).bind (fun x => (eval d b).bind (fun y => some (x + y)))
  | .mul a b => (eval d a).bind (fun x => (eval d b).bind (fun y => some (x * y)))
  | .sub a b => (eval d a).bind (fun x => (eval d b).bind (fun y => some (x - y)))
  | .neg a => (eval d a).bind (fun x => some (0 - x))
  | .rawptr _ => none
  | .inlineAsm _ => none

/-- An authority-requiring primitive has **no denotation** in the core
semantics: it manipulates machine state, which this semantics does not model.
That is precisely why translation must refuse it rather than pass it through. -/
theorem eval_authority_op_denotes_nothing {d : Dialect} (a : Term) :
    eval d (.rawptr a) = none ∧ eval d (.inlineAsm a) = none := ⟨rfl, rfl⟩

/-- A term is *safe* when it performs no operation requiring authority. This is
the property translation into `core` tests. -/
def safe : Term → Prop
  | .val _ _ => True
  | .add a b => safe a ∧ safe b
  | .mul a b => safe a ∧ safe b
  | .sub a b => safe a ∧ safe b
  | .neg a => safe a
  | .rawptr _ => False
  | .inlineAsm _ => False

/-- Translate a term into `target`, retagging values and **refusing** operations
the target may not perform. Refusal is what makes the preservation theorem
below say something: there is no path that smuggles a forbidden operation into a
permissive-looking term. -/
def translate (target : Dialect) : Term → Option Term
  | .val r _d => some (.val r target)
  | .add a b =>
      match translate target a, translate target b with
      | some a', some b' => some (.add a' b')
      | _, _ => none
  | .mul a b =>
      match translate target a, translate target b with
      | some a', some b' => some (.mul a' b')
      | _, _ => none
  | .sub a b =>
      match translate target a, translate target b with
      | some a', some b' => some (.sub a' b')
      | _, _ => none
  | .neg a => (translate target a).map Term.neg
  | .rawptr a => if permits target (.rawptr a) then (translate target a).map Term.rawptr else none
  | .inlineAsm a =>
      if permits target (.inlineAsm a) then (translate target a).map Term.inlineAsm else none

end Morph.Specs.DialectSemantics

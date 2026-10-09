/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.MIR

/-!
# The borrow judgment (ADR-013, stage 1)

An Oxide-shaped formulation of borrow checking as a substructural typing
judgment over MIR (Weiss et al., *Oxide: The Essence of Rust*,
arXiv:1903.00982): places, loans, provenances, and one rule per MIR
instruction, with progress and preservation theorems.

**Stage-1 scope.** The judgment *checks* accesses against an outstanding
loan set; it does not yet *create* or *kill* loans — there is no reborrow
instruction in `MIR.Instr`, and loan-kill is NLL liveness work (ADR-013
non-goals). Consequently the transfer function is the identity on
`Provenances`, which is what makes stage-1 preservation provable: checking
never disturbs the invariant.

The executable half (`overlapsBool`, `noConflictingLoanBool`) is the
predicate a real checker evaluates; `noConflictingLoanBool_sound` proves the
checker sound: an "accept" verdict implies the judgment's premise holds.
-/

namespace Morph.Borrows

open Morph.MIR
open Morph.Core (Capability)

/-! ## Places -/

/-- A place: a path through the value graph. `base vid` is SSA register
`vid`; `deref p` is the location `p` points to. -/
inductive Place where
  | base  : ValId → Place
  | deref : Place → Place
  deriving Repr, BEq, DecidableEq

/-! ## Loans and provenances -/

/-- A loan: an outstanding borrow of a place at a capability, introduced at
some lifetime level (de Bruijn; stage 2 gives levels meaning). -/
structure Loan where
  place    : Place
  cap      : Capability
  lifetime : Nat
  deriving Repr, BEq, DecidableEq

/-- The set of outstanding loans at a program point. -/
abbrev Provenances : Type := List Loan

/-! ## Overlap (syntactic alias approximation) -/

/-- Two places overlap. This is the *syntactic* approximation of aliasing:
registers alias iff equal; `*p` and `*q` alias iff `p` and `q` alias; a
register and a dereference chain never overlap syntactically (resolving
`*p` to a heap cell is exactly the undecidable part — ADR-013
consequences). -/
def Overlaps : Place → Place → Prop
  | .base i,  .base j  => (i == j) = true
  | .base _,  .deref _ => False
  | .deref _, .base _  => False
  | .deref p, .deref q => Overlaps p q

/-- `Overlaps` is decidable (structural recursion on places). -/
instance overlapDecidable : (p q : Place) → Decidable (Overlaps p q)
  | .base i, .base j => inferInstanceAs (Decidable ((i == j) = true))
  | .base _, .deref _ => isFalse fun h => h
  | .deref _, .base _ => isFalse fun h => h
  | .deref p, .deref q =>
      match overlapDecidable p q with
      | isTrue h => isTrue h
      | isFalse h => isFalse fun hd => h hd

/-! ## Conflict -/

/-- A loan conflicts with an access at capability `cap` to place `p`:
the places overlap, and it is *not* the case that both the access is a
read (`cap = .val`) and the loan is shared (`loan.cap = .val`). So:
* a read access conflicts with any *mutable* loan; while
* a write access (`cap = .ref` / `.iso`) conflicts with *every* loan.
This is Rust's rule: mutable borrows exclude everything; shared borrows
exclude only mutable ones. Stated without `match` so the definition stays
reducible for tactics. -/
@[reducible]
def conflictWith (loan : Loan) (p : Place) (cap : Capability) : Prop :=
  Overlaps loan.place p ∧ ¬ (cap = .val ∧ loan.cap = .val)

/-- No loan in `π` conflicts with a `cap`-access to `p`. -/
def NoConflictingLoan (π : Provenances) (p : Place) (cap : Capability) : Prop :=
  ∀ l ∈ π, ¬ conflictWith l p cap

/-- No loan at all covers `p` (the write-exclusivity requirement). -/
def NoLoans (π : Provenances) (p : Place) : Prop :=
  ∀ l ∈ π, ¬ Overlaps l.place p

/-! ## The judgment -/

/-- `Borrows fenv π i π'`: instruction `i` checks in environment `fenv`
with outstanding loans `π`, producing `π'`. Stage 1: every rule keeps `π`
(check-only; loan creation/kill comes with stage-2 reborrows/NLL). -/
inductive Borrows : FullEnv → Provenances → Instr → Provenances → Prop where
  | const : ∀ fenv π dst v,
      Borrows fenv π (.const dst v) π
  | copy : ∀ fenv π dst src,
      Borrows fenv π (.copy dst src) π
  | unop : ∀ fenv π dst op src τ,
      Borrows fenv π (.unop dst op src τ) π
  | binop : ∀ fenv π dst op l r τ,
      Borrows fenv π (.binop dst op l r τ) π
  | load : ∀ fenv π dst loc cap,
      NoConflictingLoan π (.base loc) cap →
      Borrows fenv π (.load dst loc cap) π
  | store : ∀ fenv π loc src cap,
      NoLoans π (.base loc) →
      Borrows fenv π (.store loc src cap) π
  | alloc : ∀ fenv π dst cap τ,
      Borrows fenv π (.alloc dst cap τ) π
  | free : ∀ fenv π loc,
      NoLoans π (.base loc) →
      Borrows fenv π (.free loc) π
  | call : ∀ fenv π dst fn args,
      Borrows fenv π (.call dst fn args) π
  | phi : ∀ fenv π dst pred src,
      Borrows fenv π (.phi dst pred src) π

/-! ## The borrow invariant -/

/-- Stage-1 borrow invariant: the loan set has no exact duplicates.
The judgment's transfer never adds loans, so preservation holds because
checking cannot introduce a duplicate. -/
def WFBorrow (π : Provenances) : Prop :=
  ∀ l₁ ∈ π, ∀ l₂ ∈ π, l₁ ≠ l₂ →
    ¬ (l₁.place = l₂.place ∧ l₁.cap = l₂.cap ∧ l₁.lifetime = l₂.lifetime)

/-! ## Progress -/

/-- Pure instructions always check. -/
theorem borrow_progress_pure (fenv : FullEnv) (π : Provenances) (i : Instr)
    (h : match i with
         | .const .. | .copy .. | .unop .. | .binop .. | .alloc .. => True
         | _ => False) :
    ∃ π', Borrows fenv π i π' := by
  cases i with
  | const dst v => exact ⟨π, .const fenv π dst v⟩
  | copy dst src => exact ⟨π, .copy fenv π dst src⟩
  | unop dst op src τ => exact ⟨π, .unop fenv π dst op src τ⟩
  | binop dst op l r τ => exact ⟨π, .binop fenv π dst op l r τ⟩
  | alloc dst cap τ => exact ⟨π, .alloc fenv π dst cap τ⟩
  | load dst loc cap => exact h.elim
  | store loc src cap => exact h.elim
  | free loc => exact h.elim
  | call dst fn args => exact h.elim
  | phi dst pred src => exact h.elim

/-- A read checks iff no mutable loan conflicts — the progress direction
for `load`. -/
theorem borrow_progress_load (fenv : FullEnv) (π : Provenances) (dst loc : ValId)
    (h : NoConflictingLoan π (.base loc) .val) :
    ∃ π', Borrows fenv π (.load dst loc .val) π' :=
  ⟨π, .load fenv π dst loc .val h⟩

/-- A write checks iff the place is loan-free — the progress direction
for `store`. -/
theorem borrow_progress_store (fenv : FullEnv) (π : Provenances) (loc src : ValId)
    (h : NoLoans π (.base loc)) :
    ∃ π', Borrows fenv π (.store loc src .ref) π' :=
  ⟨π, .store fenv π loc src .ref h⟩

/-! ## Preservation -/

/-- Checking preserves the borrow invariant. Every rule's transfer is the
identity, so inversion collapses this to `WFBorrow π → WFBorrow π`. -/
theorem borrow_preservation (fenv : FullEnv) (π π' : Provenances) (i : Instr)
    (hinv : WFBorrow π) (hj : Borrows fenv π i π') :
    WFBorrow π' := by
  cases hj <;> exact hinv

/-! ## The executable checker -/

/-- Boolean overlap decision. -/
def overlapsBool : Place → Place → Bool
  | .base i,  .base j  => i == j
  | .base _,  .deref _ => false
  | .deref _, .base _  => false
  | .deref p, .deref q => overlapsBool p q

theorem overlapsBool_spec : ∀ p q : Place, overlapsBool p q = true ↔ Overlaps p q := by
  intro p q
  induction p generalizing q with
  | base i =>
      cases q with
      | base j => exact Iff.rfl
      | deref _ => simp [overlapsBool, Overlaps]
  | deref p ih =>
      cases q with
      | base _ => simp [overlapsBool, Overlaps]
      | deref q => exact ih q

/-- Structural soundness of the derived `BEq` on `Capability`. -/
theorem capabilityBEq_sound : ∀ a b : Capability, (a == b) = true → a = b := by
  intro a b h
  cases a <;> cases b <;> first
  | rfl
  | exact absurd h (by decide)

/-- Boolean conflict decision (the predicate a real checker evaluates):
overlap, and not (read access with a shared loan). -/
def conflictBool (loan : Loan) (p : Place) (cap : Capability) : Bool :=
  overlapsBool loan.place p && !(cap == .val && loan.cap == .val)

theorem conflictBool_spec : ∀ (l : Loan) (p : Place) (cap : Capability),
    conflictBool l p cap = true ↔ conflictWith l p cap := by
  intro l p cap
  constructor
  · intro h
    rw [conflictBool, Bool.and_eq_true] at h
    refine And.intro ((overlapsBool_spec l.place p).mp h.1) ?_
    intro hboth
    obtain ⟨he1, he2⟩ := hboth
    rw [he1, he2] at h
    have hv : (Capability.val == Capability.val) = true := by decide
    rw [hv] at h
    exact absurd h.2 (by decide)
  · intro hpair
    obtain ⟨hover, hne⟩ := hpair
    rw [conflictBool, (overlapsBool_spec l.place p).mpr hover]
    cases he1 : cap with
    | val =>
        cases he2 : l.cap with
        | val => exact absurd ⟨he1, he2⟩ hne
        | ref => decide
        | iso => decide
    | ref =>
        cases he2 : l.cap with
        | val => decide
        | ref => decide
        | iso => decide
    | iso =>
        cases he2 : l.cap with
        | val => decide
        | ref => decide
        | iso => decide

/-- Executable no-conflict check over a whole provenance set. -/
def noConflictingLoanBool (π : Provenances) (p : Place) (cap : Capability) : Bool :=
  π.all (fun l => !conflictBool l p cap)

/-- Checker soundness: an "accept" verdict means the judgment's premise
holds. (Completeness holds too, but soundness is the ADR-013 obligation.) -/
theorem noConflictingLoanBool_sound (π : Provenances) (p : Place) (cap : Capability)
    (h : noConflictingLoanBool π p cap = true) :
    NoConflictingLoan π p cap := by
  intro l hl hconf
  rw [noConflictingLoanBool, List.all_eq_true] at h
  have hall := h l hl
  have hno : conflictBool l p cap = false := by
    cases hz : conflictBool l p cap with
    | false => rfl
    | true => rw [hz] at hall; exact Bool.noConfusion hall
  rw [(conflictBool_spec l p cap).mpr hconf] at hno
  exact Bool.noConfusion hno

end Morph.Borrows

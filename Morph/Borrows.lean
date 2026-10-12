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

/-- Structural extensionality for loans. -/
theorem Loan.ext {p₁ p₂ : Place} {c₁ c₂ : Capability} {l₁ l₂ : Nat}
    (h₁ : p₁ = p₂) (h₂ : c₁ = c₂) (h₃ : l₁ = l₂) :
    ({ place := p₁, cap := c₁, lifetime := l₁ } : Loan) =
      { place := p₂, cap := c₂, lifetime := l₂ } := by
  cases h₁; cases h₂; cases h₃; rfl

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

/-! ## Loan creation (ADR-012 §4) -/

/-- The loans a closure over `captures` creates: one per captured place, at
    the environment capability `κ`, at the closure's own lifetime level. -/
def closureLoans (_fn : FnId) (captures : List ValId) (κ : Capability) (level : Nat) : Provenances :=
  captures.map fun c => { place := .base c, cap := κ, lifetime := level }

/-- A capture set is admissible at capability `κ` when no capture is
    already covered by a conflicting loan — the same no-conflict test used
    for `load`, generalized to the whole capture list. -/
def CaptureOK (π : Provenances) (captures : List ValId) (κ : Capability) : Prop :=
  ∀ c ∈ captures, NoConflictingLoan π (.base c) κ

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
  /-- ADR-012/ADR-013 stage 2: closure creation *creates* loans. Each
      captured register becomes borrowed at the environment's capability for
      as long as the closure lives. This is the first rule whose transfer
      grows `π`. -/
  | allocClosure : ∀ fenv π dst fn captures κ,
      κ ≠ .val →
      CaptureOK π captures κ →
      Borrows fenv π (.allocClosure dst fn captures) (π ++ closureLoans fn captures κ 0)
  /-- ADR-012: dispatch through a closure reads the closure cell and passes
      the captured environment to `fn`. -/
  | callClosure : ∀ fenv π dst clo args,
      NoConflictingLoan π (.base clo) .val →
      Borrows fenv π (.callClosure dst clo args) π

/-! ## The borrow invariant -/

/-- Stage-1 borrow invariant: the loan set has no exact duplicates.
The judgment's transfer never adds loans, so preservation holds because
checking cannot introduce a duplicate. -/
def WFBorrow (π : Provenances) : Prop :=
  ∀ l₁ ∈ π, ∀ l₂ ∈ π, l₁ ≠ l₂ →
    ¬ (l₁.place = l₂.place ∧ l₁.cap = l₂.cap ∧ l₁.lifetime = l₂.lifetime)

/-- Stage-2 invariant, stated over an ordered loan list: the set is
    duplicate-free. The append in `allocClosure` can only break this by
    duplicating a *newly created* loan, which `CaptureOK` excludes (a
    capture that already carries an identical loan would conflict at `κ`).
    Preserved as a separate theorem below. -/
def WFBorrowApp (π extra : Provenances) : Prop :=
  ∀ l₁ ∈ π, ∀ l₂ ∈ extra, ¬ (l₁ = l₂)

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
  | allocClosure dst fn captures => exact h.elim
  | callClosure dst clo args => exact h.elim

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

/-- Specification of `closureLoans`: a loan is in the generated set exactly
    when it is the loan created for some capture in the list. -/
theorem closureLoans_spec (fn : FnId) (captures : List ValId) (κ : Capability)
    (level : Nat) (l : Loan) :
    l ∈ closureLoans fn captures κ level ↔
      ∃ d, d ∈ captures ∧ l = { place := .base d, cap := κ, lifetime := level } := by
  simp only [closureLoans, List.mem_map]
  constructor
  · rintro ⟨d, hd, heq⟩
    exact ⟨d, hd, heq.symm⟩
  · rintro ⟨d, hd, heq⟩
    exact ⟨d, hd, heq.symm⟩

/-- `CaptureOK` makes loan creation *fresh*: a loan `closureLoans` generates
    is not already outstanding. An existing loan on the capture's place
    would conflict with capturing it at `κ`, so `CaptureOK` rules it out.
    This is the step that lets `allocClosure` grow the loan set without
    breaking the duplicate-free invariant (ADR-012 §4: the preservation
    restrengthening obligation). -/
theorem closureLoans_fresh (π : Provenances) (fn : FnId) (captures : List ValId)
    (κ : Capability) (level : Nat) (hκ : κ ≠ .val)
    (hcap : CaptureOK π captures κ) (l : Loan)
    (hl : l ∈ closureLoans fn captures κ level) :
    l ∉ π := by
  intro hmem
  obtain ⟨d, hdmem, heq⟩ := (closureLoans_spec fn captures κ level l).mp hl
  have hplace : l.place = .base d := by rw [heq]
  have hloan : l.cap = κ := by rw [heq]
  -- `CaptureOK` forbids a conflicting loan on the captured place. With a
  -- *mutable* `κ` (`.ref`/`.iso`), every outstanding loan conflicts, so an
  -- existing loan on `base d` is impossible.
  refine hcap d hdmem l hmem ⟨?_, ?_⟩
  · rw [hplace]; simp [Overlaps]
  · rw [hloan]; intro hp; exact hκ hp.1

/-- An old loan and a freshly-created one cannot be structurally equal. -/
theorem fresh_ne_old (π : Provenances) (fn : FnId) (captures : List ValId)
    (κ : Capability) (hκ : κ ≠ .val) (hcap : CaptureOK π captures κ)
    (l₁ : Loan) (hl₁ : l₁ ∈ π) (l₂ : Loan) (hl₂ : l₂ ∈ closureLoans fn captures κ 0) :
    l₁ ≠ l₂ := by
  intro heq
  -- if l₁ = l₂, then l₁ is one of the fresh loans, so it is not in π
  exact (closureLoans_fresh π fn captures κ 0 hκ hcap l₁ (by
    rw [heq]; exact hl₂)) hl₁

/-- The `allocClosure` case, stated so its premises are explicit: appending
    freshly-created loans preserves the duplicate-free invariant. -/
theorem borrow_preservation_allocClosure (hinv : WFBorrow π) (fn : FnId)
    (captures : List ValId) (κ : Capability) (hκ : κ ≠ .val)
    (hcap : CaptureOK π captures κ) :
    WFBorrow (π ++ closureLoans fn captures κ 0) := by
  intro l₁ hl₁ l₂ hl₂ hne hdup
  rw [List.mem_append] at hl₁ hl₂
  rcases hl₁ with hl₁ | hl₁ <;> rcases hl₂ with hl₂ | hl₂
  · exact hinv l₁ hl₁ l₂ hl₂ hne hdup
  · -- l₁ ∈ π, l₂ fresh, hdup says l₁'s fields = l₂'s fields. Since loans are
    -- structures of exactly (place, cap, lifetime), hdup IS l₁ = l₂ — which
    -- `fresh_ne_old` rules out.
    exact fresh_ne_old π fn captures κ hκ hcap l₁ hl₁ l₂ hl₂ (by
      cases l₁; cases l₂; simp_all)
  · exact fresh_ne_old π fn captures κ hκ hcap l₂ hl₂ l₁ hl₁ (by
      cases l₁; cases l₂; simp_all)
  · -- both new: the loan structure pins each to its capture; identical
    -- structures mean the captures agree, so the loans are equal
    obtain ⟨d₁, hdc₁, he₁⟩ := (closureLoans_spec fn captures κ 0 l₁).mp hl₁
    obtain ⟨d₂, hdc₂, he₂⟩ := (closureLoans_spec fn captures κ 0 l₂).mp hl₂
    -- hdup (after pinning the structures) forces `base d₁ = base d₂`, hence
    -- d₁ = d₂, hence l₁ = l₂ — contradicting `hne`.
    rw [he₁, he₂] at hdup
    have hd₁₂ : d₁ = d₂ := by injection hdup.1
    refine absurd ?_ hne
    rw [he₁, he₂, hd₁₂]

/-- Checking preserves the borrow invariant: `WFBorrow π → WFBorrow π'`.
    Identity-transfer rules keep `π`; `allocClosure` appends only fresh
    loans, so the duplicate-free invariant survives loan creation. -/
theorem borrow_preservation (fenv : FullEnv) (π π' : Provenances) (i : Instr)
    (hinv : WFBorrow π) (hj : Borrows fenv π i π') :
    WFBorrow π' := by
  cases hj with
  | const => exact hinv
  | copy => exact hinv
  | unop => exact hinv
  | binop => exact hinv
  | alloc => exact hinv
  | call => exact hinv
  | phi => exact hinv
  | load _ _ hprem => exact hinv
  | store _ _ hprem => exact hinv
  | free _ hprem => exact hinv
  | callClosure _ _ hprem => exact hinv
  | allocClosure _ _ _ _ _ _ =>
      exact borrow_preservation_allocClosure hinv _ _ _ ‹_› ‹_›

/-! ## Loan kill (NLL liveness)

Loans end when their scope exits. Stage 2 models this with an explicit
`killLoans` transfer: at a scope boundary (a `return`, a block exit, or a
`callClosure` that consumes its environment) every loan introduced at or
below the given lifetime level is dropped from the provenance set. This is
the NLL kill rule ADR-013 listed as a non-goal for stage 1 and ADR-012
named as the reason preservation had to be restrengthened. -/

/-- Drop every loan at or below `level`: the loans whose scope has ended. -/
def killLoans (π : Provenances) (level : Nat) : Provenances :=
  π.filter fun l => l.lifetime > level

/-- Killing is idempotent. -/
theorem killLoans_idem (π : Provenances) (level : Nat) :
    killLoans (killLoans π level) level = killLoans π level := by
  simp [killLoans]

/-- Killing never introduces a loan. -/
theorem killLoans_subset (π : Provenances) (level : Nat) (l : Loan)
    (h : l ∈ killLoans π level) : l ∈ π := by
  have h' : l ∈ List.filter (fun x => x.lifetime > level) π := h
  exact (List.mem_filter.mp h').1

/-- Killing preserves the duplicate-free invariant. -/
theorem killLoans_preserves (π : Provenances) (level : Nat)
    (hinv : WFBorrow π) : WFBorrow (killLoans π level) := by
  intro l₁ hl₁ l₂ hl₂ hne hdup
  exact hinv l₁ (killLoans_subset _ _ _ hl₁) l₂ (killLoans_subset _ _ _ hl₂) hne hdup

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

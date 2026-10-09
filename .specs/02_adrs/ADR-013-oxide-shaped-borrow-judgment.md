# ADR-013: Oxide-Shaped Borrow Judgment for MIR Stage 2

## Status
**Proposed** (Loop 9, research program). Supersedes the withdrawn ADR-013
mention in the Loop 1 follow-up notes (no file ever existed under that number;
the `LinCtx.merge` operator it would have specified was deleted in ADR-014
stage 2).

## Context

ADR-011 places ownership checking in the MIR pipeline (stage 2) and Loop 6
refined its correctness theorem to be Oxide-shaped: progress + preservation on
a typing judgment, not raw dataflow correctness. This ADR specifies that
judgment.

The design constraint from Oxide (arXiv:1903.00982): borrow checking is a
**substructural typing judgment** that *automatically computes* lifetime /
provenance information through the same progress-and-preservation proof
architecture Morph already uses for `HasType` and `HasTypeS`.

The MIR CFG (Loop 6, `Morph/MIR.lean`) is the *input* — the judgment
consumes MIR and produces accept/reject decisions with provenances.

## Decision

### 1. Places, Loans, and Provenances

```lean
/-- A place: a path through the value graph.
    `Place.base vid` is an SSA value; `Place.deref p` is `*p`. -/
inductive Place where
  | base   : ValId → Place
  | deref  : Place → Place

/-- A loan: a borrow of a place with a capability. -/
structure Loan where
  place    : Place
  cap      : Capability
  lifetime : Nat   -- de Bruijn level of the introducing scope

/-- The provenance set: which loans are live at a program point. -/
abbrev Provenances : Type := List Loan
```

### 2. The Borrow Judgment

```lean
/-- MIR borrow checking judgment: `Borrows fenv provenances instr provenances'`
    reads `instr` in `provenances` and produces `provenances'`.
    This is the transfer function of the dataflow analysis, but it is
    presented as a typing judgment (one rule per instruction). -/
inductive Borrows : FullEnv → Provenances → Instr → Provenances → Prop where
  | const  : ∀ fenv π v dst,
      Borrows fenv π (.const dst v) π
  | copy   : ∀ fenv π dst src,
      Borrows fenv π (.copy dst src) π
  -- …every pure instruction passes through…
  | alloc  : ∀ fenv π dst cap τ,
      Borrows fenv π (.alloc dst cap τ) π   -- new value, no loan
  | load   : ∀ fenv π dst loc cap π',
      -- reading is safe if no conflicting mutable loan is outstanding
      NoConflictingLoan π (Place.base loc) .val →
      Borrows fenv π (.load dst loc cap) π'
  | store  : ∀ fenv π loc src cap π',
      -- writing is safe if no conflicting loan (read or write) is outstanding
      NoConflictingLoan π (Place.base loc) .val →
      NoConflictingLoan π (Place.base loc) .ref →
      Borrows fenv π (.store loc src cap) π'
  | free   : ∀ fenv π loc π',
      -- freeing is safe if no loan of any kind is outstanding
      NoLoans π (Place.base loc) →
      Borrows fenv π (.free loc) π'
```

### 3. No-Conflict Predicates

```lean
/-- No loan in `π` conflicts with accessing `place` at capability `cap`. -/
def NoConflictingLoan (π : Provenances) (place : Place) (cap : Capability) : Prop :=
  ∀ loan ∈ π, ¬Overlaps loan.place place ∧ ¬StrongerThan loan.cap cap

/-- No loan at all for this place. -/
def NoLoans (π : Provenances) (place : Place) : Prop :=
  ∀ loan ∈ π, ¬Overlaps loan.place place

/-- Two places overlap: same base, or one is a dereference chain of the other. -/
def Overlaps : Place → Place → Prop
```

### 4. Progress and Preservation

```lean
theorem borrow_progress : ∀ fenv π i,
    (∀ v, fenv.env v ≠ none) →  -- all registers defined
    ∃ π', Borrows fenv π i π'

theorem borrow_preservation : ∀ fenv π i π',
    Borrows fenv π i π' →
    -- executing the instruction preserves the borrow invariant
    WFBorrowState π'  -- no duplicate loans, all lifetimes valid, etc.
```

These are the **Oxide-shaped** correctness theorems: the borrow judgment has
progress (every instruction can be checked) and preservation (checking
preserves the borrow invariant).

### 5. What this does NOT cover

- **Region polymorphism**: Oxide's lifetimes are de Bruijn levels; we do not
  yet handle higher-order regions (`for<'a> fn(&'a T) -> &'a T`).
- **Two-phase borrows**: immediate re-borrowing after a mutable borrow is
  not modeled.
- **Drop elaboration**: `Drop` glue for nested owned values.

## Consequences

### Positive
- Borrow checking becomes a **theorem** about a **judgment**, not a lemma
  about a **dataflow fixpoint**. This is the same proof architecture as
  `HasType`/`HasTypeS` and reuses the existing prover expertise.
- The `NoConflictingLoan` predicate is **executable** — it is the predicate
  the Rust borrow checker evaluates. Proving it sound means the checker is
  sound.
- Stage 2's `lowering_correct` and `borrow_preservation` compose into the
  end-to-end theorem from ADR-011.

### Negative
- The `Overlaps` predicate requires an alias analysis, which in general is
  undecidable; we will use a syntactic (place-path) approximation.
- Loan set operations (add, remove, intersect) need decidability proofs.

## References
- Weiss et al. — *Oxide: The Essence of Rust* (arXiv:1903.00982).
- Jung et al. — *RustBelt* (POPL 2018) — the Iris-based semantic model.
- Matsakis — *Polonius* — the Datalog formulation of NLL.
- ADR-011 — the MIR pipeline this judgment plugs into.
- ADR-010 — the capability system and store model.

## Date
2026-09-19

## Author
Wyatt (with Nexus research program, Loop 9)

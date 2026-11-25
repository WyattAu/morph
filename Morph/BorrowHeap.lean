/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Borrows
import Morph.Memory

/-!
# D2 bridge: borrow provenances to heaps (S7)

The S7 mandate: build the D2 bridge — a `heapOf` projection from
`Borrows.lean` provenances to `Memory.lean` heaps — on the D-9
provisional default (supersede: executable `Memory.lean` is
authoritative, `Specs/MemoryModel` is cited as requirements only and is
*not* bridged; its 34 theorems stay proved-apart).

## Fragment (predicates before proofs, pins before theorems)

`heapFragment`: every loan is over a bare register (`.base`). A
`.deref` loan is outside the fragment: resolving `*p` needs a pointer
decoded out of `MemByte` contents, which is exactly the undecidable
part `Morph.Borrows` names in its `Overlaps` docstring. Refusal is
pinned in `Morph.Tests.BorrowHeap`, per the C8 discipline.

## Projection

`heapOf π`: `none` outside the fragment; otherwise one allocated
size-1 `undef` block per distinct borrowed register, with the block id
naming the register. Distinct registers map to distinct blocks and two
loans on one place share its block — reflecting the syntactic
no-aliasing (`Overlaps` on `.base` places is register equality). This
faithfulness is the content S8's agreement lemma (`wfBorrow_heapSafe`)
will use.

`ρ`-style resolution of registers against a *live* heap (an address
map consulted during evaluation) is deferred: it needs the same
byte-level pointer decoding as `deref`, plus D-8-adjacent evaluator
detail. Named future work, not silent omission.

## Stage-1 note

`WFBorrow` is variance-free (identity transfer; only `allocClosure`
grows the set, with freshness). S7 states the bridge over it without
needing it; S8 proves the agreement.
-/

namespace Morph.BorrowHeap

open Morph.Borrows
open Morph.MIR (ValId)

/-! ## Fragment: base-place loans only -/

/-- The D2 fragment predicate (executable): every outstanding loan is
over a bare register. -/
def heapFragment (π : Provenances) : Bool :=
  π.all fun l => match l.place with
    | .base _ => true
    | .deref _ => false

/-- Equation form, for rewriting under `List.all_eq_true`. -/
theorem heapFragment_all (π : Provenances) :
    heapFragment π = π.all fun l => match l.place with
      | .base _ => true
      | .deref _ => false := rfl

/-- The registers a provenance set borrows. -/
def basePlaces (π : Provenances) : List ValId :=
  π.filterMap fun l => match l.place with
    | .base v => some v
    | .deref _ => none

/-! ## Projection: canonical heap over the borrowed registers -/

/-- The D2 projection. Outside the fragment: `none`. Inside: one
allocated size-1 `undef` block per distinct borrowed register, block id
naming the register, cursor past the largest register. -/
def heapOf (π : Provenances) : Option Memory :=
  if heapFragment π then
    let places := (basePlaces π).eraseDups
    some { blocks := places.map (fun v => ({ id := v }, Block.make { id := v } 1 1)),
           nextBlockId := places.foldl Nat.max 0 + 1 }
  else none

/-! ## Total on the fragment, refusal outside it -/

/-- Inside the fragment the projection always produces a heap. -/
theorem heapOf_some_of_fragment_true {π : Provenances}
    (hf : heapFragment π = true) : ∃ h, heapOf π = some h := by
  unfold heapOf
  rw [if_pos hf]
  exact ⟨_, rfl⟩

/-- A `deref` loan anywhere in the set takes the whole set out of the
fragment — the refusal direction. -/
theorem fragment_false_of_mem_deref {π : Provenances} {l : Loan} {p : Place}
    (hmem : l ∈ π) (hplace : l.place = .deref p) :
    heapFragment π = false := by
  cases hb : heapFragment π with
  | true =>
    have h' : π.all (fun l => match l.place with
        | .base _ => true
        | .deref _ => false) = true := by
      rw [← heapFragment_all]; exact hb
    have hall := (List.all_eq_true.mp h') l hmem
    simp [hplace] at hall
  | false => rfl

/-- Outside the fragment the projection refuses. -/
theorem heapOf_none_of_fragment_false {π : Provenances}
    (h : heapFragment π = false) : heapOf π = none := by
  simp [heapOf, h]

/-- Combined refusal: a `deref` loan means no heap. -/
theorem heapOf_is_none_of_deref {π : Provenances} {l : Loan} {p : Place}
    (hmem : l ∈ π) (hplace : l.place = .deref p) :
    heapOf π = none :=
  heapOf_none_of_fragment_false (fragment_false_of_mem_deref hmem hplace)

end Morph.BorrowHeap

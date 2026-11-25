/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.BorrowHeap

/-!
# D2 bridge pins (S7)

Success case plus refusal/divergence cases, mirroring the C8 pins.
`heapOf` projects borrow provenances to canonical heaps: one allocated
block per distinct borrowed register, block id naming the register.
A `deref` loan anywhere refuses the whole set (out of fragment).
The `HeapSafe` pins preview S8's agreement lemma (`wfBorrow_heapSafe`);
the general proof comes next sprint.
-/

open Morph
open Morph.BorrowHeap
open Morph.Borrows

namespace Morph.Tests.BorrowHeap

/-- A shared loan on register 1. -/
def loanShared1 : Loan := ⟨.base 1, .val, 0⟩

/-- A mutable loan on register 1 — same place, different capability. -/
def loanMut1 : Loan := ⟨.base 1, .ref, 0⟩

/-- A shared loan on register 2 — disjoint from register 1. -/
def loanShared2 : Loan := ⟨.base 2, .val, 0⟩

/-- A loan through a dereference — outside the fragment. -/
def loanDeref : Loan := ⟨.deref (.base 1), .val, 0⟩

/-! ## Success: projection produces a heap -/

/-- A single borrowed register projects to one block. -/
example : ((heapOf [loanShared1]).map fun m => m.blocks.length) = some 1 := by
  rfl

/-- The block id names the register, cursor past it. -/
example : ((heapOf [loanShared1]).map fun m => m.nextBlockId) = some 2 := by
  rfl

/-! ## The aliasing story: one place, one block -/

/-- Shared and mutable loans on the *same* place share its block —
the projection reflects syntactic no-aliasing instead of
double-counting the region. -/
example : ((heapOf [loanShared1, loanMut1]).map fun m => m.blocks.length)
    = some 1 := by
  rfl

/-- Disjoint places get disjoint blocks. -/
example : ((heapOf [loanShared1, loanShared2]).map fun m => m.blocks.length)
    = some 2 := by
  rfl

/-! ## Refusal: `deref` is out of fragment -/

/-- A dereference loan refuses the whole set — resolving `*p` needs
pointer bytes decoded, which the fragment excludes. -/
example : heapOf [loanDeref] = none := by
  rfl

/-- ...even beside in-fragment loans. -/
example : heapOf [loanShared1, loanDeref] = none := by
  rfl

/-! ## Boundary: empty set -/

/-- No loans, no blocks — still a heap. -/
example : ((heapOf []).map fun m => m.blocks.length) = some 0 := by
  rfl

/-! ## S8 preview: projected heaps are `HeapSafe` -/

/-- The single-block projection satisfies the whole S5/S6 predicate. -/
example : ((heapOf [loanShared1]).map fun m => decide (Memory.HeapSafe m))
    = some true := by
  rfl

/-- ...and so does the two-block projection. -/
example : ((heapOf [loanShared1, loanShared2]).map fun m =>
    decide (Memory.HeapSafe m)) = some true := by
  rfl

end Morph.Tests.BorrowHeap

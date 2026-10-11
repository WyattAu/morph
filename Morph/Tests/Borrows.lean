/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Borrows

/-!
# Tests for the borrow judgment (ADR-013, stage 1)

Concrete instances exercising `Morph.Borrows`:

* `Overlaps` on registers and dereference chains;
* the conflict matrix: shared-loan + read = accept, mutable-loan + read =
  reject, any-loan + write = reject, disjoint places = accept;
* the `Borrows` judgment accepting a `load` under a shared loan and
  rejecting a `store` under any outstanding loan;
* `WFBorrow` on concrete loan sets and `borrow_preservation`;
* the executable checker agreeing with the judgment via
  `noConflictingLoanBool_sound`.
-/

namespace Morph.Tests.Borrows

open Morph.Borrows
open Morph.MIR
open Morph.Core (Capability Value Typ)

/-! ## Overlap -/

-- registers alias iff equal
example : Overlaps (.base 1) (.base 1) := by decide
example : ¬ Overlaps (.base 1) (.base 2) := by decide

-- dereference chains overlap iff their spines overlap
example : Overlaps (.deref (.base 1)) (.deref (.base 1)) := by decide
example : ¬ Overlaps (.deref (.base 1)) (.deref (.base 2)) := by decide

-- a register and a dereference chain never overlap syntactically
example : ¬ Overlaps (.base 1) (.deref (.base 1)) := by decide

-- the boolean decision agrees on concrete places
example : overlapsBool (.deref (.base 3)) (.deref (.base 3)) = true := by decide
example : overlapsBool (.base 1) (.base 2) = false := by decide

/-! ## Conflict matrix -/

/-- A shared (`.val`) loan on register 1. -/
def sharedLoan : Loan := ⟨.base 1, .val, 0⟩

/-- A mutable (`.ref`) loan on register 1. -/
def mutLoan : Loan := ⟨.base 1, .ref, 0⟩

/-- A default loan, for `headD`. -/
def defaultLoan : Loan := ⟨.base 99, .val, 0⟩

-- read access under a shared loan: no conflict
example : ¬ conflictWith sharedLoan (.base 1) .val := by
  intro h
  exact h.2 ⟨rfl, rfl⟩

-- read access under a mutable loan: conflict
example : conflictWith mutLoan (.base 1) .val :=
  ⟨by decide, fun hb => Capability.noConfusion hb.2⟩

-- write access under any loan: conflict
example : conflictWith sharedLoan (.base 1) .ref :=
  ⟨by decide, fun h => Capability.noConfusion h.1⟩
example : conflictWith mutLoan (.base 1) .ref :=
  ⟨by decide, fun h => Capability.noConfusion h.1⟩

-- disjoint places never conflict
example : ¬ conflictWith mutLoan (.base 2) .ref := by
  intro h
  have h1 : Overlaps (.base 1) (.base 2) := h.1
  exact absurd h1 (by decide)

-- the boolean checker agrees with the matrix
example : conflictBool sharedLoan (.base 1) .val = false := by decide
example : conflictBool mutLoan (.base 1) .val = true := by decide
example : conflictBool mutLoan (.base 1) .ref = true := by decide
example : conflictBool mutLoan (.base 2) .val = false := by decide

/-! ## The judgment -/

/-- Empty environment for the checking tests (the judgment ignores it in
stage 1). -/
def fenv0 : FullEnv := ⟨fun _ => none, Store.empty⟩

/-- A read under a shared loan on the same place has no conflict. -/
theorem noConflictSharedBase1 : NoConflictingLoan [sharedLoan] (.base 1) .val := by
  intro l hl hconf
  simp only [List.mem_cons] at hl
  cases hl with
  | inl heq => rw [heq] at hconf; exact hconf.2 ⟨rfl, rfl⟩
  | inr hnil => exact absurd hnil (by simp)

-- a load under a shared loan checks
example : Borrows fenv0 [sharedLoan] (.load 2 1 .val) [sharedLoan] :=
  .load fenv0 [sharedLoan] 2 1 .val noConflictSharedBase1

-- a store under an outstanding loan on the same place does not check
example : ¬ Borrows fenv0 [sharedLoan] (.store 1 2 .ref) [sharedLoan] := by
  intro h
  cases h with
  | store _ _ _ hprem =>
      exact hprem sharedLoan (by simp [sharedLoan]) (by decide)

-- a store on a disjoint place checks
example : Borrows fenv0 [sharedLoan] (.store 5 2 .ref) [sharedLoan] :=
  .store fenv0 [sharedLoan] 5 2 .ref (by
    intro l hl hover
    simp only [List.mem_cons] at hl
    cases hl with
    | inl heq => rw [heq] at hover; exact absurd hover (by decide)
    | inr hnil => exact absurd hnil (by simp))

-- pure instructions always check
example : Borrows fenv0 [] (.const 0 (.int 42)) [] := .const fenv0 [] 0 (.int 42)
example : Borrows fenv0 [] (.binop 2 .add 0 1 Typ.intType) [] :=
  .binop fenv0 [] 2 .add 0 1 Typ.intType

/-! ## WF and preservation on concrete loan sets -/

-- two loans on the same place but different capabilities are WF
example : WFBorrow [sharedLoan, mutLoan] := by
  intro l₁ h₁ l₂ h₂ hne hdup
  simp at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    first
    | exact absurd rfl hne
    | exact absurd hdup.2.1 (by decide)

-- checking the load preserves WF (transfer is identity in stage 1)
example : WFBorrow [sharedLoan] :=
  borrow_preservation fenv0 [sharedLoan] [sharedLoan] (.load 2 1 .val)
    (by
      intro l₁ h₁ l₂ h₂ hne _
      simp at h₁ h₂
      rcases h₁ with rfl <;> rcases h₂ with rfl
      exact absurd rfl hne)
    (.load fenv0 [sharedLoan] 2 1 .val noConflictSharedBase1)

/-! ## Executable checker soundness -/

-- the checker accepts a read under a shared loan, so the premise holds
example : NoConflictingLoan [sharedLoan] (.base 1) .val :=
  noConflictingLoanBool_sound [sharedLoan] (.base 1) .val (by decide)

/-! ## Loan creation (ADR-012 §4, ADR-013 stage 2) -/

/-- `closureLoans` creates one loan per capture, at the given capability. -/
example : closureLoans "f" [0, 1] .ref 0
    = [⟨.base 0, .ref, 0⟩, ⟨.base 1, .ref, 0⟩] := by
  decide

example : (closureLoans "f" [3] .iso 2).length = 1 := by decide

/-- No captures means no loans. -/
example : closureLoans "f" [] .ref 0 = [] := by decide

/-- A closure over a borrowed register creates a *different* loan (the
    capability differs), so it is not a duplicate of the existing one. -/
example : closureLoans "f" [1] .ref 0 = [mutLoan] := by
  decide

example : closureLoans "f" [1] .ref 0 ≠ [sharedLoan] := by
  decide

/-! ### Preservation under loan creation -/

/-- `CaptureOK` holds for capturing register 1 by reference when only a
    *shared* loan is outstanding (a mutable capture would conflict, a
    mutable loan is not present). -/
example : CaptureOK [sharedLoan] [1] .val := by
  intro c hc
  have : c = 1 := by simp at hc; exact hc
  subst this
  intro l hl
  have : l = sharedLoan := by simp at hl; exact hl
  subst this
  -- a shared loan does NOT conflict with a shared (`.val`) capture:
  -- this is the `read under shared loan` case from the matrix.
  show ¬ conflictWith sharedLoan (.base 1) .val
  intro hcontra
  exact hcontra.2 ⟨rfl, by simp [sharedLoan]⟩

/-- Appending freshly created loans keeps the invariant duplicate-free:
    the old shared loan and the new loan are distinct. -/
example : WFBorrow (([sharedLoan] : Provenances) ++ closureLoans "f" [2] .ref 0) := by
  apply borrow_preservation_allocClosure (π := [sharedLoan])
  · intro l₁ _ l₂ _ hne _
    cases l₁
    cases l₂
    simp_all
  · intro h; cases h
  · -- capturing register 2 conflicts with nothing (the shared loan is on 1)
    intro c hc
    have hc' : c = 2 := by simp at hc; exact hc
    subst hc'
    intro l hl
    have hl' : l = sharedLoan := by simp at hl; exact hl
    subst hl'
    show ¬ (Overlaps sharedLoan.place (.base 2) ∧
        ¬ (Capability.ref = Capability.val ∧ sharedLoan.cap = Capability.val))
    intro hcontra
    exact absurd hcontra.1 (by decide)

/-- The allocClosure rule itself checks with an empty loan set. -/
example : ∃ π', Borrows fenv0 [] (Instr.allocClosure 0 "f" [1, 2]) π' := by
  refine ⟨closureLoans "f" [1, 2] .ref 0, ?_⟩
  apply Borrows.allocClosure fenv0 [] 0 "f" [1, 2] .ref
  · intro h; cases h
  · intro c hc
    intro l hl
    simp at hl

end Morph.Tests.Borrows

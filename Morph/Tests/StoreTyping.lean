/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.TypeSystem.StoreTyping
import Morph.Semantics

/-!
# Tests for the store-typing layer (Phase 1d)

Concrete instantiations of `HasTypeS` / `StoreInv` and the memory-safety
theorems of `Morph.Specs.TypeSystem.StoreTyping`:

* an allocated location can be loaded, written and freed (no stuck heap op);
* freeing removes the location from the store typing, so no well-typed
  expression can dereference it afterwards (no use-after-free);
* progress and preservation really go through the three store-carrying step
  rules.
-/

namespace Morph.Tests.StoreTyping

open Morph
open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Morph.Specs.TypeSystem

/-! ## A concrete store: location `0` holds the integer `7` -/

/-- A store with a single allocated cell: location `0` holds the integer `7`.
    (This is exactly `(Store.alloc Store.empty .intType (.int 7)).1`.) -/
def σ₀ : Store :=
  { heap := fun l => if l = 0 then some (.intType, .int 7) else none
    nextLoc := 1
    freed := [] }

/-- A store typing declaring location `0` as an `iso` reference to an `int`. -/
def Δ₀ : StoreTyp := fun l => if l = 0 then some (.refType .iso .intType) else none

private theorem heap₀ : σ₀.heap 0 = some (.intType, .int 7) := by
  simp [σ₀]

private theorem heap₀_none {l : Loc} (h : l ≠ 0) : σ₀.heap l = none := by
  simp [σ₀, h]

private theorem pointee₀ : pointeeTy Δ₀ 0 = some .intType := by
  simp [Δ₀, pointeeTy, pointeeOf]

private theorem decl₀ : Δ₀ 0 = some (.refType .iso .intType) := by
  simp [Δ₀]

private theorem decl₀_none {l : Loc} (h : l ≠ 0) : Δ₀ l = none := by
  simp [Δ₀, h]

private theorem pointee₀_none {l : Loc} (h : l ≠ 0) : pointeeTy Δ₀ l = none := by
  simp [Δ₀, h, pointeeTy]

/-- `σ₀` satisfies the store invariant under `Δ₀`: allocated ⇒ declared and
    typed, and declared ⇒ allocated. -/
theorem σ₀_typed : StoreInv σ₀ Δ₀ := by
  constructor
  · intro loc τ v h
    by_cases hl : loc = 0
    · subst hl
      rw [heap₀] at h
      injection h with h1
      rcases h1 with ⟨rfl, rfl⟩
      exact ⟨pointee₀, by simp [σ₀], ValueType.int _ _⟩
    · rw [heap₀_none hl] at h
      simp at h
  · intro loc τ hpt
    by_cases hl : loc = 0
    · subst hl
      have hτ : τ = .intType := Option.some.inj (hpt.symm.trans pointee₀)
      subst hτ
      exact ⟨.int 7, heap₀⟩
    · rw [pointee₀_none hl] at hpt
      simp at hpt

/-! ## The heap operations are never stuck -/

example : ∃ v, Store.load σ₀ 0 = some (.intType, v) := load_ok σ₀_typed decl₀

example : ∃ σ', Store.store σ₀ 0 (.int 42) .intType = some σ' :=
  store_ok σ₀_typed decl₀

example : ∃ σ', Store.free σ₀ 0 = some σ' :=
  free_ok σ₀_typed decl₀

/-- A well-typed load of location `0` takes a step. -/
example : ∃ σ' e', Step σ₀ (.refLoad (.lit (.loc 0))) σ' e' := by
  exact safety_load_not_stuck (τ := .intType) σ₀_typed
    (.refLoad _ _ _ _ _ _ decl₀)

/-- A well-typed store into location `0` takes a step. -/
example : ∃ σ' e', Step σ₀ (.refStore (.lit (.loc 0)) (.lit (.int 3)) .intType) σ' e' := by
  exact safety_store_not_stuck σ₀_typed
    (.refStore _ _ _ _ _ _ _ decl₀ (ValueType.int _ _) (by intro h; cases h))

/-- A well-typed free of location `0` takes a step. -/
example : ∃ σ' e', Step σ₀ (.refFree (.lit (.loc 0))) σ' e' :=
  safety_free_not_stuck σ₀_typed (.refFree _ _ _ _ _ decl₀)

/-- The load really reads the value out of the store. -/
example : Step σ₀ (.refLoad (.lit (.loc 0))) σ₀ (.lit (.int 7)) :=
  Step.ref_load_done σ₀ 0 .intType (.int 7)
    (by rw [Store.load, if_neg (by simp [σ₀]), heap₀])

/-! ## Freeing a location removes it from the store typing -/

/-- Freeing location `0` preserves the invariant under the erased store typing,
    records the location as freed, and the erased store typing no longer declares
    it. -/
example : ∃ σ', StoreInv σ' (StoreTyp.erase Δ₀ 0) ∧ (StoreTyp.erase Δ₀ 0) 0 = none := by
  obtain ⟨σ', hfree⟩ := free_ok σ₀_typed decl₀
  obtain ⟨_, _, _⟩ := free_invalidates_typed σ₀_typed.1 decl₀ hfree
  exact ⟨σ', free_invalidates_inv σ₀_typed decl₀ hfree, StoreTyp.erase_eq _ _⟩

/-- Preservation along the freeing step: the result is typable under the erased
    store typing. -/
example : ∃ σ', ∃ Δ', StoreInv σ' Δ' ∧ (StoreTyp.erase Δ₀ 0) 0 = none
    ∧ HasTypeS Δ' [] [] (.lit .unit) .unitType := by
  obtain ⟨σ', hfree⟩ := free_ok σ₀_typed decl₀
  obtain ⟨Δ', hInv, hT⟩ :=
    preservationS σ₀_typed (.refFree _ _ _ _ _ decl₀) (Step.ref_free_done σ₀ 0 σ' hfree)
  exact ⟨σ', Δ', hInv, StoreTyp.erase_eq _ _, hT⟩

/-- No use after free: once the location is erased from the store typing, a
    dereference of it is not typable at all. -/
example : ∀ t : Typ, ¬ HasTypeS (StoreTyp.erase Δ₀ 0) [] [] (.refLoad (.lit (.loc 0))) t :=
  fun _t h => safety_freed_not_dereferenceable (Δ := StoreTyp.erase Δ₀ 0) (l := 0)
    (StoreTyp.erase_eq _ _) h

/-! ## Progress and preservation on concrete programs -/

/-- A reference creation is a value. -/
example : IsValue (.refCreate (.lit (.int 1)) .iso .intType)
    ∨ ∃ σ' e', Step σ₀ (.refCreate (.lit (.int 1)) .iso .intType) σ' e' :=
  progressS σ₀_typed (HasTypeS.refCreate _ _ _ _ _ _ (HasTypeS.lit_val _ _ _ _ _ (ValueType.int _ _)))

/-- Loading through a freshly created reference reduces without a store. -/
example : Step σ₀ (.refLoad (.refCreate (.lit (.int 1)) .iso .intType)) σ₀
    (.lit (.int 1)) :=
  Step.ref_load_eval σ₀ (.lit (.int 1)) .iso .intType (IsValue.lit _)

/-- Preservation for the load step: the loaded value is typed. -/
example : ∃ Δ', StoreInv σ₀ Δ' ∧ HasTypeS Δ' [] [] (.lit (.int 7)) .intType := by
  obtain ⟨Δ', hInv, hT⟩ := preservationS σ₀_typed (.refLoad _ _ _ _ _ _ decl₀)
    (Step.ref_load_done σ₀ 0 .intType (.int 7)
      (by rw [Store.load, if_neg (by simp [σ₀]), heap₀]))
  exact ⟨Δ', hInv, hT⟩

end Morph.Tests.StoreTyping

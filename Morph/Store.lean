/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Specs.TypeSystem.Spec
open Morph.Core
open Morph.Syntax

namespace Morph

/-!
# Typed Store for Operational Semantics

This module defines the store (heap) model for Morph's operational semantics.
The store enables formal verification of memory safety properties including:
- No use-after-free
- No double-free
- Capability-safe transitions (iso → val, iso → ref)

## Design (ADR-010)

The store is a typed mapping from abstract locations to (type, value) pairs.
The Step relation carries store state: `Step : Store → Expr → Store → Expr → Prop`.

This follows the CompCert methodology: expressions describe computation, the store
describes state. Memory safety is proven by showing that well-typed programs
preserve the store typing invariant.

## Migration Path

Phase 1 (current): Store type defined, not yet integrated into Step.
Phase 2: Step signature changes to carry Store.
Phase 3: Linear context added to HasType.
Phase 4: Memory safety proofs.

-/


/-! ## Abstract Location -/

/-- Abstract heap location. Morally a Nat, but wrapped for clarity. -/
abbrev Loc := Nat

/-! ## Store State -/

/-- The typed store maps locations to (type, value) pairs.
    - `heap`: partial map from locations to typed values
    - `nextLoc`: fresh location generator (monotonically increasing)
    - `freed`: list of freed locations (for double-free detection)
-/
structure Store where
  heap    : Loc → Option (Typ × Value)
  nextLoc : Loc
  freed   : List Loc

namespace Store

/-! ## Store Operations -/

/-- The empty store. -/
def empty : Store :=
  { heap := fun _ => none
    nextLoc := 0
    freed := [] }

/-- Allocate a new location with a typed value.
    Returns the updated store and the fresh location. -/
def alloc (σ : Store) (τ : Typ) (v : Value) : Store × Loc :=
  let loc := σ.nextLoc
  ( { heap := fun l => if l = loc then some (τ, v) else σ.heap l
      nextLoc := loc + 1
      freed := σ.freed }
  , loc )

/-- Load a typed value from a location.
    Returns none if the location is unallocated or freed. -/
def load (σ : Store) (loc : Loc) : Option (Typ × Value) :=
  if loc ∈ σ.freed then none
  else σ.heap loc

/-- Store a value at an existing location (mutate in place).
    Returns none if the location is freed. -/
def store (σ : Store) (loc : Loc) (v : Value) (τ : Typ) : Option Store :=
  if loc ∈ σ.freed then none
  else some
    { heap := fun l => if l = loc then some (τ, v) else σ.heap l
      nextLoc := σ.nextLoc
      freed := σ.freed }

/-- Free a location (mark as freed, preventing future access).
    Returns none if already freed. -/
def free (σ : Store) (loc : Loc) : Option Store :=
  if loc ∈ σ.freed then none
  else some
    { heap := fun l => if l = loc then none else σ.heap l
      nextLoc := σ.nextLoc
      freed := loc :: σ.freed }

/-! ## Store Queries -/

/-- Check if a location is allocated and not freed. -/
def isValid (σ : Store) (loc : Loc) : Bool :=
  !(σ.freed.contains loc) && (σ.heap loc).isSome

/-- Check if a location has been freed. -/
def isFreed (σ : Store) (loc : Loc) : Bool :=
  loc ∈ σ.freed

/-! ## Store Typing Invariant

The real store invariant is `StoreTyped` / `StoreInv` in
`Morph/Specs/TypeSystem/StoreTyping.lean`, which additionally relates each
location to the `StoreTyp` map used for typing and requires the stored value to
inhabit its declared type. An earlier placeholder tracked only the freed list
and has been removed. -/

/-! ## Capability-Specific Store Properties -/

/-- An iso capability means unique ownership: no other location or variable
    can reference this location. -/
def IsUniqueOwner (σ : Store) (loc : Loc) : Prop :=
  -- The location exists in the heap
  ∃ τ v, σ.heap loc = some (τ, v) ∧
  -- It has iso capability
  (∃ τ', τ = .refType .iso τ') ∧
  -- No other live location points to it
  loc ∉ σ.freed

/-- A val capability means shared immutable: the value cannot be mutated
    through this reference. -/
def IsSharedImmutable (σ : Store) (loc : Loc) : Prop :=
  ∃ τ v, σ.heap loc = some (τ, v) ∧
  (∃ τ', τ = .refType .val τ') ∧
  loc ∉ σ.freed

/-- A ref capability means exclusive mutable borrow: only one ref can exist
    at a time for a given location. -/
def IsExclusiveBorrow (σ : Store) (loc : Loc) : Prop :=
  ∃ τ v, σ.heap loc = some (τ, v) ∧
  (∃ τ', τ = .refType .ref τ') ∧
  loc ∉ σ.freed

end Store

/-! ## Value Extension for Locations

The `Value.loc` constructor wraps a store location as a runtime value.
This enables references to be passed as first-class values.

NOTE: `Value.loc` is already defined in Core.lean as `Value.loc : Loc → Value`.
This module documents the semantics of location values. -/

/-! ## Store Typing Map

### Deviations from the Phase 1d sketch (and why)

1. **`ValueType.undef` is not a constructor** (`Value.loc` also carries an extra
   `cap ≠ .iso` premise). A constructor of `¬ ValueType Δ .undef τ` is not a
   constructor of `ValueType` at all, so `undef` is instead excluded by giving it
   no case: `not_valueType_undef` proves `¬ ValueType Δ .undef τ` for *every* `τ`.
   The `cap ≠ .iso` premise on `ValueType.loc` makes "an `iso` reference is not
   storable" part of the typing relation, which is exactly what makes freeing
   sound (`noLocValue_of_iso`, `free_invalidates_typed`).

2. **`StoreTyped` relates a heap cell to `pointeeTy Δ loc`, not to `Δ loc`.**
   `Store.store` writes the *pointee* type `τ` into the cell while `Δ loc` is
   `some (.refType cap τ)`, so `Δ loc = some τ` cannot hold after a write.

3. **`StoreInv` (two-sided) is the invariant used by the progress/preservation
   theorems**, and `storeTyped_load_some`, `not_freed_of_typed`,
   `alloc_preserves_typed`, `store_preserves_typed` and `free_invalidates_typed`
   carry the extra side conditions (location allocated / un-freed / `iso`)
   without which the one-sided statements are false. Each is documented at its
   definition.

`StoreTyp` maps abstract locations to declared types. A declared location is
written `Δ loc = some (.refType cap τ)`: the *program* sees a reference of type
`.refType cap τ` for that location, while the *heap cell* is declared with the
pointee type `τ` (see `pointeeTy` below, which is the projection used by the
invariant). This distinction is what makes `Store.store` — which writes the
pointee type into the cell — compatible with a typing discipline in which the
reference type `.refType cap τ` is the type of the `Value.loc loc` value. -/

/-- Store typing map: each live location maps to its declared type. -/
abbrev StoreTyp := Loc → Option Typ

/-- The pointee type of a type: a reference points at its content type. -/
def pointeeOf : Typ → Typ
  | .refType _ τ => τ
  | τ => τ

/-- Type of the *contents* of a location, as declared by a store typing map.

    `Δ loc = some (.refType cap τ)` means "`loc` is a live location holding a
    reference to a `τ`", so its heap cell is declared with type `τ`. Any other
    declaration `Δ loc = some τ` declares the cell directly with type `τ`. -/
def pointeeTy (Δ : StoreTyp) (loc : Loc) : Option Typ :=
  match Δ loc with
  | some τ => some (pointeeOf τ)
  | none => none

/-- Types that are *not* reference types. Needed when a location is populated
    with a value whose own type must be recorded verbatim in the store typing. -/
def NonRefTyp : Typ → Prop
  | .refType _ _ => False
  | _ => True

@[simp] theorem pointeeTy_of_none {Δ : StoreTyp} {loc : Loc} (h : Δ loc = none) :
    pointeeTy Δ loc = none := by
  simp [pointeeTy, h]

theorem pointeeTy_of_ref {Δ : StoreTyp} {loc : Loc} {cap : Capability} {τ : Typ}
    (h : Δ loc = some (.refType cap τ)) : pointeeTy Δ loc = some τ := by
  simp [pointeeTy, pointeeOf, h]

theorem pointeeTy_of_eq {Δ : StoreTyp} {loc : Loc} {τ : Typ} (h : Δ loc = some τ) :
    pointeeTy Δ loc = some (pointeeOf τ) := by
  simp [pointeeTy, h]

theorem pointeeTy_of_nonref {Δ : StoreTyp} {loc : Loc} {τ : Typ}
    (hnr : NonRefTyp τ) (h : Δ loc = some τ) : pointeeTy Δ loc = some τ := by
  cases τ <;> simp_all [pointeeTy, pointeeOf, NonRefTyp]

/-! ## Store Typing Operations -/

namespace StoreTyp

/-- Extend `Δ` with a fresh location `l`, declared to hold content of type `τ`. -/
def extend (Δ : StoreTyp) (l : Loc) (τ : Typ) : StoreTyp :=
  fun l' => if l' = l then some τ else Δ l'

@[simp] theorem extend_eq (Δ : StoreTyp) (l : Loc) (τ : Typ) :
    extend Δ l τ l = some τ := by
  simp [extend]

@[simp] theorem extend_ne {Δ : StoreTyp} {l l' : Loc} {τ : Typ} (h : l' ≠ l) :
    extend Δ l τ l' = Δ l' := by
  simp [extend, h]

/-- Forget `l` in `Δ`: after the location is freed it is no longer declared, so
    no well-typed value can refer to it any more. -/
def erase (Δ : StoreTyp) (l : Loc) : StoreTyp :=
  fun l' => if l' = l then none else Δ l'

@[simp] theorem erase_eq (Δ : StoreTyp) (l : Loc) : erase Δ l l = none := by
  simp [erase]

@[simp] theorem erase_ne {Δ : StoreTyp} {l l' : Loc} (h : l' ≠ l) :
    erase Δ l l' = Δ l' := by
  simp [erase, h]

@[simp] theorem pointeeTy_extend {Δ : StoreTyp} {l : Loc} {τ : Typ}
    (hnr : NonRefTyp τ) : pointeeTy (extend Δ l τ) l = some τ :=
  pointeeTy_of_nonref hnr (extend_eq Δ l τ)

@[simp] theorem pointeeTy_erase_self (Δ : StoreTyp) (l : Loc) :
    pointeeTy (erase Δ l) l = none := by simp [pointeeTy]

theorem pointeeTy_extend_ne {Δ : StoreTyp} {l l' : Loc} {τ : Typ} (h : l' ≠ l) :
    pointeeTy (extend Δ l τ) l' = pointeeTy Δ l' := by
  simp only [pointeeTy, extend, if_neg h]

theorem pointeeTy_erase_ne {Δ : StoreTyp} {l l' : Loc} (h : l' ≠ l) :
    pointeeTy (erase Δ l) l' = pointeeTy Δ l' := by
  simp only [pointeeTy, erase, if_neg h]

end StoreTyp

/-! ## Value Typing -/

mutual

/-- A value inhabits type `τ` relative to a store typing `Δ`.

    Note the `loc` case: a location value is well-typed only if `Δ` knows the
    location and it holds a reference type. This is what ties values to the heap.

    Two deliberate restrictions:

    * `.undef` has no constructor, so it is never well-typed at *any* type
      (`not_valueType_undef`). Uninitialized memory is ruled out of well-typed
      values.
    * A location value typed with the linear `iso` capability is excluded. `iso`
      means unique ownership, so an `iso` pointer may not be *stored* in a heap
      cell: this is what makes `Store.free` safe (see `noLocValue_of_iso`). The
      `refFree` typing rule below still hands out `iso` references — it simply
      never types a `.loc` value as `iso`. -/
inductive ValueType : StoreTyp → Value → Typ → Prop where
  | int : ∀ Δ n, ValueType Δ (.int n) .intType
  | bool : ∀ Δ b, ValueType Δ (.bool b) .boolType
  | string : ∀ Δ s, ValueType Δ (.string s) .stringType
  | unit : ∀ Δ, ValueType Δ .unit .unitType
  | pointer : ∀ Δ p, ValueType Δ (.pointer p) .pointerType
  | float : ∀ Δ w f, ValueType Δ (.float f) (.floatType w)
  | none : ∀ Δ τ, ValueType Δ .none (.optionType τ)
  | some : ∀ Δ v τ, ValueType Δ v τ → ValueType Δ (.some v) (.optionType τ)
  | ok : ∀ Δ v τ_ok τ_err, ValueType Δ v τ_ok →
      ValueType Δ (.ok v) (.resultType τ_ok τ_err)
  | err : ∀ Δ v τ_ok τ_err, ValueType Δ v τ_err →
      ValueType Δ (.err v) (.resultType τ_ok τ_err)
  | tuple_ : ∀ Δ vs τs, ValueTypes Δ vs τs → ValueType Δ (.tuple_ vs) (.tupleType τs)
  | array_ : ∀ Δ vs τ, ValueTypes Δ vs (List.replicate vs.length τ) →
      ValueType Δ (.array_ vs) (.arrayType τ vs.length)
  | loc : ∀ Δ loc cap τ, Δ loc = some (.refType cap τ) → cap ≠ .iso →
      ValueType Δ (.loc loc) (.refType cap τ)

/-- List version of `ValueType`. -/
inductive ValueTypes : StoreTyp → List Value → List Typ → Prop where
  | nil : ∀ Δ, ValueTypes Δ [] []
  | cons : ∀ Δ v vs τ τs, ValueType Δ v τ → ValueTypes Δ vs τs →
      ValueTypes Δ (v :: vs) (τ :: τs)

end

/-- `undef` is never well-typed, at any type: uninitialized memory cannot occur
    in a well-typed value. -/
theorem not_valueType_undef {Δ : StoreTyp} (τ : Typ) :
    ¬ ValueType Δ .undef τ := by
  intro h
  cases h

/-- A location value is typable exactly when `Δ` declares it as a non-`iso`
    reference. -/
theorem valueType_loc_iff {Δ : StoreTyp} {loc : Loc} {cap : Capability} {τ : Typ}
    (h : ValueType Δ (.loc loc) (.refType cap τ)) : Δ loc = some (.refType cap τ) := by
  cases h with
  | loc _ _ _ hΔ _ => exact hΔ

mutual

/-- Monotonicity of value typing: *learning more* about locations never breaks a
    value typing, provided every newly declared location was undeclared before.
    This is what allows `Δ` to be extended by an allocation. -/
theorem valueType_mono {Δ Δ' : StoreTyp} (h : ∀ l, Δ' l = Δ l ∨ Δ l = none) :
    ∀ {v : Value} {τ : Typ}, ValueType Δ v τ → ValueType Δ' v τ := by
  intro v τ hv
  cases hv with
  | int n => exact .int _ _
  | bool b => exact .bool _ _
  | string s => exact .string _ _
  | unit => exact .unit _
  | pointer p => exact .pointer _ _
  | float w f => exact .float _ _ _
  | none τ => exact .none _ _
  | some v τ hv => exact .some _ _ _ (valueType_mono h hv)
  | ok v τ_ok τ_err hv => exact .ok _ _ _ _ (valueType_mono h hv)
  | err v τ_ok τ_err hv => exact .err _ _ _ _ (valueType_mono h hv)
  | tuple_ vs τs hvs => exact .tuple_ _ _ _ (valueTypes_mono h hvs)
  | array_ vs τ hvs => exact .array_ _ _ _ (valueTypes_mono h hvs)
  | loc loc cap τ hΔ hcap =>
      rcases h loc with h' | hnone
      · exact .loc _ _ _ _ (h'.trans hΔ) hcap
      · rw [hnone] at hΔ
        simp at hΔ

theorem valueTypes_mono {Δ Δ' : StoreTyp} (h : ∀ l, Δ' l = Δ l ∨ Δ l = none) :
    ∀ {vs : List Value} {τs : List Typ}, ValueTypes Δ vs τs → ValueTypes Δ' vs τs := by
  intro vs τs hvs
  cases hvs with
  | nil => exact .nil _
  | cons v vs τ τs hv hvs =>
      exact .cons _ _ _ _ _ (valueType_mono h hv) (valueTypes_mono h hvs)

end

theorem valueType_extend_ne {Δ : StoreTyp} {l : Loc} {τ : Typ} {v : Value} {t : Typ}
    (hd : Δ l = none) (hv : ValueType Δ v t) : ValueType (StoreTyp.extend Δ l τ) v t := by
  refine @valueType_mono Δ (StoreTyp.extend Δ l τ) (fun x => ?_) v t hv
  by_cases hx : x = l
  · exact Or.inr (by rw [hx]; exact hd)
  · exact Or.inl (StoreTyp.extend_ne hx)

theorem valueType_erase_ne_of_none {Δ : StoreTyp} {l : Loc} {v : Value} {t : Typ}
    (hd : Δ l = none) (hv : ValueType Δ v t) : ValueType (StoreTyp.erase Δ l) v t := by
  refine @valueType_mono Δ (StoreTyp.erase Δ l) (fun x => ?_) v t hv
  by_cases hx : x = l
  · exact Or.inl (by simp [hx, hd])
  · exact Or.inl (StoreTyp.erase_ne hx)

/-! ## Absence of Pointers to a Location -/

mutual

/-- `NoLocValue loc v`: the value `v` contains no pointer to `loc`. -/
def NoLocValue : Loc → Value → Prop
  | loc, .loc l => l ≠ loc
  | loc, .some v => NoLocValue loc v
  | loc, .ok v => NoLocValue loc v
  | loc, .err v => NoLocValue loc v
  | loc, .tuple_ vs => NoLocValues loc vs
  | loc, .array_ vs => NoLocValues loc vs
  | _, _ => True

/-- List version of `NoLocValue`. -/
def NoLocValues : Loc → List Value → Prop
  | _, [] => True
  | loc, v :: vs => NoLocValue loc v ∧ NoLocValues loc vs

end

theorem noLocValues_iff (loc : Loc) (vs : List Value) :
    NoLocValues loc vs ↔ ∀ v ∈ vs, NoLocValue loc v := by
  induction vs with
  | nil => simp [NoLocValues]
  | cons a as ih => simp [NoLocValues, ih]

mutual

/-- Erasing a location from `Δ` preserves the typing of every value that does not
    point at that location. -/
theorem valueType_erase_of_noLoc {Δ : StoreTyp} {loc : Loc} {v : Value} {τ : Typ} :
    ValueType Δ v τ → NoLocValue loc v → ValueType (StoreTyp.erase Δ loc) v τ := by
  intro hv hnd
  cases hv with
  | int n => exact .int _ _
  | bool b => exact .bool _ _
  | string s => exact .string _ _
  | unit => exact .unit _
  | pointer p => exact .pointer _ _
  | float w f => exact .float _ _ _
  | none τ => exact .none _ _
  | some v τ hv => exact .some _ _ _ (valueType_erase_of_noLoc hv hnd)
  | ok v τ_ok τ_err hv => exact .ok _ _ _ _ (valueType_erase_of_noLoc hv hnd)
  | err v τ_ok τ_err hv => exact .err _ _ _ _ (valueType_erase_of_noLoc hv hnd)
  | tuple_ vs τs hvs =>
      exact .tuple_ _ _ _ (valueTypes_erase_of_noLoc hvs (by simpa only [NoLocValue] using hnd))
  | array_ vs τ hvs =>
      exact .array_ _ _ _ (valueTypes_erase_of_noLoc hvs (by simpa only [NoLocValue] using hnd))
  | loc l cap τ hΔ hcap =>
      refine .loc _ l cap τ ?_ hcap
      rw [StoreTyp.erase_ne (by simpa [NoLocValue] using hnd)]
      exact hΔ

theorem valueTypes_erase_of_noLoc {Δ : StoreTyp} {loc : Loc}
    {vs : List Value} {τs : List Typ} :
    ValueTypes Δ vs τs → NoLocValues loc vs →
      ValueTypes (StoreTyp.erase Δ loc) vs τs := by
  intro hvs hnd
  cases hvs with
  | nil => exact .nil _
  | cons v vs τ τs hv hvs =>
      exact .cons _ _ _ _ _
        (valueType_erase_of_noLoc hv hnd.1)
        (valueTypes_erase_of_noLoc hvs hnd.2)

/-- A well-typed value never points at a location that `Δ` declares with the
    linear `iso` capability: `iso` references are uniquely owned, so they are not
    storable in the heap. This is what makes freeing an `iso` location safe. -/
theorem noLocValue_of_iso {Δ : StoreTyp} {loc : Loc} {v : Value} {τ : Typ}
    {cap : Capability} {τ' : Typ} (hv : ValueType Δ v τ)
    (hEq : Δ loc = some (.refType cap τ')) (hiso : cap = .iso) : NoLocValue loc v := by
  cases hv with
  | int n => dsimp [NoLocValue]
  | bool b => dsimp [NoLocValue]
  | string s => dsimp [NoLocValue]
  | unit => dsimp [NoLocValue]
  | pointer p => dsimp [NoLocValue]
  | float w f => dsimp [NoLocValue]
  | none τ => dsimp [NoLocValue]
  | some v τ hv =>
      simp only [NoLocValue]
      exact noLocValue_of_iso hv hEq hiso
  | ok v τ_ok τ_err hv =>
      simp only [NoLocValue]
      exact noLocValue_of_iso hv hEq hiso
  | err v τ_ok τ_err hv =>
      simp only [NoLocValue]
      exact noLocValue_of_iso hv hEq hiso
  | tuple_ vs τs hvs =>
      simp only [NoLocValue]
      exact noLocValues_of_iso hvs hEq hiso
  | array_ vs τ hvs =>
      simp only [NoLocValue]
      exact noLocValues_of_iso hvs hEq hiso
  | loc l cap0 τ0 hΔ hcap0 =>
      intro hl
      subst hl
      have h2 : Typ.refType cap τ' = Typ.refType cap0 τ0 := Option.some.inj (hEq.symm.trans hΔ)
      have h3 : cap = cap0 := by injection h2
      exact hcap0 (h3.symm.trans hiso)

theorem noLocValues_of_iso {Δ : StoreTyp} {loc : Loc} {vs : List Value} {τs : List Typ}
    {cap : Capability} {τ' : Typ} (hvs : ValueTypes Δ vs τs)
    (hEq : Δ loc = some (.refType cap τ')) (hiso : cap = .iso) : NoLocValues loc vs := by
  cases hvs with
  | nil => dsimp [NoLocValues]
  | cons v vs τ τs hv hvs =>
      exact ⟨noLocValue_of_iso hv hEq hiso, noLocValues_of_iso hvs hEq hiso⟩

end

/-! ## Store Invariant -/

/-- The store is well-typed: every allocated location is declared in `Δ` with a
    matching value type, and no allocated location has been freed. -/
def StoreTyped (σ : Store) (Δ : StoreTyp) : Prop :=
  ∀ loc τ v, σ.heap loc = some (τ, v) →
    pointeeTy Δ loc = some τ ∧ loc ∉ σ.freed ∧ ValueType Δ v τ

/-- The two-sided store invariant: `StoreTyped` *and* every declared location is
    really allocated. The second half is what makes dereferencing a declared
    location succeed instead of getting stuck (`load_ok`), so it is the invariant
    carried by the store-aware progress/preservation theorems. -/
def StoreInv (σ : Store) (Δ : StoreTyp) : Prop :=
  StoreTyped σ Δ ∧ ∀ loc τ, pointeeTy Δ loc = some τ → ∃ v, σ.heap loc = some (τ, v)

/-! ## Invariant: Instantiation -/

theorem storeTyped_empty : StoreTyped Store.empty (fun _ => none) := by
  intro loc τ v h
  simp [Store.empty] at h

theorem storeInv_empty : StoreInv Store.empty (fun _ => none) :=
  ⟨storeTyped_empty, fun loc τ h => by
    have h2 : (none : Option Typ) = some τ := (pointeeTy_of_none rfl).symm.trans h
    simp at h2⟩

/-! ## Invariant: Lookup -/

theorem storeTyped_load_some {σ : Store} {Δ : StoreTyp} {loc : Loc} {τ : Typ} {v : Value}
    (hσ : StoreTyped σ Δ) (hheap : σ.heap loc = some (τ, v)) :
    Store.load σ loc = some (τ, v) ∧ pointeeTy Δ loc = some τ ∧ loc ∉ σ.freed := by
  obtain ⟨hΔ, hnf, _⟩ := hσ loc τ v hheap
  exact ⟨by simp only [Store.load, if_neg hnf, hheap], hΔ, hnf⟩

/-- A successful load implies the location is live and its contents are typed. -/
theorem storeTyped_of_load {σ : Store} {Δ : StoreTyp} {loc : Loc} {τ : Typ} {v : Value}
    (hσ : StoreTyped σ Δ) (hload : Store.load σ loc = some (τ, v)) :
    loc ∉ σ.freed ∧ ValueType Δ v τ := by
  simp only [Store.load] at hload
  split at hload
  · simp at hload
  · rename_i hnf
    exact ⟨hnf, (hσ loc τ v hload).2.2⟩

/-! ## Heap Projections of Store Operations

These equations let the invariant be transported along a store operation
without repeatedly unfolding the (non-computational) store definitions. -/

@[simp] theorem alloc_nextLoc (σ : Store) (τ : Typ) (v : Value) :
    (Store.alloc σ τ v).2 = σ.nextLoc := rfl

@[simp] theorem alloc_heap (σ : Store) (τ : Typ) (v : Value) :
    (Store.alloc σ τ v).1.heap = fun l => if l = σ.nextLoc then some (τ, v) else σ.heap l := rfl

@[simp] theorem alloc_freed (σ : Store) (τ : Typ) (v : Value) :
    (Store.alloc σ τ v).1.freed = σ.freed := rfl

theorem store_heap {σ σ' : Store} {loc : Loc} {v : Value} {τ : Typ}
    (hstore : Store.store σ loc v τ = some σ') :
    (σ'.heap = fun l => if l = loc then some (τ, v) else σ.heap l) ∧
      (σ'.freed = σ.freed) := by
  have hmem : loc ∉ σ.freed := by
    intro hmem
    simp only [Store.store, if_pos hmem] at hstore
    simp at hstore
  simp only [Store.store, if_neg hmem, Option.some.injEq] at hstore
  rw [← hstore]
  exact ⟨rfl, rfl⟩

theorem free_heap {σ σ' : Store} {loc : Loc} (hfree : Store.free σ loc = some σ') :
    (σ'.heap = fun l => if l = loc then none else σ.heap l) ∧
      (σ'.freed = loc :: σ.freed) := by
  have hmem : loc ∉ σ.freed := by
    intro hmem
    simp only [Store.free, if_pos hmem] at hfree
    simp at hfree
  simp only [Store.free, if_neg hmem, Option.some.injEq] at hfree
  rw [← hfree]
  exact ⟨rfl, rfl⟩

/-! ## Invariant: Allocation -/

/-- Allocation extends the store typing at the fresh location (recording the type
    of the allocated payload) and keeps every old entry.

    Side conditions: the fresh location must be undeclared in `Δ` (so nothing is
    forgotten — this is what `valueType_mono` needs), un-freed, and the payload
    type must not itself be a reference type (a reference type in `Δ` denotes a
    cell holding its pointee type, see `pointeeTy`). -/
theorem alloc_preserves_typed {σ : Store} {Δ : StoreTyp} {τ : Typ} {v : Value}
    (hv : ValueType Δ v τ) (hσ : StoreTyped σ Δ)
    (hfresh : Δ σ.nextLoc = none) (hnotfreed : σ.nextLoc ∉ σ.freed)
    (hnr : NonRefTyp τ) :
    StoreTyped (Store.alloc σ τ v).1 (StoreTyp.extend Δ σ.nextLoc τ) := by
  simp only [StoreTyped, alloc_heap, alloc_freed]
  intro l τ' v' h
  by_cases hl : l = σ.nextLoc
  · rw [hl] at h ⊢
    have h' : some (τ, v) = some (τ', v') := by simpa only [if_pos rfl] using h
    have h2 : τ = τ' := congrArg Prod.fst (Option.some.inj h')
    have h3 : v = v' := congrArg Prod.snd (Option.some.inj h')
    subst h2; subst h3
    exact ⟨StoreTyp.pointeeTy_extend hnr, hnotfreed, valueType_extend_ne hfresh hv⟩
  · have h' : σ.heap l = some (τ', v') := by simpa only [if_neg hl] using h
    obtain ⟨hpt, hnf, hv'⟩ := hσ l τ' v' h'
    rw [StoreTyp.pointeeTy_extend_ne hl]
    exact ⟨hpt, hnf, valueType_extend_ne hfresh hv'⟩

/-! ## Invariant: Mutation -/

/-- Writing a well-typed value of the declared pointee type into a live,
    un-freed location preserves the invariant. -/
theorem store_preserves_typed {σ σ' : Store} {Δ : StoreTyp} {loc : Loc}
    {cap : Capability} {τ : Typ} {v : Value}
    (hσ : StoreTyped σ Δ) (hv : ValueType Δ v τ) (hfree : loc ∉ σ.freed)
    (hΔ : Δ loc = some (.refType cap τ))
    (hstore : Store.store σ loc v τ = some σ') : StoreTyped σ' Δ := by
  obtain ⟨hheap', hfreed'⟩ := store_heap hstore
  have htyped : StoreTyped σ' Δ := by
    simp only [StoreTyped]
    intro l τ' v' h
    rw [hheap'] at h
    rw [hfreed']
    by_cases hl : l = loc
    · subst hl
      have h' : some (τ, v) = some (τ', v') := by simpa only [if_pos rfl] using h
      have h2 : τ = τ' := congrArg Prod.fst (Option.some.inj h')
      have h3 : v = v' := congrArg Prod.snd (Option.some.inj h')
      subst h2; subst h3
      exact ⟨pointeeTy_of_ref hΔ, hfree, hv⟩
    · have h' : σ.heap l = some (τ', v') := by simpa only [if_neg hl] using h
      exact hσ l τ' v' h'
  exact htyped

/-- Freeing an `iso`-declared location preserves the invariant after *forgetting
    the location*: the freed cell holds nothing, so no value can be typed through
    it and no dangling reference can be formed.

    The `iso` side condition is essential: `iso` means unique ownership, so no
    live cell holds a pointer to `loc` (`noLocValue_of_iso`), which is exactly
    what makes erasing `loc` from `Δ` preserve the typing of all other cells. -/
theorem free_invalidates_typed {σ σ' : Store} {Δ : StoreTyp} {loc : Loc} {τ : Typ}
    (hσ : StoreTyped σ Δ) (hiso : Δ loc = some (.refType .iso τ))
    (hfree : Store.free σ loc = some σ') :
    StoreTyped σ' (StoreTyp.erase Δ loc) ∧ loc ∈ σ'.freed ∧ σ'.heap loc = none := by
  obtain ⟨hheap', hfreed'⟩ := free_heap hfree
  have htyped : StoreTyped σ' (StoreTyp.erase Δ loc) := by
    simp only [StoreTyped]
    intro l τ' v' h
    rw [hheap'] at h
    rw [hfreed']
    by_cases hl : l = loc
    · subst hl
      have h' : none = some (τ', v') := by simpa only [if_pos rfl] using h
      simp at h'
    · have h' : σ.heap l = some (τ', v') := by simpa only [if_neg hl] using h
      obtain ⟨hpt, hnf, hv⟩ := hσ l τ' v' h'
      have hpt' : pointeeTy (StoreTyp.erase Δ loc) l = some τ' := by
        rw [StoreTyp.pointeeTy_erase_ne hl]
        exact hpt
      have hnf' : ¬ l ∈ loc :: σ.freed := by
        rw [List.mem_cons]
        intro hmem
        rcases hmem with hmem | hmem
        · exact hl hmem
        · exact hnf hmem
      exact ⟨hpt', hnf', valueType_erase_of_noLoc hv (noLocValue_of_iso hv hiso rfl)⟩
  exact ⟨htyped, by rw [hfreed']; exact List.mem_cons_self, by rw [hheap']; simp⟩

/-! ## Invariant: Not Freed -/

theorem not_freed_of_typed {σ : Store} {Δ : StoreTyp} {loc : Loc} {τ : Typ} {v : Value}
    (hσ : StoreTyped σ Δ) (_hΔ : Δ loc = some τ) (hheap : σ.heap loc = some (τ, v)) :
    loc ∉ σ.freed :=
  (hσ loc τ v hheap).2.1

/-- A declared location (hence allocated, by the invariant) is never freed. -/
theorem not_freed_of_inv {σ : Store} {Δ : StoreTyp} {loc : Loc} {τ : Typ}
    (hInv : StoreInv σ Δ) (hΔ : Δ loc = some τ) : loc ∉ σ.freed := by
  obtain ⟨hσ, htot⟩ := hInv
  obtain ⟨v, hheap⟩ := htot loc _ (pointeeTy_of_eq hΔ)
  exact (hσ loc _ v hheap).2.1

/-! ## Invariant: Two-Sided Versions -/

theorem store_preserves_inv {σ σ' : Store} {Δ : StoreTyp} {loc : Loc}
    {cap : Capability} {τ : Typ} {v : Value}
    (hInv : StoreInv σ Δ) (hv : ValueType Δ v τ) (hΔ : Δ loc = some (.refType cap τ))
    (hstore : Store.store σ loc v τ = some σ') :
    StoreInv σ' Δ := by
  obtain ⟨hσ, htot⟩ := hInv
  obtain ⟨hheap'⟩ := store_heap hstore
  have hfree : loc ∉ σ.freed := not_freed_of_inv ⟨hσ, htot⟩ hΔ
  refine ⟨store_preserves_typed hσ hv hfree hΔ hstore, ?_⟩
  intro l t hpt
  by_cases hl : l = loc
  · subst hl
    have hpt' : pointeeTy Δ l = some τ := pointeeTy_of_ref hΔ
    have heq : τ = t := Option.some.inj (hpt'.symm.trans hpt)
    subst heq
    exact ⟨v, by rw [hheap']; simp only [↓reduceIte]⟩
  · obtain ⟨v', hv'⟩ := htot l t hpt
    refine ⟨v', ?_⟩
    rw [hheap']
    simpa only [if_neg hl] using hv'

theorem free_invalidates_inv {σ σ' : Store} {Δ : StoreTyp} {loc : Loc} {τ : Typ}
    (hInv : StoreInv σ Δ) (hiso : Δ loc = some (.refType .iso τ))
    (hfree : Store.free σ loc = some σ') :
    StoreInv σ' (StoreTyp.erase Δ loc) := by
  obtain ⟨hσ, htot⟩ := hInv
  obtain ⟨hheap', hfreed'⟩ := free_heap hfree
  refine ⟨(free_invalidates_typed hσ hiso hfree).1, ?_⟩
  intro l t hpt
  by_cases hl : l = loc
  · subst hl
    rw [StoreTyp.pointeeTy_erase_self] at hpt
    simp at hpt
  · rw [StoreTyp.pointeeTy_erase_ne hl] at hpt
    obtain ⟨v', hv'⟩ := htot l t hpt
    refine ⟨v', ?_⟩
    rw [hheap']
    simpa only [if_neg hl] using hv'

/-! ## Memory Safety of Store Operations

The key consequences: a live declared location can always be loaded, written, or
freed — i.e. no well-typed heap operation gets stuck. -/

theorem load_ok {σ : Store} {Δ : StoreTyp} {loc : Loc} {cap : Capability} {τ : Typ}
    (hInv : StoreInv σ Δ) (hΔ : Δ loc = some (.refType cap τ)) :
    ∃ v, Store.load σ loc = some (τ, v) := by
  obtain ⟨hσ, htot⟩ := hInv
  obtain ⟨v, hheap⟩ := htot loc τ (pointeeTy_of_ref hΔ)
  obtain ⟨hload, _, _⟩ := storeTyped_load_some hσ hheap
  exact ⟨v, hload⟩

/-- The type read out of a successful load agrees with the pointee type declared
    for that location. -/
theorem load_type_eq {σ : Store} {Δ : StoreTyp} {loc : Loc} {cap : Capability} {τ : Typ}
    {t : Typ} {v : Value} (hσ : StoreTyped σ Δ) (hΔ : Δ loc = some (.refType cap τ))
    (hload : Store.load σ loc = some (t, v)) : t = τ := by
  have hheap : σ.heap loc = some (t, v) := by
    simp only [Store.load, if_neg (storeTyped_of_load hσ hload).1] at hload
    exact hload
  obtain ⟨_, hpt, _⟩ := storeTyped_load_some hσ hheap
  exact Option.some.inj (hpt.symm.trans (pointeeTy_of_ref hΔ))

theorem store_ok {σ : Store} {Δ : StoreTyp} {loc : Loc} {cap : Capability} {τ : Typ}
    {v : Value} (hInv : StoreInv σ Δ) (hΔ : Δ loc = some (.refType cap τ)) :
    ∃ σ', Store.store σ loc v τ = some σ' := by
  have hnf : loc ∉ σ.freed := not_freed_of_inv hInv hΔ
  exact ⟨{ heap := fun l => if l = loc then some (τ, v) else σ.heap l
           nextLoc := σ.nextLoc
           freed := σ.freed },
    by simp [Store.store, hnf]⟩

theorem free_ok {σ : Store} {Δ : StoreTyp} {loc : Loc} {cap : Capability} {τ : Typ}
    (hInv : StoreInv σ Δ) (hΔ : Δ loc = some (.refType cap τ)) :
    ∃ σ', Store.free σ loc = some σ' := by
  have hnf : loc ∉ σ.freed := not_freed_of_inv hInv hΔ
  exact ⟨{ heap := fun l => if l = loc then none else σ.heap l
           nextLoc := σ.nextLoc
           freed := loc :: σ.freed },
    by simp [Store.free, hnf]⟩

end Morph

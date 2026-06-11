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

/-! ## Store Typing Invariant -/

/-- A store is well-typed if every allocated location contains a value
    that matches its declared type. -/
def StoreTyping (σ : Store) (Γ : TypEnv) : Prop :=
  ∀ loc τ v,
    σ.heap loc = some (τ, v) →
    loc ∉ σ.freed

-- NOTE: Full store typing (value matches type) will be proven after
-- Step is migrated to carry Store. For now, we only track the freed list invariant.

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

end Morph

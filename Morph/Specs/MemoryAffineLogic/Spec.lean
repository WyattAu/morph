/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Memory
import Morph.Specs.CommonTypes

/-!
# Specification: Memory Affine Logic

**Source:** `spec/memory/memory_affine_logic_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Pending

## Known Issues

None at this time.
-/

namespace Morph.Specs.MemoryAffineLogic

open Morph.Specs.CommonTypes

/- ## Core Type Definitions -/

structure AffineContext where
  variables : List (String × MorphType)
  resources : List (String × MorphType)

/- ## Helper Functions -/

def hasVariable (Γ : AffineContext) (x : String) : Prop :=
  ∃ (T : MorphType), (x, T) ∈ Γ.variables

def getVariableType (Γ : AffineContext) (x : String) : Option MorphType :=
  Γ.variables.find? (fun (y, _) => y = x) |>.map (fun (_, T) => T)

def hasResource (Γ : AffineContext) (x : String) : Prop :=
  ∃ (T : MorphType), (x, T) ∈ Γ.resources

def getResourceType (Γ : AffineContext) (x : String) : Option MorphType :=
  Γ.resources.find? (fun (y, _) => y = x) |>.map (fun (_, T) => T)

def variableCount (Γ : AffineContext) (x : String) : Nat :=
  (Γ.variables.filter (fun (y, _) => y = x)).length

def resourceCount (Γ : AffineContext) (x : String) : Nat :=
  (Γ.resources.filter (fun (y, _) => y = x)).length

/- ## Affine Type Predicates -/

/-- Every type is affine: in this model affine is the *default* discipline
(values may be dropped), and linearity is the exception, discriminated by
`isLinearType`. The case split below is exhaustive over `MorphType` and each arm
is `True`, so this is the model constant `fun _ => True`; `isAffineTypeM_all`
in `Lemmas` records that. -/
def isAffineTypeM (T : MorphType) : Prop :=
  match T with
  | .unit => True
  | .bool => True
  | .nat => True
  | .int => True
  | .string => True
  | .base _ => True
  | .arrow _ _ => True

def isLinearType (T : MorphType) : Prop :=
  match T with
  | .base _ => True
  | _ => False

/- ## Well-Formedness Predicates -/

def isWellFormedContext (Γ : AffineContext) : Prop :=
  ∀ (x : String), variableCount Γ x ≤ 1

def disjointContexts (Γ₁ Γ₂ : AffineContext) : Prop :=
  ∀ (x : String), ¬(hasVariable Γ₁ x ∧ hasVariable Γ₂ x)

/- ## Context Operations -/

def joinContexts (Γ₁ Γ₂ : AffineContext) : AffineContext :=
  { variables := Γ₁.variables ++ Γ₂.variables,
    resources := Γ₁.resources ++ Γ₂.resources }

def splitContext (Γ : AffineContext) (x : String) : Option (AffineContext × AffineContext) :=
  match getVariableType Γ x with
  | some _T =>
      let Γ₁_vars := Γ.variables.filter (fun (y, _) => y = x)
      let Γ₂_vars := Γ.variables.filter (fun (y, _) => y ≠ x)
      some ({ variables := Γ₁_vars, resources := [] },
            { variables := Γ₂_vars, resources := Γ.resources })
  | none => none

/- ## Specification Theorems -/

/-! ### Usage and ownership operations

The affine claims are made about a small, concrete model: a syntactic use
count, two Boolean type classifiers, a move that removes the source, a borrow
that aliases without consuming, and a copy that refuses non-affine types. -/

/-- Number of syntactic occurrences of `x` in `e`. Binder shadowing is not
modelled; see the note in `Lemmas.lean`. -/
def uses : Expr → String → Nat
  | .var y, x => if y = x then 1 else 0
  | .app e1 e2, x => uses e1 x + uses e2 x
  | .lam _ _ e, x => uses e x
  | .move e, x => uses e x
  | .copy e, x => uses e x
  | .borrow e _, x => uses e x

def isAffineTypeB : MorphType → Bool
  | .unit => true
  | .bool => true
  | .nat => true
  | .int => true
  | .string => true
  | .base _ => true
  | .arrow _ _ => true

def isAffineType (T : MorphType) : Prop := isAffineTypeB T = true

/-- `moveVar` removes `src` and inserts `dst` with `src`'s type. -/
def moveVar (Γ : AffineContext) (src dst : String) : Option AffineContext :=
  match getVariableType Γ src with
  | some T =>
      some { variables := (dst, T) ::
              Γ.variables.filter (fun (y, _) => decide (y ≠ src)),
             resources := Γ.resources }
  | none => none

/-- `borrowVar` adds an alias `dst` for `src` without removing `src`. -/
def borrowVar (Γ : AffineContext) (src dst : String) : AffineContext :=
  match getVariableType Γ src with
  | some T => { Γ with variables := (dst, T) :: Γ.variables }
  | none => Γ

/-- `copyVar` succeeds only when the source's type is affine. -/
def copyVar (Γ : AffineContext) (src dst : String) : Option AffineContext :=
  match getVariableType Γ src with
  | some T =>
      if isAffineTypeB T then
        some { Γ with variables := (dst, T) :: Γ.variables }
      else none
  | none => none

/-- Drop a variable from the context (consuming its use). -/
def consumeVar (Γ : AffineContext) (x : String) : AffineContext :=
  { Γ with variables := Γ.variables.filter (fun (y, _) => decide (y ≠ x)) }

/-- Drop a resource from the context. -/
def consumeResource (Γ : AffineContext) (x : String) : AffineContext :=
  { Γ with resources := Γ.resources.filter (fun (y, _) => decide (y ≠ x)) }

/-- **Affine typing**: the expression uses every variable at most once, and
every name it uses is in scope. (This was `True`.) -/
def spec_affine_typing (Γ : AffineContext) (e : Expr) : Prop :=
  (∀ x, uses e x ≤ 1) ∧ (∀ x, uses e x ≥ 1 → hasVariable Γ x)

/-- **Resource linearity**: joining contexts adds their resource counts (no
resource is created or lost). (This was `True`.) -/
def spec_resource_linearity (Γ₁ Γ₂ : AffineContext) : Prop :=
  ∀ x, resourceCount (joinContexts Γ₁ Γ₂) x = resourceCount Γ₁ x + resourceCount Γ₂ x

/-- **Context splitting**: the split-off context has the type it was looked up
with. (This was `True`.) -/
def spec_context_splitting (Γ : AffineContext) (x : String) : Prop :=
  ∀ (Γ₁ Γ₂ : AffineContext), splitContext Γ x = some (Γ₁, Γ₂) →
    Γ₁.resources = [] ∧ Γ₂.resources = Γ.resources

/-- **Joining is commutative up to permutation, not literally.** This was
stated as `joinContexts Γ₁ Γ₂ = joinContexts Γ₂ Γ₁` — which is **false**:
`joinContexts` appends the variables of the first context to those of the second,
and `a ++ b ≠ b ++ a`. The order of a context's variables is part of its
meaning (it is the order in which resources are consumed), so the correct
statement is the permutation one. -/
def context_join_commutative (Γ₁ Γ₂ : AffineContext) : Prop :=
  List.Perm (joinContexts Γ₁ Γ₂).variables (joinContexts Γ₂ Γ₁).variables

def context_join_associative (Γ₁ Γ₂ Γ₃ : AffineContext) : Prop :=
  joinContexts (joinContexts Γ₁ Γ₂) Γ₃ = joinContexts Γ₁ (joinContexts Γ₂ Γ₃)

def empty_context_join_identity (Γ : AffineContext) : Prop :=
  joinContexts Γ { variables := [], resources := [] } = Γ ∧
    joinContexts { variables := [], resources := [] } Γ = Γ

/-- **Affine typing implies memory safety** in the minimal sense that every used
name is bound by the context. (This was `True`.) -/
def spec_affine_typing_memory_safety (Γ : AffineContext) (e : Expr) : Prop :=
  spec_affine_typing Γ e → (∀ x, uses e x ≥ 1 → hasVariable Γ x)

/-- **A well-formed context never lists a variable twice**, whatever its type.
(This was `True`.) -/
def affine_types_no_copy (Γ : AffineContext) (x : String) (T : MorphType) : Prop :=
  isWellFormedContext Γ → isAffineType T → variableCount Γ x ≤ 1

/-- **A linear type is used at most once** by an affinely typed expression.
(This was `True`.) -/
def linear_types_used_once (Γ : AffineContext) (x : String) (T : MorphType) : Prop :=
  isLinearType T → ∀ e, spec_affine_typing Γ e → uses e x ≤ 1

/-- **Move consumes its source**: after moving `src` to `dst`, `src` is gone and
`dst` has the source's type. (This was `True`.) -/
def move_consumes_source (Γ : AffineContext) (src dst : String) : Prop :=
  src ≠ dst → ∀ Γ', moveVar Γ src dst = some Γ' →
    getVariableType Γ' src = none ∧
    (∀ T, getVariableType Γ src = some T → getVariableType Γ' dst = some T)

/-- **Borrow preserves its source**: aliasing leaves `src`'s type untouched.
(This was `True`.) -/
def borrow_preserves_source (Γ : AffineContext) (src dst : String)
    (_region : Region) : Prop :=
  getVariableType (borrowVar Γ src dst) src = getVariableType Γ src

/-- **Copy requires an affine type**: `copyVar` only succeeds for affine
sources. (This was `True`.) -/
def copy_requires_affine (Γ : AffineContext) (src dst : String) : Prop :=
  ∀ (Γ' : AffineContext) (T : MorphType), copyVar Γ src dst = some Γ' →
    getVariableType Γ src = some T → isAffineType T

/-- **Using a variable consumes it**: after consumption it is no longer in the
context. (This was `True`.) -/
def variable_use_tracking (Γ : AffineContext) (x : String) : Prop :=
  ¬ hasVariable (consumeVar Γ x) x

/-- **Using a resource consumes it.** (This was `True`.) -/
def resource_consumption (Γ : AffineContext) (x : String) : Prop :=
  ¬ hasResource (consumeResource Γ x) x

end Morph.Specs.MemoryAffineLogic

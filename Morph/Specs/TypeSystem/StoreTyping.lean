/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Store
import Morph.Semantics
import Morph.Specs.TypeSystem.Spec
import Morph.LinearContext
import Morph.Proofs.TypeSoundness.Progress
import Morph.Proofs.TypeSoundness.Preservation

/-!
# Store-Aware Typing and Memory Safety (Phase 1d)

`HasType ctx Γ e τ` (ADR-010) types the *program*: it says nothing about the
store, so it cannot type a location value (`.lit (.loc l)`) and it cannot
constrain a dereference to a live location.

This module adds the store-aware layer:

- `HasTypeS Δ ctx Γ e τ` extends ordinary typing with the store typing `Δ`
  (`Morph.StoreTyp`, see `Morph/Store.lean`), so location values become typable
  and heap operations are restricted to *declared* locations.
- `StoreInv σ Δ` (`Morph.Store`) is the invariant threaded through the two
  theorems below: allocated ⇒ declared and typed, declared ⇒ allocated and live.
- `progressS` / `preservationS` carry `Step : Store → Expr → Store → Expr → Prop`
  and give, respectively, "a well-typed program never gets stuck" and "the store
  invariant and the typing are restored after a step".
- The `safety_*` corollaries state the actual memory-safety properties: no
  well-typed load/store/free gets stuck, and a freed location can never be
  dereferenced again.

## Deviations from the plain Phase 1d sketch (and why)

1. **`StoreInv` rather than `StoreTyped` in the hypotheses of `progressS`,
   `preservationS` and the safety corollaries.** `StoreTyped` is one-sided
   ("allocated ⇒ declared"). Dereferencing a *declared* location may still get
   stuck when nothing is allocated there: take `σ.heap = fun _ => none`,
   `σ.freed = []`, `Δ l = some (.refType cap τ)` — `StoreTyped` holds, yet
   `.refLoad (.lit (.loc l))` steps to nothing. So the theorems take the
   two-sided `StoreInv` (`StoreTyped` + declared ⇒ allocated), which is what
   makes `load_ok` / `store_ok` / `free_ok` provable.

2. **`HasTypeS.refStore_cong` takes a `ValueType`, not a `HasTypeS`, for the
   stored value.** With a `HasTypeS` premise the rule is unsound: `HasType` types
   `.lit (.some v)` at `.optionType τ` for *any* `v` (including `.undef`), and
   `Step.ref_store_done` would then write an untyped value into the heap, so no
   sound invariant could be maintained.

3. **`ValueType.loc` requires `cap ≠ .iso`** (`Morph/Store.lean`). An `iso`
   reference is uniquely owned and must not be storable in a heap cell; without
   this guard a live cell could hold a pointer to the location being freed and
   `free_invalidates_typed` would be false. `noLocValue_of_iso` turns the guard
   into "no live cell points at an `iso` location", which is exactly what makes
   freeing sound. `HasTypeS.refFree` still hands out `iso` references.

4. **`HasTypeS.refCreate_cong` is dropped.** With an unconstrained payload it is
   not preserved: `Step.ref_create_step` turns `.refCreate e cap τ` into
   `.refCreate e' cap τ` for an arbitrary `e'`, which a rule requiring
   `IsValue e` cannot type again (a `.tuple_` of values may step to a different
   `.tuple_`, and proving the element-wise value invariant would need a mutual
   induction over the list-valued semantics). `HasTypeS.refCreate` already covers
   creating a reference from a literal value, which is all the semantics needs.

5. `HasTypeS` is stated for a general `ctx`/`Γ`, while `progressS` and
   `preservationS` are stated for closed programs (`[] []`), mirroring `progress`
   and `preservation` in `Morph.Proofs.TypeSoundness`.
-/

namespace Morph.Specs.TypeSystem

open Morph.Core
open Morph.Syntax
open Morph.Semantics

/-! ## Store-Aware Typing Judgment

`HasTypeS Δ ctx Γ e τ` extends `HasType ctx Γ e τ` with the store typing `Δ`:

- `lit_val` types a *value* literal by `ValueType`, which covers location
  values (`.lit (.loc l)`) as soon as `Δ l = some (.refType cap τ)`.
- `refLoad` / `refStore` / `refFree` are only available for locations declared
  in `Δ`, so a well-typed program can never mention a dangling location.
- `refFree` additionally requires the `iso` capability (only a unique reference
  may be consumed); `refStore` requires `cap ≠ .val` (an immutable reference
  cannot be mutated through).
-/

inductive HasTypeS : StoreTyp → LinCtx → TypEnv → Morph.Syntax.Expr → Morph.Core.Typ → Prop where
  /-- Anything typable without the store is typable with it. -/
  | lift : ∀ Δ ctx Γ e τ, HasType ctx Γ e τ ctx → HasTypeS Δ ctx Γ e τ
  /-- Value literals, including location values. -/
  | lit_val : ∀ Δ ctx Γ v τ, ValueType Δ v τ → HasTypeS Δ ctx Γ (.lit v) τ
  /-- Dereferencing a declared location. -/
  | refLoad : ∀ Δ ctx Γ loc cap τ,
      Δ loc = some (.refType cap τ) →
      HasTypeS Δ ctx Γ (.refLoad (.lit (.loc loc))) τ
  | refLoad_cong : ∀ Δ ctx Γ e cap τ,
      HasTypeS Δ ctx Γ e (.refType cap τ) →
      HasTypeS Δ ctx Γ (.refLoad e) τ
  /-- Writing through a mutable (non-`val`) reference. -/
  | refStore : ∀ Δ ctx Γ loc v cap τ,
      Δ loc = some (.refType cap τ) →
      ValueType Δ v τ →
      cap ≠ .val →
      HasTypeS Δ ctx Γ (.refStore (.lit (.loc loc)) (.lit v) τ) .unitType
  | refStore_cong : ∀ Δ ctx Γ e v cap τ,
      HasTypeS Δ ctx Γ e (.refType cap τ) →
      ValueType Δ v τ →
      cap ≠ .val →
      HasTypeS Δ ctx Γ (.refStore e (.lit v) τ) .unitType
  /-- Consuming a unique (`iso`) reference. -/
  | refFree : ∀ Δ ctx Γ loc τ,
      Δ loc = some (.refType .iso τ) →
      HasTypeS Δ ctx Γ (.refFree (.lit (.loc loc))) .unitType
  | refFree_cong : ∀ Δ ctx Γ e τ,
      HasTypeS Δ ctx Γ e (.refType .iso τ) →
      HasTypeS Δ ctx Γ (.refFree e) .unitType
  /-- Creating a reference (a value: it does not touch the store). -/
  | refCreate : ∀ Δ ctx Γ v cap τ,
      HasTypeS Δ ctx Γ (.lit v) τ →
      HasTypeS Δ ctx Γ (.refCreate (.lit v) cap τ) (.refType cap τ)

/-! ## Syntactic Facts

`HasType` cannot type a location value and `IsValue` cannot hold a heap
operation, so ordinary typing never reaches the store-changing rules. -/

theorem not_step_lit (σ σ' : Store) (v : Value) (e' : Expr) :
    ¬ Step σ (.lit v) σ' e' := by
  intro h
  cases h

theorem not_hasType_loc {ctx : LinCtx} {Γ : TypEnv} {l : Loc} {τ : Typ} {c : LinCtx} :
    ¬ HasType ctx Γ (.lit (.loc l)) τ c := by
  intro h
  cases h

theorem not_isValue_refLoad (e : Expr) : ¬ IsValue (.refLoad e) := by
  intro h
  cases h

theorem not_isValue_refStore (e v : Expr) (τ : Typ) : ¬ IsValue (.refStore e v τ) := by
  intro h
  cases h

theorem not_isValue_refFree (e : Expr) : ¬ IsValue (.refFree e) := by
  intro h
  cases h

theorem not_hasType_refLoadLit {ctx : LinCtx} {Γ : TypEnv} {l : Loc} {τ : Typ} {c : LinCtx} :
    ¬ HasType ctx Γ (.refLoad (.lit (.loc l))) τ c := by
  intro h
  cases h with
  | refLoad_type _ _ _ _ _ hE => exact not_hasType_loc hE

theorem not_hasType_refStoreLit {ctx : LinCtx} {Γ : TypEnv} {l : Loc} {v : Expr} {τ : Typ}
    {τ' : Typ} {c : LinCtx} : ¬ HasType ctx Γ (.refStore (.lit (.loc l)) v τ) τ' c := by
  intro h
  cases h with
  | refStore_type _ _ _ _ _ _ hE _ => exact not_hasType_loc hE

theorem not_hasType_refFreeLit {ctx : LinCtx} {Γ : TypEnv} {l : Loc} {τ' : Typ} {c : LinCtx} :
    ¬ HasType ctx Γ (.refFree (.lit (.loc l))) τ' c := by
  intro h
  cases h with
  | refFree_type _ _ _ _ hE => exact not_hasType_loc hE

/-- Ordinary typing cannot give a function a reference type. -/
theorem not_hasType_lam_ref {n : Nat} {body : Expr} {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] (.lam n body) (.refType cap τ) [] := by
  intro h
  cases h

/-- Ordinary typing cannot give `none_` a reference type. -/
theorem not_hasType_none__ref {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] .none_ (.refType cap τ) [] := by
  intro h
  cases h

/-- Ordinary typing cannot give `ok_ e` a reference type. -/
theorem not_hasType_ok__ref {e : Expr} {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] (.ok_ e) (.refType cap τ) [] := by
  intro h
  cases h

/-- Ordinary typing cannot give `err_ e` a reference type. -/
theorem not_hasType_err__ref {e : Expr} {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] (.err_ e) (.refType cap τ) [] := by
  intro h
  cases h

/-- Ordinary typing cannot give `some_ e` a reference type. -/
theorem not_hasType_some__ref {e : Expr} {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] (.some_ e) (.refType cap τ) [] := by
  intro h
  cases h

/-- Ordinary typing cannot give a tuple a reference type. -/
theorem not_hasType_tuple__ref {elems : List Expr} {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] (.tuple_ elems) (.refType cap τ) [] := by
  intro h
  cases h

/-- Ordinary typing cannot give an array literal a reference type. -/
theorem not_hasType_arrayLit_ref {elems : List Expr} {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] (.arrayLit elems) (.refType cap τ) [] := by
  intro h
  cases h

/-- Ordinary typing cannot give a value literal a reference type. -/
theorem not_hasType_lit_ref {v : Value} {cap : Capability} {τ : Typ} :
    ¬ HasType [] [] (.lit v) (.refType cap τ) [] := by
  intro h
  cases h

/-! ## Inversion Lemmas -/

/-- A location value is typable at `.refType cap τ` only if the location is
    declared in `Δ`. -/
theorem hasTypeS_lit_loc_ref {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv} {l : Loc}
    {cap : Capability} {τ : Typ} (h : HasTypeS Δ ctx Γ (.lit (.loc l)) (.refType cap τ)) :
    Δ l = some (.refType cap τ) := by
  cases h
  · exact False.elim (not_hasType_loc (by assumption))
  · exact valueType_loc_iff (by assumption)

/-- A dereference of a literal location is typable only if the location is
    declared in `Δ`. -/
theorem hasTypeS_refLoad_loc {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv} {l : Loc} {τ : Typ}
    (h : HasTypeS Δ ctx Γ (.refLoad (.lit (.loc l))) τ) :
    ∃ cap, Δ l = some (.refType cap τ) := by
  cases h
  · exact False.elim (not_hasType_refLoadLit (by assumption))
  · exact ⟨_, by assumption⟩
  · exact ⟨_, hasTypeS_lit_loc_ref (by assumption)⟩

/-- A `refFree` of a literal location is typable only if the location is declared
    with the `iso` capability (the only capability that may be consumed). -/
theorem hasTypeS_refFree_iso {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv} {l : Loc}
    (h : HasTypeS Δ ctx Γ (.refFree (.lit (.loc l))) .unitType) :
    ∃ τ, Δ l = some (.refType .iso τ) := by
  cases h
  · exact False.elim (not_hasType_refFreeLit
      (by assumption : HasType _ _ (.refFree (.lit (.loc l))) _ _))
  · exact ⟨_, by assumption⟩
  · exact ⟨_, hasTypeS_lit_loc_ref (by assumption)⟩

/-- The payload of a `refCreate` expression is typable at the pointee type. -/
theorem refCreate_inner_typed {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv} {e : Expr}
    {cap : Capability} {τ : Typ} (h : HasTypeS Δ ctx Γ (.refCreate e cap τ) (.refType cap τ)) :
    HasTypeS Δ ctx Γ e τ := by
  cases h
  · have hT : HasType ctx Γ (Expr.refCreate e cap τ) (.refType cap τ) ctx := by assumption
    cases hT
    exact .lift _ _ _ _ _ (by assumption)
  · exact by assumption

/-- Inversion for a location value: `.lit (.loc l)` can only be typable at a
    reference type, and then `Δ` must declare `l` with that very type. Stated
    with a `match` on the result type so that it applies without case-splitting
    the caller. -/
theorem hasTypeS_lit_loc_ref' {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv} {l : Loc} {t : Typ}
    (h : HasTypeS Δ ctx Γ (.lit (.loc l)) t) :
    match t with
    | .refType cap τ => Δ l = some (.refType cap τ)
    | _ => True := by
  cases h with
  | lift _ _ hT => exact False.elim (not_hasType_loc hT)
  | lit_val _ _ hv =>
      cases hv with
      | loc _ _ _ hΔ _ => exact hΔ

/-- Typing inversion for a `refCreate` expression typed at a reference type: the
    payload is typable at the pointee type (the `refCreate` rules force the
    annotation and the result type to agree). -/
theorem refCreate_typed_at_ref {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv} {e : Expr}
    {cap : Capability} {τ : Typ} {cap' : Capability} {τ' : Typ}
    (h : HasTypeS Δ ctx Γ (.refCreate e cap τ) (.refType cap' τ')) :
    HasTypeS Δ ctx Γ e τ' := by
  cases h with
  | lift _ _ hT =>
      cases hT
      exact .lift _ _ _ _ _ (by assumption)
  | refCreate _ _ _ _ => exact by assumption

/-- A reference value is either a location value or a `refCreate` (in which case
    the inner expression is a value). -/
theorem canonical_refS {Δ : StoreTyp} {cap : Capability} {τ : Typ} {e : Expr}
    (hv : IsValue e) (ht : HasTypeS Δ [] [] e (.refType cap τ)) :
    (∃ l, e = .lit (.loc l) ∧ Δ l = some (.refType cap τ))
      ∨ (∃ e', e = .refCreate e' cap τ ∧ IsValue e') := by
  cases hv with
  | lit v =>
      cases ht
      · exact absurd (by assumption) not_hasType_lit_ref
      · cases (by assumption : ValueType Δ v (.refType cap τ))
        exact Or.inl ⟨_, rfl, by assumption⟩
  | lam n body =>
      cases ht
      exact absurd (by assumption) not_hasType_lam_ref
  | none_ =>
      cases ht
      exact absurd (by assumption) not_hasType_none__ref
  | err_ e he =>
      cases ht
      exact absurd (by assumption) not_hasType_err__ref
  | ok_ e he =>
      cases ht
      exact absurd (by assumption) not_hasType_ok__ref
  | some_ e he =>
      cases ht
      exact absurd (by assumption) not_hasType_some__ref
  | tuple_ elems hvs =>
      cases ht
      exact absurd (by assumption) not_hasType_tuple__ref
  | array_ elems hvs =>
      cases ht
      exact absurd (by assumption) not_hasType_arrayLit_ref
  | refCreate e cap τ hv' =>
      cases ht
      · cases (by assumption : HasType _ _ _ _ _)
        exact Or.inr ⟨_, rfl, hv'⟩
      · exact Or.inr ⟨_, rfl, IsValue.lit _⟩

/-! ## Store-Typed Programs Never Change the Store

An expression typable without the store can never be a store operation that
*changes* the store: the three store-changing rules all mention a location
value, and `HasType` cannot type one. This is what lets `HasTypeS.lift` reuse the
store-free `preservation`. -/
theorem lift_step {σ σ' : Store} {ctx : LinCtx} {Γ : TypEnv} {e e' : Expr} {τ : Typ} {cout : LinCtx}
    (hT : HasType ctx Γ e τ cout) (hStep : Step σ e σ' e') :
    σ' = σ ∧ HasType ctx Γ e' τ cout := by
  have hT' := Morph.Proofs.TypeSoundness.preservation hT hStep
  refine ⟨?_, hT'⟩
  cases hStep with
  | ref_load_done _ _ _ _ => exact False.elim (not_hasType_refLoadLit hT)
  | ref_store_done _ _ _ _ _ => exact False.elim (not_hasType_refStoreLit hT)
  | ref_free_done _ _ _ => exact False.elim (not_hasType_refFreeLit hT)
  | _ => rfl

/-- A step out of an expression typed at a *reference* type never changes the
    store: such an expression is a location value or a `refCreate`, and neither
    can be the source of a store rule. This is what makes the `_cong` typing
    rules composable with `progressS`. -/
theorem ref_typed_step_preserves {Δ : StoreTyp} :
    ∀ {e : Expr} {t : Typ} {cap : Capability} {τ : Typ},
      HasTypeS Δ [] [] e t → t = .refType cap τ →
        ∀ {σ σ' : Store} {e' : Expr}, Step σ e σ' e' → σ' = σ := by
  intro e t cap τ hE
  revert cap τ
  induction hE with
  | lift _ _ hT =>
      intro cap τ ht σ σ' e' hStep
      cases hStep with
      | ref_load_done _ _ _ _ => exact False.elim (not_hasType_refLoadLit hT)
      | ref_store_done _ _ _ _ _ => exact False.elim (not_hasType_refStoreLit hT)
      | ref_free_done _ _ _ => exact False.elim (not_hasType_refFreeLit hT)
      | _ => rfl
  | lit_val _ _ _ =>
      intro cap τ ht σ σ' e' hStep
      exact absurd hStep (not_step_lit _ _ _ _)
  | refLoad _ _ _ _ =>
      intro cap τ ht σ σ' e' hStep
      cases hStep with
      | ref_load_done _ _ _ _ => rfl
      | ref_load_step _ _ _ => exact absurd (by assumption) (not_step_lit _ _ _ _)
  | refLoad_cong _ _ _ _ ih =>
      intro cap τ ht σ σ' e' hStep
      cases hStep with
      | ref_load_step _ _ _ =>
          obtain ⟨rfl⟩ := ih rfl (by assumption : Step _ _ _ _)
          rfl
      | ref_load_done _ _ _ _ => rfl
      | ref_load_eval _ _ _ _ => rfl
  | refStore _ _ _ _ _ _ _ => intro cap τ ht; cases ht
  | refStore_cong _ _ _ _ _ _ _ => intro cap τ ht; cases ht
  | refFree _ _ _ => intro cap τ ht; cases ht
  | refFree_cong _ _ _ _ => intro cap τ ht; cases ht
  | refCreate _ _ _ _ _ =>
      intro cap τ ht σ σ' e' hStep
      cases hStep with
      | ref_create_step _ _ _ _ _ => exact absurd (by assumption) (not_step_lit _ _ _ _)
/-! ## Progress -/

set_option maxHeartbeats 1000000 in
/-- A well-typed program is a value or it steps. A step out of a store-aware
    typing derivation either keeps the store (non-store rules) or is one of the
    three store rules, which succeed because the invariant says the declared
    location is live and allocated (`load_ok`, `store_ok`, `free_ok`). -/
theorem progressS_gen : ∀ {σ : Store} {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv}
    {e : Expr} {τ : Typ},
    ctx = [] → Γ = [] → StoreInv σ Δ → HasTypeS Δ ctx Γ e τ →
      IsValue e ∨ ∃ σ' e', Step σ e σ' e' := by
  intro σ Δ ctx Γ e τ hctx hΓ hInv h
  revert hctx hΓ hInv
  induction h with
  | lift _ _ hT =>
      intro hctx hΓ _
      subst hctx; subst hΓ
      rcases Morph.Proofs.TypeSoundness.progress (σ := σ) hT with hv | ⟨e', hs⟩
      · exact Or.inl hv
      · exact Or.inr ⟨σ, e', hs⟩
  | lit_val _ _ _ => intro _ _ _; exact Or.inl (IsValue.lit _)
  | refLoad _ _ _ hΔ =>
      intro _ _ hInv
      obtain ⟨v, hload⟩ := load_ok hInv hΔ
      exact Or.inr ⟨σ, .lit v, Step.ref_load_done σ _ _ v hload⟩
  | refLoad_cong _ _ _ hE ih =>
      intro hctx hΓ hInv
      subst hctx; subst hΓ
      rcases ih rfl rfl hInv with hv | ⟨_, e', hs⟩
      · rcases canonical_refS hv hE with ⟨l, hl, hΔ⟩ | ⟨e', he, hvi⟩
        · rw [hl]
          obtain ⟨v, hload⟩ := load_ok hInv hΔ
          exact Or.inr ⟨σ, .lit v, Step.ref_load_done σ l _ v hload⟩
        · rw [he]
          exact Or.inr ⟨σ, _, Step.ref_load_eval σ e' _ _ hvi⟩
      · obtain ⟨rfl⟩ := ref_typed_step_preserves hE rfl hs
        exact Or.inr ⟨σ, .refLoad e', Step.ref_load_step σ _ e' hs⟩
  | refStore _ _ _ _ hΔ _ _ =>
      intro _ _ hInv
      obtain ⟨σ', hstore⟩ := store_ok hInv hΔ
      exact Or.inr ⟨σ', .lit .unit, Step.ref_store_done σ _ _ _ σ' hstore⟩
  | refStore_cong _ _ _ _ hE _ hcap ihE =>
      intro hctx hΓ hInv
      subst hctx; subst hΓ
      rcases ihE rfl rfl hInv with hv | ⟨_, e', hs⟩
      · rcases canonical_refS hv hE with ⟨l, hl, hΔ⟩ | ⟨e', he, hvi⟩
        · rw [hl]
          obtain ⟨σ', hstore⟩ := store_ok hInv hΔ
          exact Or.inr ⟨σ', .lit .unit, Step.ref_store_done σ l _ _ σ' hstore⟩
        · rw [he]
          exact Or.inr ⟨σ, .lit .unit, Step.ref_store_eval σ e' _ _ _ hvi (IsValue.lit _) hcap⟩
      · obtain ⟨rfl⟩ := ref_typed_step_preserves hE rfl hs
        exact Or.inr ⟨σ, .refStore e' (.lit _) _, Step.ref_store_step_arr σ _ e' _ _ hs⟩
  | refFree _ _ hΔ =>
      intro _ _ hInv
      obtain ⟨σ', hfree⟩ := free_ok hInv hΔ
      exact Or.inr ⟨σ', .lit .unit, Step.ref_free_done σ _ σ' hfree⟩
  | refFree_cong _ _ hE ih =>
      intro hctx hΓ hInv
      subst hctx; subst hΓ
      rcases ih rfl rfl hInv with hv | ⟨_, e', hs⟩
      · rcases canonical_refS hv hE with ⟨l, hl, hΔ⟩ | ⟨e', he, hvi⟩
        · rw [hl]
          obtain ⟨σ', hfree⟩ := free_ok hInv hΔ
          exact Or.inr ⟨σ', .lit .unit, Step.ref_free_done σ l σ' hfree⟩
        · rw [he]
          exact Or.inr ⟨σ, .lit .unit, Step.ref_free_eval σ e' _ hvi⟩
      · obtain ⟨rfl⟩ := ref_typed_step_preserves hE rfl hs
        exact Or.inr ⟨σ, .refFree e', Step.ref_free_step σ _ e' hs⟩
  | refCreate _ _ _ _ => intro _ _ _; exact Or.inl (IsValue.refCreate (.lit _) _ _ (IsValue.lit _))

/-- A well-typed program is a value or it steps (closed programs). -/
theorem progressS {σ : Store} {Δ : StoreTyp} {e : Expr} {τ : Typ}
    (hInv : StoreInv σ Δ) (h : HasTypeS Δ [] [] e τ) :
    IsValue e ∨ ∃ σ' e', Step σ e σ' e' :=
  progressS_gen rfl rfl hInv h

/-! ## Preservation

The induction hypothesis is stated in two parts:

* for a step that does **not** change the store, the store typing is unchanged
  (this is what makes the value payload of a `refStore_cong` typable again);
* in general, some store typing works for the new store.

-/

set_option maxHeartbeats 1000000 in
/-- Stepping a well-typed program preserves its type *and* the store invariant.
    The store typing is adapted to the new store: only the store-changing rules
    modify it, and then only by forgetting the freed location. -/
theorem preservationS_gen : ∀ {σ : Store} {Δ : StoreTyp} {ctx : LinCtx} {Γ : TypEnv}
    {e : Expr} {τ : Typ},
    ctx = [] → Γ = [] → StoreInv σ Δ → HasTypeS Δ ctx Γ e τ →
      ∀ {σ' : Store} {e' : Expr}, Step σ e σ' e' →
        (∀ _hs : σ' = σ, StoreInv σ Δ ∧ HasTypeS Δ ctx Γ e' τ) ∧
        ∃ Δ', StoreInv σ' Δ' ∧ HasTypeS Δ' ctx Γ e' τ := by
  intro σ Δ ctx Γ e τ hctx hΓ hInv h
  revert hctx hΓ hInv
  induction h with
  | lift _ _ hT =>
      intro hctx hΓ hInv σ' e' hStep
      subst hctx; subst hΓ
      obtain ⟨rfl, hT'⟩ := lift_step hT hStep
      refine ⟨fun _ => ⟨hInv, ?_⟩, ⟨Δ, hInv, ?_⟩⟩
      · exact .lift _ _ _ _ _ hT'
      · exact .lift _ _ _ _ _ hT'
  | lit_val _ _ _ =>
      intro _ _ _ σ' e' hStep
      exact False.elim (not_step_lit _ _ _ _ hStep)
  | refLoad _ _ _ hΔ =>
      intro hctx hΓ hInv σ' e' hStep
      cases hStep with
      | ref_load_done _ _ _ _ =>
          have heq := load_type_eq hInv.1 hΔ (by assumption)
          obtain ⟨_, hv⟩ := storeTyped_of_load hInv.1 (by assumption)
          rw [heq] at hv
          refine ⟨fun _ => ⟨hInv, ?_⟩, ⟨Δ, hInv, ?_⟩⟩
          · exact .lit_val _ _ _ _ _ hv
          · exact .lit_val _ _ _ _ _ hv
      | ref_load_step _ _ _ =>
          exact False.elim (not_step_lit _ _ _ _ (by assumption))
  | refLoad_cong _ _ _ hE ih =>
      intro hctx hΓ hInv σ' e' hStep
      cases hStep with
      | ref_load_step _ _ _ =>
          obtain ⟨hf, _⟩ := ih hctx hΓ hInv (by assumption)
          obtain ⟨_, hT⟩ := hf rfl
          exact ⟨fun _ => ⟨hInv, .refLoad_cong _ _ _ _ _ _ hT⟩,
            ⟨Δ, hInv, .refLoad_cong _ _ _ _ _ _ hT⟩⟩
      | ref_load_eval _ _ _ _ =>
          refine ⟨fun _ => ⟨hInv, ?_⟩, ⟨Δ, hInv, ?_⟩⟩
          · exact refCreate_typed_at_ref hE
          · exact refCreate_typed_at_ref hE
      | ref_load_done _ _ _ _ =>
          have heq := load_type_eq hInv.1 (hasTypeS_lit_loc_ref' hE) (by assumption)
          obtain ⟨_, hv⟩ := storeTyped_of_load hInv.1 (by assumption)
          rw [heq] at hv
          refine ⟨fun _ => ⟨hInv, ?_⟩, ⟨Δ, hInv, ?_⟩⟩
          · exact .lit_val _ _ _ _ _ hv
          · exact .lit_val _ _ _ _ _ hv
  | refStore _ _ _ _ hΔ hv _ =>
      intro hctx hΓ hInv σ' e' hStep
      cases hStep with
      | ref_store_done _ _ _ _ _ =>
          exact ⟨fun _ => ⟨hInv, .lit_val _ _ _ _ _ (.unit _)⟩,
            ⟨Δ, store_preserves_inv hInv hv hΔ (by assumption), .lit_val _ _ _ _ _ (.unit _)⟩⟩
      | ref_store_step_arr _ _ _ _ _ =>
          exact False.elim (not_step_lit _ _ _ _ (by assumption))
      | ref_store_step_val _ _ _ _ _ _ =>
          exact False.elim (not_step_lit _ _ _ _ (by assumption))
  | refStore_cong _ _ _ _ hE _ _ ihE =>
      intro hctx hΓ hInv σ' e' hStep
      cases hStep with
      | ref_store_step_arr _ _ _ _ _ =>
          obtain ⟨hf, _⟩ := ihE hctx hΓ hInv (by assumption)
          refine ⟨?_, ?_⟩
          · intro _
            obtain ⟨_, hT⟩ := hf rfl
            exact ⟨hInv, .refStore_cong _ _ _ _ _ _ _ hT (by assumption) (by assumption)⟩
          · obtain ⟨_, hT⟩ := hf rfl
            exact ⟨Δ, hInv, .refStore_cong _ _ _ _ _ _ _ hT (by assumption) (by assumption)⟩
      | ref_store_step_val _ _ _ _ _ _ =>
          exact False.elim (not_step_lit _ _ _ _ (by assumption))
      | ref_store_eval _ _ _ _ _ _ _ =>
          exact ⟨fun _ => ⟨hInv, .lit_val _ _ _ _ _ (.unit _)⟩,
            ⟨Δ, hInv, .lit_val _ _ _ _ _ (.unit _)⟩⟩
      | ref_store_done _ _ _ _ _ =>
          exact ⟨fun _ => ⟨hInv, .lit_val _ _ _ _ _ (.unit _)⟩,
            ⟨Δ, store_preserves_inv hInv (by assumption : ValueType Δ _ _) (hasTypeS_lit_loc_ref' hE)
              (by assumption), .lit_val _ _ _ _ _ (.unit _)⟩⟩
  | refFree _ _ hΔ =>
      intro hctx hΓ hInv σ' e' hStep
      cases hStep with
      | ref_free_done _ _ _ =>
          exact ⟨fun _ => ⟨hInv, .lit_val _ _ _ _ _ (.unit _)⟩,
            ⟨StoreTyp.erase Δ _, free_invalidates_inv hInv hΔ (by assumption),
              .lit_val _ _ _ _ _ (.unit _)⟩⟩
      | ref_free_step _ _ _ =>
          exact False.elim (not_step_lit _ _ _ _ (by assumption))
  | refFree_cong _ _ hE ih =>
      intro hctx hΓ hInv σ' e' hStep
      cases hStep with
      | ref_free_step _ _ _ =>
          obtain ⟨hf, _⟩ := ih hctx hΓ hInv (by assumption)
          obtain ⟨_, hT⟩ := hf rfl
          exact ⟨fun _ => ⟨hInv, .refFree_cong _ _ _ _ _ hT⟩,
            ⟨Δ, hInv, .refFree_cong _ _ _ _ _ hT⟩⟩
      | ref_free_eval _ _ _ =>
          exact ⟨fun _ => ⟨hInv, .lit_val _ _ _ _ _ (.unit _)⟩,
            ⟨Δ, hInv, .lit_val _ _ _ _ _ (.unit _)⟩⟩
      | ref_free_done _ _ _ =>
          exact ⟨fun _ => ⟨hInv, .lit_val _ _ _ _ _ (.unit _)⟩,
            ⟨StoreTyp.erase Δ _, free_invalidates_inv hInv (hasTypeS_lit_loc_ref' hE)
              (by assumption), .lit_val _ _ _ _ _ (.unit _)⟩⟩
  | refCreate _ _ _ _ =>
      intro _ _ _ σ' e' hStep
      cases hStep with
      | ref_create_step _ _ _ _ _ =>
          exact False.elim (not_step_lit _ _ _ _ (by assumption))

/-- Stepping a well-typed program preserves its type and the store invariant. -/
theorem preservationS {σ : Store} {Δ : StoreTyp} {e e' : Expr} {τ : Typ}
    (hInv : StoreInv σ Δ) (h : HasTypeS Δ [] [] e τ) (hStep : Step σ e σ' e') :
    ∃ Δ', StoreInv σ' Δ' ∧ HasTypeS Δ' [] [] e' τ :=
  (preservationS_gen rfl rfl hInv h hStep).2


/-! ## Memory-Safety Corollaries

These are the point of the development: heap operations on well-typed,
store-typed programs are never stuck, and a freed location is unreachable. -/

/-- A well-typed load never gets stuck. -/
theorem safety_load_not_stuck {σ : Store} {Δ : StoreTyp} {l : Loc} {τ : Typ}
    (hInv : StoreInv σ Δ) (hT : HasTypeS Δ [] [] (.refLoad (.lit (.loc l))) τ) :
    ∃ σ' e', Step σ (.refLoad (.lit (.loc l))) σ' e' := by
  rcases progressS hInv hT with hv | ⟨σ', e', hs⟩
  · exact absurd hv (not_isValue_refLoad _)
  · exact ⟨σ', e', hs⟩

/-- A well-typed store never gets stuck. -/
theorem safety_store_not_stuck {σ : Store} {Δ : StoreTyp} {l : Loc} {v : Value}
    {τ : Typ} (hInv : StoreInv σ Δ)
    (hT : HasTypeS Δ [] [] (.refStore (.lit (.loc l)) (.lit v) τ) .unitType) :
    ∃ σ' e', Step σ (.refStore (.lit (.loc l)) (.lit v) τ) σ' e' := by
  rcases progressS hInv hT with hv | ⟨σ', e', hs⟩
  · exact absurd hv (not_isValue_refStore _ _ _)
  · exact ⟨σ', e', hs⟩

/-- A well-typed free never gets stuck. -/
theorem safety_free_not_stuck {σ : Store} {Δ : StoreTyp} {l : Loc}
    (hInv : StoreInv σ Δ) (hT : HasTypeS Δ [] [] (.refFree (.lit (.loc l))) .unitType) :
    ∃ σ' e', Step σ (.refFree (.lit (.loc l))) σ' e' := by
  rcases progressS hInv hT with hv | ⟨σ', e', hs⟩
  · exact absurd hv (not_isValue_refFree _)
  · exact ⟨σ', e', hs⟩

/-- No use after free: after a well-typed free, the freed location is no longer
    declared by the resulting store typing, and it is recorded as freed. -/
theorem safety_no_use_after_free {σ σ' : Store} {l : Loc} {Δ : StoreTyp} {e' : Expr}
    (hInv : StoreInv σ Δ) (hT : HasTypeS Δ [] [] (.refFree (.lit (.loc l))) .unitType)
    (hStep : Step σ (.refFree (.lit (.loc l))) σ' e') :
    ∃ Δ', StoreInv σ' Δ' ∧ Δ' l = none ∧ l ∈ σ'.freed := by
  obtain ⟨τ, hΔ⟩ := hasTypeS_refFree_iso hT
  have hfreeStep : Store.free σ l = some σ' := by
    cases hStep with
    | ref_free_done _ _ _ => assumption
    | ref_free_step _ _ _ => exact False.elim (not_step_lit _ _ _ _ (by assumption))
  obtain ⟨htyped, hmem, _⟩ := free_invalidates_typed hInv.1 hΔ hfreeStep
  exact ⟨StoreTyp.erase Δ l, ⟨htyped, (free_invalidates_inv hInv hΔ hfreeStep).2⟩,
    StoreTyp.erase_eq _ _, by simpa using hmem⟩

/-- If a location is not declared in the store typing, no well-typed expression
    can dereference it: no use after free. -/
theorem safety_freed_not_dereferenceable {Δ : StoreTyp} {l : Loc} {t : Typ}
    (hl : Δ l = none) (h : HasTypeS Δ [] [] (.refLoad (.lit (.loc l))) t) : False := by
  obtain ⟨cap', hΔ⟩ := hasTypeS_refLoad_loc h
  rw [hl] at hΔ
  simp at hΔ

end Morph.Specs.TypeSystem

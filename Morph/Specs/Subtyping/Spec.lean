/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TypeSystem.Spec

/-!
# Subtyping: a decidable, meaningful relation

Research loop 12, discharging **SG-005** ("Decidability proof for subtyping").

**What was there.** `Morph/Specs/TypeSystem/Spec.lean` declares

```lean
inductive Subtype : Typ -> Typ -> Prop where
  | refl : forall typ, Subtype typ typ
  | trans : forall typ1 typ2 typ3, Subtype typ1 typ2 -> Subtype typ2 typ3 -> Subtype typ1 typ3
```

`refl` and `trans` over reflexivity derive **equality and nothing else** — see
`subtype_iff_eq` below — and nothing in `HasType`, `inferType` or `typeCheck`
consumes the relation. Loop 1 recorded exactly this.

**And the gap table claims otherwise.** `SPEC_GAPS_AND_BASIS.md` marks GA-005
"Subtyping over `Typ` is decidable — **Validated** — `instDecidableSubtype`
(ADR-015): `isSubtype` decision procedure". Neither `isSubtype` nor
`instDecidableSubtype` exists anywhere in the repository, and no ADR-015 exists
either. GA-005 was *Validated* against a decision procedure that was never
written. This loop supplies it — for a relation worth having.

## The relation

`Sub` is a preorder on `Typ` with

- `neverType` as bottom and `unitType` as top;
- **covariance** in `optionType`, `resultType` (both components) and `arrayType`
  (element; the length is a literal, hence exact);
- **exactness** everywhere else. In particular `refType` is invariant in both
  capability and payload: handing a `refType .iso (optionType τ)` where a
  `refType .iso τ` is expected would *widen* what the holder may do with it,
  which is unsound in a capability system.

## What is proved

- **`isSubtype` is a decision procedure** — a total, structural function.
- **`isSubtype_sound`** — `isSubtype τ σ = true → Sub τ σ`.
- **`isSubtype_complete`** — `Sub τ σ → isSubtype τ σ = true`.
- Together: **`Decidable (Sub τ σ)`** — the decidability SG-005 asks for.
- **`subtype_iff_eq`** — the *old* relation is exactly equality, which is why
  proving anything about it was hopeless, and why GA-005's claim and SG-005's
  gap pointed in opposite directions at the same object.
-/

namespace Morph.Specs.Subtyping

open Morph.Core Morph.Syntax Morph.Specs.TypeSystem

/-- **Subtyping.** A preorder on types: `neverType` is the bottom, `unitType`
the top, and the type constructors are covariant. -/
inductive Sub : Typ → Typ → Prop where
  /-- Reflexivity. -/
  | refl (τ : Typ) : Sub τ τ
  /-- `neverType` is the bottom type. -/
  | never (τ : Typ) : Sub .neverType τ
  /-- `unitType` is the top type. -/
  | unit (τ : Typ) : Sub τ .unitType
  /-- `optionType` is covariant. -/
  | option {τ σ : Typ} : Sub τ σ → Sub (.optionType τ) (.optionType σ)
  /-- `resultType` is covariant in both components. -/
  | result {τ τ' σ σ' : Typ} : Sub τ σ → Sub τ' σ' →
      Sub (.resultType τ τ') (.resultType σ σ')
  /-- `arrayType` is covariant in its element; the length is exact. -/
  | array {τ σ : Typ} {n : Nat} : Sub τ σ → Sub (.arrayType τ n) (.arrayType σ n)

/-- The decision procedure. Total, structural, and — as the soundness and
completeness theorems below show — exactly decides `Sub`. -/
def isSubtype : Typ → Typ → Bool
  | .neverType, _ => true
  | _, .unitType => true
  | .optionType a, .optionType b => isSubtype a b
  | (.optionType _), _ => false
  | .resultType a b, .resultType c d => isSubtype a c && isSubtype b d
  | (.resultType _ _), _ => false
  | .arrayType a n, .arrayType b m => decide (n = m) && isSubtype a b
  | (.arrayType _ _), _ => false
  | .refType c a, .refType d b => decide (c = d) && Morph.Specs.TypeSystem.eqTyp a b
  | (.refType _ _), _ => false
  | t, s => Morph.Specs.TypeSystem.eqTyp t s

/-! ### Size facts

The measure is the shipped `tS` (the same one `eqTyp` is proved lawful
against). -/

/-- `tS` grows when a type is wrapped in `optionType`. -/
theorem tS_option (a : Typ) : tS a < tS (.optionType a) := by
  simp [Morph.Specs.TypeSystem.tS]

/-- `tS` grows when a type is wrapped in `resultType`. -/
theorem tS_result (a b : Typ) : tS a + tS b < tS (.resultType a b) := by
  simp [Morph.Specs.TypeSystem.tS]

/-- `tS` grows when a type is wrapped in `arrayType`. -/
theorem tS_array (a : Typ) (n : Nat) : tS a < tS (.arrayType a n) := by
  simp [Morph.Specs.TypeSystem.tS]

/-! ### Soundness and completeness -/

/-- **Soundness.** The decision procedure never accepts a non-subtype. -/
theorem isSubtype_sound : ∀ (τ σ : Typ), isSubtype τ σ = true → Sub τ σ := by
  have main : ∀ (fuel : Nat) (τ σ : Typ), tS τ + tS σ ≤ fuel →
      isSubtype τ σ = true → Sub τ σ := by
    intro fuel
    refine Nat.strongRecOn (motive := fun fuel =>
      ∀ (τ σ : Typ), tS τ + tS σ ≤ fuel → isSubtype τ σ = true → Sub τ σ)
      fuel (fun fuel' ih => ?_)
    intro τ σ hsize h
    cases τ with
    | neverType => exact Sub.never _
    | unitType =>
        cases σ with
        | unitType => exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | intType =>
        cases σ with
        | unitType => exact Sub.unit _
        | intType => exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | boolType =>
        cases σ with
        | unitType => exact Sub.unit _
        | boolType => exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | stringType =>
        cases σ with
        | unitType => exact Sub.unit _
        | stringType => exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | pointerType =>
        cases σ with
        | unitType => exact Sub.unit _
        | pointerType => exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | intWidthType w =>
        cases σ with
        | unitType => exact Sub.unit _
        | intWidthType w' =>
            simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff] at h
            cases h
            exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | floatType w =>
        cases σ with
        | unitType => exact Sub.unit _
        | floatType w' =>
            simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff] at h
            cases h
            exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | typeVar n =>
        cases σ with
        | unitType => exact Sub.unit _
        | typeVar n' =>
            simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff] at h
            cases h
            exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | structType name fields =>
        cases σ with
        | unitType => exact Sub.unit _
        | structType name' fields' =>
            simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff] at h
            cases h
            simp_all
            exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | refType c a =>
        cases σ with
        | unitType => exact Sub.unit _
        | refType d b =>
            simp only [isSubtype, Bool.and_eq_true] at h
            obtain ⟨hc, hτ⟩ := h
            have hc' : c = d := of_decide_eq_true hc
            have hτ' : a = b := (Morph.Specs.TypeSystem.eqTyp_iff a b).mp hτ
            subst hc'; subst hτ'
            exact Sub.refl _
        | _ =>
            simp [isSubtype] at h
    | tupleType ts =>
        cases σ with
        | unitType => exact Sub.unit _
        | tupleType ts' =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
            exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | functionType args ret =>
        cases σ with
        | unitType => exact Sub.unit _
        | functionType args' ret' =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
            exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | linearFunctionType args ret =>
        cases σ with
        | unitType => exact Sub.unit _
        | linearFunctionType args' ret' =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
            exact Sub.refl _
        | _ =>
            have h2 := (Morph.Specs.TypeSystem.eqTyp_iff _ _).mp h
            cases h2
    | optionType a =>
        cases σ with
        | unitType => exact Sub.unit _
        | optionType b =>
            simp only [isSubtype] at h
            have hle : tS a + tS b < fuel' := by
              have h2 := hsize
              have h3 : tS a + 1 + (tS b + 1) ≤ fuel' := by
                simpa [Morph.Specs.TypeSystem.tS] using h2
              omega
            exact Sub.option (ih (tS a + tS b) hle a b (by omega) h)
        | _ =>
            simp [isSubtype] at h
    | resultType a b =>
        cases σ with
        | unitType => exact Sub.unit _
        | resultType c d =>
            simp only [isSubtype, Bool.and_eq_true] at h
            obtain ⟨h1, h2⟩ := h
            have hle1 : tS a + tS c < fuel' := by
              have h2' := hsize
              have h3 : tS a + tS b + 1 + (tS c + tS d + 1) ≤ fuel' := by
                simpa [Morph.Specs.TypeSystem.tS] using h2'
              omega
            have hle2 : tS b + tS d < fuel' := by
              have h2' := hsize
              have h3 : tS a + tS b + 1 + (tS c + tS d + 1) ≤ fuel' := by
                simpa [Morph.Specs.TypeSystem.tS] using h2'
              omega
            exact Sub.result
              (ih (tS a + tS c) hle1 a c (by omega) h1)
              (ih (tS b + tS d) hle2 b d (by omega) h2)
        | _ =>
            simp [isSubtype] at h
    | arrayType a n =>
        cases σ with
        | unitType => exact Sub.unit _
        | arrayType b m =>
            simp only [isSubtype, Bool.and_eq_true] at h
            obtain ⟨hn, hsub⟩ := h
            have hn' : n = m := of_decide_eq_true hn
            subst hn'
            have hle : tS a + tS b < fuel' := by
              have h2 := hsize
              have h3 : tS a + 1 + (tS b + 1) ≤ fuel' := by
                simpa [Morph.Specs.TypeSystem.tS] using h2
              omega
            exact Sub.array (ih (tS a + tS b) hle a b (by omega) hsub)
        | _ =>
            simp [isSubtype] at h
  intro τ σ h
  exact main (tS τ + tS σ) τ σ (Nat.le_refl _) h

/-- `neverType` is below every type. -/
theorem isSubtype_never (σ : Typ) : isSubtype .neverType σ = true := by
  cases σ <;> rfl

/-- `unitType` is above every type. -/
theorem isSubtype_unit (τ : Typ) : isSubtype τ .unitType = true := by
  cases τ <;> rfl

/-- The decision procedure accepts every type against itself. -/
theorem isSubtype_refl : ∀ (τ : Typ), isSubtype τ τ = true := by
  intro τ
  cases τ with
  | neverType => simp [isSubtype]
  | unitType => simp [isSubtype]
  | intType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | boolType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | stringType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | pointerType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | intWidthType w => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | floatType w => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | typeVar n => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | structType name fields => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | refType c a => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | optionType a => simp [isSubtype, isSubtype_refl a]
  | resultType a b => simp [isSubtype, isSubtype_refl a, isSubtype_refl b]
  | arrayType a n => simp [isSubtype, isSubtype_refl a]
  | tupleType ts => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | functionType args ret => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  | linearFunctionType args ret => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]

/-- **Completeness.** The decision procedure never rejects a subtype. -/
theorem isSubtype_complete : ∀ {τ σ : Typ}, Sub τ σ → isSubtype τ σ = true := by
  intro τ σ h
  induction h with
  | refl τ => exact isSubtype_refl τ
  | never τ => exact isSubtype_never τ
  | unit τ => exact isSubtype_unit τ
  | option _ ih => simp [isSubtype, ih]
  | result _ _ ih1 ih2 => simp [isSubtype, ih1, ih2]
  | array _ ih => simp [isSubtype, ih]

/-- **Decidability.** The point of SG-005. -/
instance instDecidableSub (τ σ : Typ) : Decidable (Sub τ σ) :=
  if h : isSubtype τ σ then isTrue (isSubtype_sound τ σ h)
  else isFalse (fun h' => h (isSubtype_complete h'))

/-- Subtyping is reflexive. -/
theorem sub_refl (τ : Typ) : Sub τ τ := Sub.refl τ

/-- `neverType` is below every type, `unitType` above every type. -/
theorem sub_never (τ : Typ) : Sub .neverType τ := Sub.never τ

theorem sub_unit (τ : Typ) : Sub τ .unitType := Sub.unit τ

/-! ### The old relation was equality

`Subtype` — `refl` and `trans` over reflexivity — derives exactly equality.
This is why loop 1 could find nothing to prove about it, and why GA-005's
"Validated" claim and SG-005's open gap were pointing at the same object from
opposite directions. -/

/-- The shipped `Subtype` relation is exactly equality. -/
theorem subtype_iff_eq {τ σ : Typ} : Morph.Specs.TypeSystem.Subtype τ σ ↔ τ = σ := by
  constructor
  · intro h
    have aux : ∀ {t1 t2 : Typ}, Morph.Specs.TypeSystem.Subtype t1 t2 → t1 = t2 := by
      intro t1 t2 hh
      induction hh with
      | @refl t => rfl
      | @trans t1 t2 t3 _ _ ih1 ih2 => exact ih1.trans ih2
    exact aux h
  · intro h
    subst h
    exact Morph.Specs.TypeSystem.Subtype.refl _

end Morph.Specs.Subtyping

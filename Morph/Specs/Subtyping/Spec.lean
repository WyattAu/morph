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

(Since loop 44 the executable checker *does* consume the new relation, but only
at its acceptance boundary: `Morph.TypeChecker.checkTypeAs` is the exact check
or a top-level `isSubtype` of the inferred type, with soundness
`checkTypeAs_sound` in `Morph.Specs.TypeSystem.InferenceSound`. The judgment
`HasType` stays exact on purpose — adding subsumption to it would falsify its
inversion lemmas, since `boolType <: unitType`.)

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

mutual
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
  /-- `tupleType` is covariant pointwise; the length is exact. -/
  | tuple {ts ts' : List Typ} : SubList ts ts' → Sub (.tupleType ts) (.tupleType ts')
  /-- `structType` is covariant pointwise in field types; the struct name,
  the field names (in order), and the field count are exact. -/
  | struct {nm : String} {fs fs' : List (String × Typ)} :
      SubFields fs fs' → Sub (.structType nm fs) (.structType nm fs')

/-- Pointwise subtyping on tuple elements. -/
inductive SubList : List Typ → List Typ → Prop where
  | nil : SubList [] []
  | cons {a b : Typ} {as bs : List Typ} :
      Sub a b → SubList as bs → SubList (a :: as) (b :: bs)

/-- Pointwise subtyping on struct fields; field names agree pairwise. -/
inductive SubFields : List (String × Typ) → List (String × Typ) → Prop where
  | nil : SubFields [] []
  | cons {n : String} {a b : Typ} {fs fs' : List (String × Typ)} :
      Sub a b → SubFields fs fs' → SubFields ((n, a) :: fs) ((n, b) :: fs')
end

mutual
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
  | .tupleType ts, .tupleType ts' => isSubtypeList ts ts'
  | (.tupleType _), _ => false
  | .structType nm fs, .structType nm' fs' =>
      decide (nm = nm') && isSubtypeFields fs fs'
  | (.structType _ _), _ => false
  | .refType c a, .refType d b => decide (c = d) && Morph.Specs.TypeSystem.eqTyp a b
  | (.refType _ _), _ => false
  | t, s => Morph.Specs.TypeSystem.eqTyp t s

/-- Pointwise decision for tuple elements. -/
def isSubtypeList : List Typ → List Typ → Bool
  | [], [] => true
  | a :: as, b :: bs => isSubtype a b && isSubtypeList as bs
  | _, _ => false

/-- Pointwise decision for struct fields (names compared exactly). -/
def isSubtypeFields : List (String × Typ) → List (String × Typ) → Bool
  | [], [] => true
  | (n, a) :: fs, (n', b) :: fs' =>
      decide (n = n') && isSubtype a b && isSubtypeFields fs fs'
  | _, _ => false
end

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

/-- **Joint soundness** over types, tuple elements, and struct fields: the
decision procedure never accepts a non-subtype. -/
theorem sound_main : ∀ (fuel : Nat),
    (∀ τ σ : Typ, tS τ + tS σ ≤ fuel → isSubtype τ σ = true → Sub τ σ) ∧
    (∀ ts ts' : List Typ, tSl ts + tSl ts' ≤ fuel →
      isSubtypeList ts ts' = true → SubList ts ts') ∧
    (∀ fs fs' : List (String × Typ), tSlF fs + tSlF fs' ≤ fuel →
      isSubtypeFields fs fs' = true → SubFields fs fs') := by
  intro fuel
  refine Nat.strongRecOn (motive := fun fuel =>
    (∀ τ σ : Typ, tS τ + tS σ ≤ fuel → isSubtype τ σ = true → Sub τ σ) ∧
    (∀ ts ts' : List Typ, tSl ts + tSl ts' ≤ fuel →
      isSubtypeList ts ts' = true → SubList ts ts') ∧
    (∀ fs fs' : List (String × Typ), tSlF fs + tSlF fs' ≤ fuel →
      isSubtypeFields fs fs' = true → SubFields fs fs'))
    fuel (fun fuel' ih => ?_)
  refine ⟨?_, ?_, ?_⟩
  · intro τ σ hsize h
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
            simp only [isSubtype, Bool.and_eq_true] at h
            obtain ⟨hnm, hfields⟩ := h
            have hnm' : name = name' := of_decide_eq_true hnm
            subst hnm'
            have hle : tSlF fields + tSlF fields' < fuel' := by
              have h2 := hsize
              have h3 : tSlF fields + 1 + (tSlF fields' + 1) ≤ fuel' := by
                simpa [Morph.Specs.TypeSystem.tS] using h2
              omega
            exact Sub.struct ((ih _ hle).2.2 _ _ (by omega) hfields)
        | _ =>
            simp [isSubtype] at h
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
            simp only [isSubtype] at h
            have hle : tSl ts + tSl ts' < fuel' := by
              have h2 := hsize
              have h3 : tSl ts + 1 + (tSl ts' + 1) ≤ fuel' := by
                simpa [Morph.Specs.TypeSystem.tS] using h2
              omega
            exact Sub.tuple ((ih _ hle).2.1 _ _ (by omega) h)
        | _ =>
            simp [isSubtype] at h
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
            exact Sub.option ((ih _ hle).1 _ _ (by omega) h)
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
              ((ih _ hle1).1 _ _ (by omega) h1)
              ((ih _ hle2).1 _ _ (by omega) h2)
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
            exact Sub.array ((ih _ hle).1 _ _ (by omega) hsub)
        | _ =>
            simp [isSubtype] at h
  · intro ts ts' hsize h
    cases ts with
    | nil =>
        cases ts' with
        | nil => exact SubList.nil
        | cons _ _ => simp [isSubtypeList] at h
    | cons a as =>
        cases ts' with
        | nil => simp [isSubtypeList] at h
        | cons b bs =>
            simp only [isSubtypeList, Bool.and_eq_true] at h
            obtain ⟨hab, htail⟩ := h
            have e1 : tSl (a :: as) = tS a + tSl as + 1 := tSl.eq_2 _ _
            have e2 : tSl (b :: bs) = tS b + tSl bs + 1 := tSl.eq_2 _ _
            have hmT : tS a + tS b < fuel' := by omega
            have hmL : tSl as + tSl bs < fuel' := by omega
            exact SubList.cons ((ih _ hmT).1 _ _ (by omega) hab)
              ((ih _ hmL).2.1 _ _ (by omega) htail)
  · intro fs fs' hsize h
    cases fs with
    | nil =>
        cases fs' with
        | nil => exact SubFields.nil
        | cons _ _ => simp [isSubtypeFields] at h
    | cons p ps =>
        cases fs' with
        | nil => simp [isSubtypeFields] at h
        | cons q qs =>
            obtain ⟨n, a⟩ := p
            obtain ⟨n', b⟩ := q
            simp only [isSubtypeFields, Bool.and_eq_true] at h
            obtain ⟨⟨hnm, hab⟩, htail⟩ := h
            have hnm' : n = n' := of_decide_eq_true hnm
            subst hnm'
            have e1 : tSlF ((n, a) :: ps) = tS a + tSlF ps + 1 := tSlF.eq_2 _ _ _
            have e2 : tSlF ((n, b) :: qs) = tS b + tSlF qs + 1 := tSlF.eq_2 _ _ _
            have hmT : tS a + tS b < fuel' := by omega
            have hmL : tSlF ps + tSlF qs < fuel' := by omega
            exact SubFields.cons ((ih _ hmT).1 _ _ (by omega) hab)
              ((ih _ hmL).2.2 _ _ (by omega) htail)

/-- **Soundness.** The decision procedure never accepts a non-subtype. -/
theorem isSubtype_sound : ∀ (τ σ : Typ), isSubtype τ σ = true → Sub τ σ :=
  fun τ σ h => (sound_main (tS τ + tS σ)).1 τ σ (Nat.le_refl _) h

/-- **Soundness, tuple elements.** -/
theorem isSubtypeList_sound (as bs : List Typ)
    (h : isSubtypeList as bs = true) : SubList as bs :=
  (sound_main (tSl as + tSl bs)).2.1 as bs (Nat.le_refl _) h

/-- **Soundness, struct fields.** -/
theorem isSubtypeFields_sound (fs fs' : List (String × Typ))
    (h : isSubtypeFields fs fs' = true) : SubFields fs fs' :=
  (sound_main (tSlF fs + tSlF fs')).2.2 fs fs' (Nat.le_refl _) h

/-- `neverType` is below every type. -/
theorem isSubtype_never (σ : Typ) : isSubtype .neverType σ = true := by
  cases σ <;> rfl

/-- `unitType` is above every type. -/
theorem isSubtype_unit (τ : Typ) : isSubtype τ .unitType = true := by
  cases τ <;> rfl

/-- Joint reflexivity over types, tuple elements, and struct fields. -/
theorem refl_main : ∀ (fuel : Nat),
    (∀ τ : Typ, tS τ ≤ fuel → isSubtype τ τ = true) ∧
    (∀ ts : List Typ, tSl ts ≤ fuel → isSubtypeList ts ts = true) ∧
    (∀ fs : List (String × Typ), tSlF fs ≤ fuel →
      isSubtypeFields fs fs = true) := by
  intro fuel
  refine Nat.strongRecOn (motive := fun fuel =>
    (∀ τ : Typ, tS τ ≤ fuel → isSubtype τ τ = true) ∧
    (∀ ts : List Typ, tSl ts ≤ fuel → isSubtypeList ts ts = true) ∧
    (∀ fs : List (String × Typ), tSlF fs ≤ fuel →
      isSubtypeFields fs fs = true))
    fuel (fun fuel' ih => ?_)
  refine ⟨?_, ?_, ?_⟩
  · intro τ hle
    cases τ with
    | neverType => simp only [isSubtype]
    | unitType => simp only [isSubtype]
    | intType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | boolType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | stringType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | pointerType => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | intWidthType w => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | floatType w => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | typeVar n => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | refType c a => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | optionType a =>
        have hm : tS a < fuel' := by
          have h2 := hle
          have h3 : tS a + 1 ≤ fuel' := by
            simpa [Morph.Specs.TypeSystem.tS] using h2
          omega
        have e : isSubtype a a = true := (ih _ hm).1 a (Nat.le_refl _)
        simp [isSubtype, e]
    | resultType a b =>
        have hm1 : tS a < fuel' := by
          have h2 := hle
          have h3 : tS a + tS b + 1 ≤ fuel' := by
            simpa [Morph.Specs.TypeSystem.tS] using h2
          omega
        have hm2 : tS b < fuel' := by
          have h2 := hle
          have h3 : tS a + tS b + 1 ≤ fuel' := by
            simpa [Morph.Specs.TypeSystem.tS] using h2
          omega
        have e1 : isSubtype a a = true := (ih _ hm1).1 a (Nat.le_refl _)
        have e2 : isSubtype b b = true := (ih _ hm2).1 b (Nat.le_refl _)
        simp [isSubtype, e1, e2]
    | arrayType a n =>
        have hm : tS a < fuel' := by
          have h2 := hle
          have h3 : tS a + 1 ≤ fuel' := by
            simpa [Morph.Specs.TypeSystem.tS] using h2
          omega
        have e : isSubtype a a = true := (ih _ hm).1 a (Nat.le_refl _)
        simp [isSubtype, e]
    | tupleType ts =>
        simp only [isSubtype]
        have hm : tSl ts < fuel' := by
          have h2 := hle
          have h3 : tSl ts + 1 ≤ fuel' := by
            simpa [Morph.Specs.TypeSystem.tS] using h2
          omega
        exact (ih _ hm).2.1 ts (Nat.le_refl _)
    | structType name fields =>
        have hm : tSlF fields < fuel' := by
          have h2 := hle
          have h3 : tSlF fields + 1 ≤ fuel' := by
            simpa [Morph.Specs.TypeSystem.tS] using h2
          omega
        have e : isSubtypeFields fields fields = true :=
          (ih _ hm).2.2 fields (Nat.le_refl _)
        simp [isSubtype, e]
    | functionType args ret => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
    | linearFunctionType args ret => simp [isSubtype, Morph.Specs.TypeSystem.eqTyp_iff]
  · intro ts hle
    cases ts with
    | nil => simp only [isSubtypeList]
    | cons a as =>
        have e : tSl (a :: as) = tS a + tSl as + 1 := tSl.eq_2 _ _
        have hmT : tS a < fuel' := by omega
        have hmL : tSl as < fuel' := by omega
        have e1 : isSubtype a a = true := (ih _ hmT).1 a (Nat.le_refl _)
        have e2 : isSubtypeList as as = true := (ih _ hmL).2.1 as (Nat.le_refl _)
        simp [isSubtypeList, e1, e2]
  · intro fs hle
    cases fs with
    | nil => simp only [isSubtypeFields]
    | cons p ps =>
        obtain ⟨n, a⟩ := p
        have e : tSlF ((n, a) :: ps) = tS a + tSlF ps + 1 := tSlF.eq_2 _ _ _
        have hmT : tS a < fuel' := by omega
        have hmL : tSlF ps < fuel' := by omega
        have e1 : isSubtype a a = true := (ih _ hmT).1 a (Nat.le_refl _)
        have e2 : isSubtypeFields ps ps = true := (ih _ hmL).2.2 ps (Nat.le_refl _)
        simp [isSubtypeFields, e1, e2]

/-- The decision procedure accepts every type against itself. -/
theorem isSubtype_refl : ∀ (τ : Typ), isSubtype τ τ = true :=
  fun τ => (refl_main (tS τ)).1 τ (Nat.le_refl _)

/-- Pointwise reflexivity, tuple elements. -/
theorem isSubtypeList_refl : ∀ (as : List Typ), isSubtypeList as as = true :=
  fun as => (refl_main (tSl as)).2.1 as (Nat.le_refl _)

/-- Pointwise reflexivity, struct fields. -/
theorem isSubtypeFields_refl : ∀ (fs : List (String × Typ)),
    isSubtypeFields fs fs = true :=
  fun fs => (refl_main (tSlF fs)).2.2 fs (Nat.le_refl _)

/-- The tuple case of completeness. -/
theorem sub_tuple_complete {ts ts' : List Typ} (_h : SubList ts ts')
    (ih : isSubtypeList ts ts' = true) :
    isSubtype (.tupleType ts) (.tupleType ts') = true := by
  simp [isSubtype, ih]

/-- The struct case of completeness. -/
theorem sub_struct_complete {nm : String} {fs fs' : List (String × Typ)}
    (_h : SubFields fs fs') (ih : isSubtypeFields fs fs' = true) :
    isSubtype (.structType nm fs) (.structType nm fs') = true := by
  simp [isSubtype, ih]

/-- The list-cons case of completeness. -/
theorem subList_cons_complete {a b : Typ} {as bs : List Typ}
    (ih1 : isSubtype a b = true) (ih2 : isSubtypeList as bs = true) :
    isSubtypeList (a :: as) (b :: bs) = true := by
  simp [isSubtypeList, ih1, ih2]

/-- The fields-cons case of completeness. -/
theorem subFields_cons_complete {n : String} {a b : Typ}
    {fs fs' : List (String × Typ)}
    (ih1 : isSubtype a b = true) (ih2 : isSubtypeFields fs fs' = true) :
    isSubtypeFields ((n, a) :: fs) ((n, b) :: fs') = true := by
  simp [isSubtypeFields, ih1, ih2]

/-- **Completeness.** The decision procedure never rejects a subtype — via
the generated mutual recursor, as in loop 70. -/
theorem isSubtype_complete : ∀ {τ σ : Typ}, Sub τ σ → isSubtype τ σ = true :=
  fun {τ σ} h =>
  Sub.rec (motive_1 := fun τ σ _ => isSubtype τ σ = true)
    (motive_2 := fun ts ts' _ => isSubtypeList ts ts' = true)
    (motive_3 := fun fs fs' _ => isSubtypeFields fs fs' = true)
    (fun τ => isSubtype_refl τ)
    (fun τ => isSubtype_never τ)
    (fun τ => isSubtype_unit τ)
    (fun _ ih => by simp [isSubtype, ih])
    (fun _ _ ih1 ih2 => by simp [isSubtype, ih1, ih2])
    (fun _ ih => by simp [isSubtype, ih])
    (fun h ih => sub_tuple_complete h ih)
    (fun h ih => sub_struct_complete h ih)
    (by simp only [isSubtypeList])
    (fun _ _ ih1 ih2 => subList_cons_complete ih1 ih2)
    (by simp only [isSubtypeFields])
    (fun _ _ ih1 ih2 => subFields_cons_complete ih1 ih2)
    h

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

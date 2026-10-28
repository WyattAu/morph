/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.Subtyping.Spec

/-!
# Subtyping lemmas: exactness, variance, and the missing function rule

Research loop 50 (continuation of loop 12, SG-005).

**Research basis.**
- Pierce POPL'92 (F-sub undecidability): full function contravariance +
  bounded quantification is undecidable; Morph avoids the former by
  staying rank-1.
- Kennedy-Pierce FOOL-WOOD'07 (variance): C# declaration-site variance is
  sound only with explicit `in`/`out`; use-site variance needs capture.
- Brandt-Henglein TLCA'97 (coinductive subtyping): function subtyping is
  the coinductive closure of the structural rules.
- Kozen-Palsberg-Schwartzbach POPL'93: semantic subtyping via set inclusion.
- Julia Belyakova et al. PLDI'24 (decidable subtyping for Julia
  existentials): decidability via restricted grammar + fuel measure —
  the same shape as `tS` here.
- Castagna 2024-25 set-theoretic wave: semantic subtyping with
  intersection/negation; Morph has neither, so syntactic subtyping suffices.

**Language comparison.**
- Rust (`rustc` variance): functions are contravariant in args, covariant
  in return; checked by the variance engine, mechanized in RustBelt
  (safety only, no growth bounds).
- TypeScript: function bivariance for methods (unsound by design for
  usability); Morph refuses this — exactness is sound but incomplete.
- OCaml: row polymorphism + variance annotations; needs explicit
  declarations Morph does not have.
- Linear Haskell / Granule: arrow subtyping refused (Linear Haskell) or
  mediated by SMT grades (Granule); Morph's `linearFunctionType` is
  exact for the same reason — variance needs a grade algebra.
- F*: SMT-discharged subtyping; Morph stays structural so `isSubtype`
  is total without a solver.

**What is proved here.**
Function and linear-function types are currently compared *exactly*
(no variance). This is sound (equality implies subtyping) but
incomplete by design. The missing contravariant rule needs a list
relation mutually inductive with `Sub`, which core Lean's `induction`
does not support — so completeness for functions needs a
hand-written mutual recursor or a further measure argument. Done in the
Loop 70 section below: `SubV`/`SubListV` internalize variance to arbitrary
depth, decided by `isSubV`/`isSubListV`, complete via `SubV.rec`.
-/

namespace Morph.Specs.Subtyping

open Morph.Core Morph.Syntax Morph.Specs.TypeSystem

/-- Function types are compared exactly: `isSubtype` falls through to `eqTyp`. -/
theorem isSubtype_function_eq (args args' : List Typ) (ret ret' : Typ) :
    isSubtype (Typ.functionType args ret) (Typ.functionType args' ret') =
      eqTyp (Typ.functionType args ret) (Typ.functionType args' ret') := by
  simp only [isSubtype]

/-- Linear-function types are compared exactly. -/
theorem isSubtype_linearFunction_eq (args args' : List Typ) (ret ret' : Typ) :
    isSubtype (Typ.linearFunctionType args ret) (Typ.linearFunctionType args' ret') =
      eqTyp (Typ.linearFunctionType args ret) (Typ.linearFunctionType args' ret') := by
  simp only [isSubtype]

/-- Exact function subtyping implies equality of the whole type. -/
theorem function_subtype_eq {args args' : List Typ} {ret ret' : Typ}
    (h : isSubtype (Typ.functionType args ret) (Typ.functionType args' ret') = true) :
    (Typ.functionType args ret) = (Typ.functionType args' ret') := by
  rw [isSubtype_function_eq] at h
  exact (eqTyp_iff _ _).mp h

/-- Exact linear-function subtyping implies equality. -/
theorem linearFunction_subtype_eq {args args' : List Typ} {ret ret' : Typ}
    (h : isSubtype (Typ.linearFunctionType args ret) (Typ.linearFunctionType args' ret') = true) :
    (Typ.linearFunctionType args ret) = (Typ.linearFunctionType args' ret') := by
  rw [isSubtype_linearFunction_eq] at h
  exact (eqTyp_iff _ _).mp h

/-- Equality is sufficient for function subtyping (soundness direction). -/
theorem function_eq_subtype {args args' : List Typ} {ret ret' : Typ}
    (h : (Typ.functionType args ret) = (Typ.functionType args' ret')) :
    Sub (Typ.functionType args ret) (Typ.functionType args' ret') := by
  cases h
  exact Sub.refl _

/-- `Sub` is reflexive (witnessed by the decision procedure). -/
theorem sub_refl_dec (τ : Typ) : isSubtype τ τ = true :=
  isSubtype_refl τ

/-- Bottom/top are extremal through the decision procedure. -/
theorem sub_never_dec (τ : Typ) : isSubtype .neverType τ = true :=
  isSubtype_never τ

theorem sub_unit_dec (τ : Typ) : isSubtype τ .unitType = true :=
  isSubtype_unit τ

/-! ## Loop 61: contravariant function subtyping (additive extension)

Research basis: Pierce F-sub (undecidable with bounded quantification +
full variance — Morph stays rank-1, so the rule below is decidable);
Kennedy–Pierce FOOL-WOOD'07 (use-site variance needs explicit
contravariant positions); Brandt–Henglein TLCA'97 (function subtyping as
the coinductive closure of structural rules); Belyakova et al. PLDI'24
(decidability via restricted grammar + measure — same shape as `tS`).

Language comparison: Rust (`rustc` variance engine: args contravariant,
return covariant); TypeScript (method bivariance — unsound by design,
Morph refuses it); OCaml (variance annotations required); Linear Haskell
(arrow variance refused); F* (SMT-discharged).

`Sub` in `Spec.lean` compares functions *exactly* (sound but incomplete).
Changing the inductive would invalidate `isSubtype_sound/complete`, so the
contravariant rule lives here as a conservative extension `SubX`:
every `Sub` derivation embeds via `.ofSub`, and the new `.func`/`.linfunc`
rules add exactly contravariant-args + covariant-return. `isSubtypeFun`
decides it by delegating non-function pairs to the shipped `isSubtype`.
Loop 70 internalizes this to arbitrary depth; the wiring section at the
end of this file (`SubX.toSubV`, `isSubtypeFun_le_isSubV`) shows every
loop-61 acceptance is a loop-70 acceptance.
-/

/-- `Sub` plus contravariant function rules. -/
inductive SubX : Typ → Typ → Prop where
  | ofSub {τ σ : Typ} : Sub τ σ → SubX τ σ
  | func {args args' : List Typ} {ret ret' : Typ} :
      SubList args' args → SubX ret ret' →
      SubX (.functionType args ret) (.functionType args' ret')
  | linfunc {args args' : List Typ} {ret ret' : Typ} :
      SubList args' args → SubX ret ret' →
      SubX (.linearFunctionType args ret) (.linearFunctionType args' ret')

/-- Decision procedure for the extension: functions get variance,
everything else falls through to the shipped `isSubtype`.
Nested single matches (rather than a pair match) so the equation compiler
generates a clean splitter for the `split` tactic. -/
def isSubtypeFun (τ σ : Typ) : Bool :=
  match τ with
  | .functionType args ret =>
    match σ with
    | .functionType args' ret' =>
      (args.length == args'.length) &&
        isSubtypeList args' args && isSubtype ret ret'
    | _ => isSubtype τ σ
  | .linearFunctionType args ret =>
    match σ with
    | .linearFunctionType args' ret' =>
      (args.length == args'.length) &&
        isSubtypeList args' args && isSubtype ret ret'
    | _ => isSubtype τ σ
  | _ => isSubtype τ σ

theorem SubX.refl (τ : Typ) : SubX τ τ :=
  .ofSub (.refl τ)

theorem SubX.of_never (τ : Typ) : SubX .neverType τ :=
  .ofSub (.never τ)

theorem SubX.to_unit (τ : Typ) : SubX τ .unitType :=
  .ofSub (.unit τ)

/-- Soundness of the extended decision procedure. -/
theorem isSubtypeFun_sound (τ σ : Typ) (h : isSubtypeFun τ σ = true) :
    SubX τ σ := by
  revert h
  cases τ with
  | functionType args ret =>
    simp only [isSubtypeFun]
    split
    · intro h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨_, hargs⟩, hret⟩ := h
      have harg : SubList _ _ := isSubtypeList_sound _ _ hargs
      have hret' : Sub _ _ := isSubtype_sound _ _ hret
      exact .func harg (.ofSub hret')
    · intro h
      exact .ofSub (isSubtype_sound _ _ h)
  | linearFunctionType args ret =>
    simp only [isSubtypeFun]
    split
    · intro h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨_, hargs⟩, hret⟩ := h
      have harg : SubList _ _ := isSubtypeList_sound _ _ hargs
      have hret' : Sub _ _ := isSubtype_sound _ _ hret
      exact .linfunc harg (.ofSub hret')
    · intro h
      exact .ofSub (isSubtype_sound _ _ h)
  | _ =>
    cases σ with
    | functionType args' ret' =>
      intro h
      exact .ofSub (isSubtype_sound _ _ h)
    | linearFunctionType args' ret' =>
      intro h
      exact .ofSub (isSubtype_sound _ _ h)
    | _ =>
      intro h
      exact .ofSub (isSubtype_sound _ _ h)

/-- The old procedure embeds: every acceptance is still accepted. -/
theorem isSubtypeFun_extends (τ σ : Typ) (h : isSubtype τ σ = true) :
    isSubtypeFun τ σ = true := by
  revert h
  cases τ with
  | functionType args ret =>
    simp only [isSubtypeFun]
    split
    · intro h
      cases function_subtype_eq h
      simp only [beq_self_eq_true, Bool.true_and,
        isSubtypeList_refl, isSubtype_refl]
    · intro h
      exact h
  | linearFunctionType args ret =>
    simp only [isSubtypeFun]
    split
    · intro h
      cases linearFunction_subtype_eq h
      simp only [beq_self_eq_true, Bool.true_and,
        isSubtypeList_refl, isSubtype_refl]
    · intro h
      exact h
  | _ =>
    cases σ with
    | functionType args' ret' =>
      intro h
      exact h
    | linearFunctionType args' ret' =>
      intro h
      exact h
    | _ =>
      intro h
      exact h

/-- Headline contravariance witness: `never <: int`, so
`(int → unit) <: (never → unit)` — the exact case the old procedure
rejected (it compared function types by equality). -/
example : isSubtypeFun
    (.functionType [.intType] .unitType)
    (.functionType [.neverType] .unitType) = true := rfl

example : SubX
    (.functionType [.intType] .unitType)
    (.functionType [.neverType] .unitType) :=
  isSubtypeFun_sound _ _ rfl

/-- The old procedure rejects that pair (exact comparison). -/
example : isSubtype
    (.functionType [.intType] .unitType)
    (.functionType [.neverType] .unitType) = false := rfl

/-! ## Loop 70: fully-variant internalization (mutual inductive + recursor)

Loop 61's `SubX`/`SubList` is one level deep: `SubList.cons` carries the
shipped `Sub` (exact on functions) and `isSubtypeFun` delegates returns to
the shipped `isSubtype`. Nested variance — e.g.
`((never → unit) → unit) <: ((int → unit) → unit)` — is accepted by neither.
Full internalization makes the list relation carry the *extended* relation,
which is genuinely mutual (`SubV` via `SubListV` via `SubV`). Core Lean's
`induction` tactic does not do mutual induction, so completeness below is
proved by applying the generated mutual recursor `SubV.rec` directly with
explicit motives — the hand-written mutual recursor loops 50/61 called for.
-/

mutual
/-- Subtyping with full function contravariance at every depth. -/
inductive SubV : Typ → Typ → Prop where
  | ofSub {τ σ : Typ} : Sub τ σ → SubV τ σ
  | func {args args' : List Typ} {ret ret' : Typ} :
      SubListV args' args → SubV ret ret' →
      SubV (.functionType args ret) (.functionType args' ret')
  | linfunc {args args' : List Typ} {ret ret' : Typ} :
      SubListV args' args → SubV ret ret' →
      SubV (.linearFunctionType args ret) (.linearFunctionType args' ret')
/-- Pointwise full-variance subtyping on parameter lists. -/
inductive SubListV : List Typ → List Typ → Prop where
  | nil : SubListV [] []
  | cons {a b : Typ} {as bs : List Typ} :
      SubV a b → SubListV as bs → SubListV (a :: as) (b :: bs)
end

/-- Every type has positive size. -/
theorem tS_pos (τ : Typ) : 0 < tS τ := by
  cases τ <;> simp [tS] <;> omega

mutual
/-- Decision procedure with full variance: returns recurse into `isSubV`.
Termination is by `tS` measure: every recursive call is on strictly smaller
types (`simp [tS, tSl]` exposes the `+ 1`s, `omega` finishes). -/
def isSubV : Typ → Typ → Bool
  | .neverType, _ => true
  | _, .unitType => true
  | .functionType args ret, .functionType args' ret' =>
      decide (args.length = args'.length) && isSubListV args' args &&
        isSubV ret ret'
  | .linearFunctionType args ret, .linearFunctionType args' ret' =>
      decide (args.length = args'.length) && isSubListV args' args &&
        isSubV ret ret'
  | τ, σ => isSubtype τ σ
termination_by τ σ => tS τ + tS σ
decreasing_by all_goals simp only [tS.eq_2, tS.eq_3]; all_goals omega
/-- Pointwise decision for parameter lists. -/
def isSubListV : List Typ → List Typ → Bool
  | [], [] => true
  | a :: as, b :: bs => isSubV a b && isSubListV as bs
  | _, _ => false
termination_by as bs => tSl as + tSl bs
decreasing_by all_goals simp only [tSl.eq_2]; all_goals omega
end

/-! ### Reflexivity, length, completeness, soundness for `SubV` -/

/-- Joint reflexivity, by strong induction on the size measure. -/
theorem subV_refl_pair : ∀ (n : Nat),
    (∀ τ : Typ, tS τ ≤ n → isSubV τ τ = true) ∧
    (∀ as : List Typ, tSl as ≤ n → isSubListV as as = true) := by
  intro n
  refine Nat.strongRecOn (motive := fun n =>
    (∀ τ : Typ, tS τ ≤ n → isSubV τ τ = true) ∧
    (∀ as : List Typ, tSl as ≤ n → isSubListV as as = true)) n (fun n ih => ?_)
  constructor
  · intro τ hle
    cases τ with
    | neverType => simp only [isSubV]
    | functionType args ret =>
      have e : tS (.functionType args ret) = tSl args + tS ret + 1 := tS.eq_2 _ _
      have hp := tS_pos ret
      have hL : tSl args < n := by omega
      have hR : tS ret < n := by omega
      have eL := (ih _ hL).2 args (Nat.le_refl _)
      have eR := (ih _ hR).1 ret (Nat.le_refl _)
      simp [isSubV, eL, eR]
    | linearFunctionType args ret =>
      have e : tS (.linearFunctionType args ret) = tSl args + tS ret + 1 := tS.eq_3 _ _
      have hp := tS_pos ret
      have hL : tSl args < n := by omega
      have hR : tS ret < n := by omega
      have eL := (ih _ hL).2 args (Nat.le_refl _)
      have eR := (ih _ hR).1 ret (Nat.le_refl _)
      simp [isSubV, eL, eR]
    | _ =>
      simp only [isSubV]
      all_goals exact isSubtype_complete (Sub.refl _)
  · intro as hle
    cases as with
    | nil => simp only [isSubListV]
    | cons a as =>
      have e : tSl (a :: as) = tS a + tSl as + 1 := tSl.eq_2 _ _
      have hp := tS_pos a
      have hT : tS a < n := by omega
      have hL : tSl as < n := by omega
      have e1 := (ih _ hT).1 a (Nat.le_refl _)
      have e2 := (ih _ hL).2 as (Nat.le_refl _)
      simp [isSubListV, e1, e2]

/-- `isSubV` is reflexive. -/
theorem isSubV_refl (τ : Typ) : isSubV τ τ = true :=
  (subV_refl_pair (tS τ)).1 τ (Nat.le_refl _)

/-- `isSubListV` is reflexive. -/
theorem isSubListV_refl (as : List Typ) : isSubListV as as = true :=
  (subV_refl_pair (tSl as)).2 as (Nat.le_refl _)

/-- `SubListV` derivations relate equal-length lists. -/
theorem subListV_length : ∀ {as bs : List Typ}, SubListV as bs → as.length = bs.length := by
  intro as bs h
  induction as generalizing bs with
  | nil => cases h; rfl
  | cons a as ih =>
    cases h with
    | cons _ ht => simp only [List.length_cons, ih ht]

/-- The `ofSub` case of completeness: the shipped relation embeds. -/
theorem sub_ofSub_complete {τ σ : Typ} (s : Sub τ σ) : isSubV τ σ = true := by
  cases s with
  | refl τ => exact isSubV_refl τ
  | never _ => simp only [isSubV]
  | unit τ =>
    cases τ with
    | neverType => simp only [isSubV]
    | _ => simp only [isSubV]
  | option h => simpa only [isSubV] using isSubtype_complete (Sub.option h)
  | result h1 h2 => simpa only [isSubV] using isSubtype_complete (Sub.result h1 h2)
  | array h => simpa only [isSubV] using isSubtype_complete (Sub.array h)
  | tuple h => simpa only [isSubV] using isSubtype_complete (Sub.tuple h)
  | struct h => simpa only [isSubV] using isSubtype_complete (Sub.struct h)

/-- The function case of completeness (contravariant parameters). -/
theorem subV_func_complete {args args' : List Typ} {ret ret' : Typ}
    (hl : SubListV args' args) (_hr : SubV ret ret')
    (ihl : isSubListV args' args = true) (ihr : isSubV ret ret' = true) :
    isSubV (.functionType args ret) (.functionType args' ret') = true := by
  have hlen : args.length = args'.length := (subListV_length hl).symm
  simp [isSubV, hlen, ihl, ihr]

/-- The linear-function case of completeness. -/
theorem subV_linfunc_complete {args args' : List Typ} {ret ret' : Typ}
    (hl : SubListV args' args) (_hr : SubV ret ret')
    (ihl : isSubListV args' args = true) (ihr : isSubV ret ret' = true) :
    isSubV (.linearFunctionType args ret) (.linearFunctionType args' ret') = true := by
  have hlen : args.length = args'.length := (subListV_length hl).symm
  simp [isSubV, hlen, ihl, ihr]

/-- The cons case of completeness. -/
theorem subListV_cons_complete {a b : Typ} {as bs : List Typ}
    (ih1 : isSubV a b = true) (ih2 : isSubListV as bs = true) :
    isSubListV (a :: as) (b :: bs) = true := by
  simp [isSubListV, ih1, ih2]

/-- **Completeness.** Every `SubV` derivation is accepted by `isSubV`, via
the generated mutual recursor — the hand-written mutual recursion that loops
50/61 called for. -/
theorem isSubV_complete {τ σ : Typ} (h : SubV τ σ) : isSubV τ σ = true :=
  SubV.rec (motive_1 := fun τ σ _ => isSubV τ σ = true)
    (motive_2 := fun as bs _ => isSubListV as bs = true)
    (fun s => sub_ofSub_complete s)
    (fun hl hr ihl ihr => subV_func_complete hl hr ihl ihr)
    (fun hl hr ihl ihr => subV_linfunc_complete hl hr ihl ihr)
    (by simp only [isSubListV])
    (fun _ _ ih1 ih2 => subListV_cons_complete ih1 ih2)
    h

/-- **Completeness, list side.** Every `SubListV` derivation is accepted by
`isSubListV`. -/
theorem isSubListV_complete {as bs : List Typ} (h : SubListV as bs) :
    isSubListV as bs = true :=
  SubListV.rec (motive_1 := fun τ σ _ => isSubV τ σ = true)
    (motive_2 := fun as bs _ => isSubListV as bs = true)
    (fun s => sub_ofSub_complete s)
    (fun hl hr ihl ihr => subV_func_complete hl hr ihl ihr)
    (fun hl hr ihl ihr => subV_linfunc_complete hl hr ihl ihr)
    (by simp only [isSubListV])
    (fun _ _ ih1 ih2 => subListV_cons_complete ih1 ih2)
    h

/-- Joint soundness, by strong induction on the size measure. -/
theorem subV_sound_pair : ∀ (n : Nat),
    (∀ τ σ : Typ, tS τ + tS σ ≤ n → isSubV τ σ = true → SubV τ σ) ∧
    (∀ as bs : List Typ, tSl as + tSl bs ≤ n → isSubListV as bs = true → SubListV as bs) := by
  intro n
  refine Nat.strongRecOn (motive := fun n =>
    (∀ τ σ : Typ, tS τ + tS σ ≤ n → isSubV τ σ = true → SubV τ σ) ∧
    (∀ as bs : List Typ, tSl as + tSl bs ≤ n → isSubListV as bs = true → SubListV as bs))
    n (fun n ih => ?_)
  constructor
  · intro τ σ hsize h
    cases τ with
    | neverType => exact SubV.ofSub (Sub.never _)
    | functionType args ret =>
      cases σ with
      | functionType args' ret' =>
        simp only [isSubV, Bool.and_eq_true] at h
        obtain ⟨⟨_, hlist⟩, hret⟩ := h
        have e1 : tS (.functionType args ret) = tSl args + tS ret + 1 := tS.eq_2 _ _
        have e2 : tS (.functionType args' ret') = tSl args' + tS ret' + 1 := tS.eq_2 _ _
        have hmL : tSl args' + tSl args < n := by omega
        have hmR : tS ret + tS ret' < n := by omega
        exact SubV.func ((ih _ hmL).2 _ _ (Nat.le_refl _) hlist) ((ih _ hmR).1 _ _ (Nat.le_refl _) hret)
      | unitType => exact SubV.ofSub (Sub.unit _)
      | _ => exact SubV.ofSub (isSubtype_sound _ _ (by simpa only [isSubV] using h))
    | linearFunctionType args ret =>
      cases σ with
      | linearFunctionType args' ret' =>
        simp only [isSubV, Bool.and_eq_true] at h
        obtain ⟨⟨_, hlist⟩, hret⟩ := h
        have e1 : tS (.linearFunctionType args ret) = tSl args + tS ret + 1 := tS.eq_3 _ _
        have e2 : tS (.linearFunctionType args' ret') = tSl args' + tS ret' + 1 := tS.eq_3 _ _
        have hmL : tSl args' + tSl args < n := by omega
        have hmR : tS ret + tS ret' < n := by omega
        exact SubV.linfunc ((ih _ hmL).2 _ _ (Nat.le_refl _) hlist) ((ih _ hmR).1 _ _ (Nat.le_refl _) hret)
      | unitType => exact SubV.ofSub (Sub.unit _)
      | _ => exact SubV.ofSub (isSubtype_sound _ _ (by simpa only [isSubV] using h))
    | _ =>
      cases σ with
      | unitType => exact SubV.ofSub (Sub.unit _)
      | _ => exact SubV.ofSub (isSubtype_sound _ _ (by simpa only [isSubV] using h))
  · intro as bs hsize h
    cases as with
    | nil =>
      cases bs with
      | nil => exact SubListV.nil
      | cons _ _ => simp [isSubListV] at h
    | cons a as =>
      cases bs with
      | nil => simp [isSubListV] at h
      | cons b bs =>
        simp only [isSubListV, Bool.and_eq_true] at h
        obtain ⟨hab, htail⟩ := h
        have e1 : tSl (a :: as) = tS a + tSl as + 1 := tSl.eq_2 _ _
        have e2 : tSl (b :: bs) = tS b + tSl bs + 1 := tSl.eq_2 _ _
        have hmT : tS a + tS b < n := by omega
        have hmL : tSl as + tSl bs < n := by omega
        exact SubListV.cons ((ih _ hmT).1 _ _ (Nat.le_refl _) hab) ((ih _ hmL).2 _ _ (Nat.le_refl _) htail)

/-- **Soundness.** `isSubV` accepts only genuine `SubV` derivations. -/
theorem isSubV_sound {τ σ : Typ} (h : isSubV τ σ = true) : SubV τ σ :=
  (subV_sound_pair (tS τ + tS σ)).1 τ σ (Nat.le_refl _) h

/-- **Soundness, list side.** -/
theorem isSubListV_sound {as bs : List Typ} (h : isSubListV as bs = true) : SubListV as bs :=
  (subV_sound_pair (tSl as + tSl bs)).2 as bs (Nat.le_refl _) h

/-! ## Loop 61 ⟶ Loop 70 wiring: every one-level acceptance is a full one

`SubX.toSubV` / `isSubtypeFun_le_isSubV` retire the loop-61 extension:
anything it derives or accepts, `SubV` / `isSubV` handle too. The nested
witness below is the payoff — one-level `SubX`/`isSubtypeFun` compare the
inner arrows exactly and reject it, while `isSubV` accepts.
-/

/-- `SubList` embeds pointwise into `SubListV` — via the generated mutual
recursor `Sub.rec`, since `SubList` is mutually inductive with `Sub` and
plain `induction` does not support mutual inductives. -/
theorem SubList.toSubListV {as bs : List Typ} (h : SubList as bs) : SubListV as bs :=
  SubList.rec (motive_1 := fun _ _ _ => True) (motive_2 := fun as bs _ => SubListV as bs)
    (motive_3 := fun _ _ _ => True)
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial)
    SubListV.nil
    (fun h1 _ _ ih => SubListV.cons (SubV.ofSub h1) ih)
    trivial
    (fun _ _ _ _ => trivial)
    h

/-- Every loop-61 `SubX` derivation is a loop-70 `SubV` derivation. -/
theorem SubX.toSubV {τ σ : Typ} (h : SubX τ σ) : SubV τ σ := by
  induction h with
  | ofSub s => exact SubV.ofSub s
  | func hl _ ihr => exact SubV.func hl.toSubListV ihr
  | linfunc hl _ ihr => exact SubV.linfunc hl.toSubListV ihr

/-- Every `isSubtypeFun` acceptance is an `isSubV` acceptance. -/
theorem isSubtypeFun_le_isSubV {τ σ : Typ} (h : isSubtypeFun τ σ = true) :
    isSubV τ σ = true :=
  isSubV_complete (SubX.toSubV (isSubtypeFun_sound _ _ h))

/-- Headline nested-variance witness, decided: inner arrows are compared
with full variance, so `((never → unit) → unit) <: ((int → unit) → unit)`. -/
example : isSubV
    (.functionType [.functionType [.neverType] .unitType] .unitType)
    (.functionType [.functionType [.intType] .unitType] .unitType) = true := by
  simp [isSubV, isSubListV]

/-- The one-level `isSubtypeFun` rejects the nested pair (inner arrows
compared exactly). -/
example : isSubtypeFun
    (.functionType [.functionType [.neverType] .unitType] .unitType)
    (.functionType [.functionType [.intType] .unitType] .unitType) = false := rfl

/-- So does the shipped `isSubtype`. -/
example : isSubtype
    (.functionType [.functionType [.neverType] .unitType] .unitType)
    (.functionType [.functionType [.intType] .unitType] .unitType) = false := rfl

/-- The loop-61 witness upgrades through the bridge. -/
example : isSubV
    (.functionType [.intType] .unitType)
    (.functionType [.neverType] .unitType) = true :=
  isSubtypeFun_le_isSubV rfl

/-- And relationally. -/
example : SubV
    (.functionType [.intType] .unitType)
    (.functionType [.neverType] .unitType) :=
  SubX.toSubV (isSubtypeFun_sound _ _ rfl)

/-- Same story for linear functions: nested variance is accepted. -/
example : isSubV
    (.linearFunctionType [.linearFunctionType [.neverType] .unitType] .unitType)
    (.linearFunctionType [.linearFunctionType [.intType] .unitType] .unitType) = true := by
  simp [isSubV, isSubListV]

/-- While the one-level and shipped procedures reject it. -/
example : isSubtypeFun
    (.linearFunctionType [.linearFunctionType [.neverType] .unitType] .unitType)
    (.linearFunctionType [.linearFunctionType [.intType] .unitType] .unitType) = false := rfl

example : isSubtype
    (.linearFunctionType [.linearFunctionType [.neverType] .unitType] .unitType)
    (.linearFunctionType [.linearFunctionType [.intType] .unitType] .unitType) = false := rfl

end Morph.Specs.Subtyping

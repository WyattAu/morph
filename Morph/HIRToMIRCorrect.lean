/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIR
import Morph.Frontend.HIREval
import Morph.Frontend.HIRInterp
import Morph.MIRExecLemmas

/-!
# Straight-line `compile_correct` bridge, stage A (loops 139+)

Expression-level bridge between `HIRToMIR.lowerExpr` and the two
interpreters: `HIREval.evalHIR` on the source side, `MIR.execInstrsFull`
on the target side. One-directional (D-2/D-4): whenever lowering
succeeds, both sides agree on the result value and the store stays put;
nothing is claimed in the other direction.

The environment relation `RelEnv henv ρ env` ties the HIR runtime
environment (`HIREval.HEnv`) to the MIR register file through the
lowering's `ρ` correspondence (first-match on both sides, exactly as
`rhoLookup` mirrors `lookupHEnv`).

Fuel. `evalHIR` is fuel-bounded; per-construct composition lifts each
sub-claim to a shared fuel via `evalHIR_mono` (fuel monotonicity,
restricted to the straight-line fragment `SLExpr`) plus the generic
`mapM_mono_pointwise` helper for block element lists.
-/

namespace Morph.HIRToMIRCorrect

open Morph.HIRToMIR Morph.MIR Morph.Frontend.HIREval Morph.Frontend.HIRInterp
open Morph.Core

/-! ## Operator coherence -/

/-- `toUnOp` succeeds only on MIR-unary operators, where `toOperator`
is the identity. -/
theorem toUnOp_toOperator (op : Operator) (u : UnOp) (h : toUnOp op = some u) :
    u.toOperator = op := by
  cases op with
  | not => cases h; rfl
  | notb => cases h; rfl
  | add => simp [toUnOp] at h
  | sub => simp [toUnOp] at h
  | mul => simp [toUnOp] at h
  | div => simp [toUnOp] at h
  | mod => simp [toUnOp] at h
  | eq => simp [toUnOp] at h
  | neq => simp [toUnOp] at h
  | lt => simp [toUnOp] at h
  | leq => simp [toUnOp] at h
  | gt => simp [toUnOp] at h
  | geq => simp [toUnOp] at h
  | and => simp [toUnOp] at h
  | or => simp [toUnOp] at h
  | andb => simp [toUnOp] at h
  | orb => simp [toUnOp] at h
  | xorb => simp [toUnOp] at h
  | shl => simp [toUnOp] at h
  | shr => simp [toUnOp] at h
  | ptrAdd => simp [toUnOp] at h
  | ptrSub => simp [toUnOp] at h
  | ptrLoad => simp [toUnOp] at h
  | ptrStore => simp [toUnOp] at h

/-- `toBinOp` succeeds only on MIR-binary operators, where `toOperator`
is the identity. -/
theorem toBinOp_toOperator (op : Operator) (b : BinOp) (h : toBinOp op = some b) :
    b.toOperator = op := by
  cases op with
  | add => cases h; rfl
  | sub => cases h; rfl
  | mul => cases h; rfl
  | div => cases h; rfl
  | mod => cases h; rfl
  | eq => cases h; rfl
  | neq => cases h; rfl
  | lt => cases h; rfl
  | leq => cases h; rfl
  | gt => cases h; rfl
  | geq => cases h; rfl
  | and => cases h; rfl
  | or => cases h; rfl
  | not => cases h; rfl
  | andb => cases h; rfl
  | orb => cases h; rfl
  | xorb => cases h; rfl
  | shl => cases h; rfl
  | shr => cases h; rfl
  | notb => simp [toBinOp] at h
  | ptrAdd => simp [toBinOp] at h
  | ptrSub => simp [toBinOp] at h
  | ptrLoad => simp [toBinOp] at h
  | ptrStore => simp [toBinOp] at h

/-! ## Unop / binop glue

`evalHIR` and the MIR-side operand run the *same* surface oracle —
`Executable.evalUnop`/`evalBinop` — on the same literal payload, so agreement
holds exactly when the lowering's operator projection picked the
corresponding MIR operator. -/

theorem evalUnop_glue (op : Operator) (u : UnOp) (v w : Value)
    (hto : toUnOp op = some u) :
    (MIR.evalUnOp u v = some w) ↔
      (Morph.Executable.evalUnop op (.lit v) = some (.lit w)) := by
  have hco := toUnOp_toOperator op u hto
  constructor
  · intro hmir
    simp only [MIR.evalUnOp] at hmir ⊢
    rw [hco] at hmir
    obtain ⟨a, ha1, ha2⟩ := bind_some_eq hmir
    cases a with
    | lit w' =>
        simp only [Option.some.injEq] at ha2
        rw [← ha2]
        exact ha1
    | _ => simp at ha2
  · intro hex
    simp only [MIR.evalUnOp]
    rw [hco, hex]
    simp

theorem evalBinop_glue (op : Operator) (b : BinOp) (v1 v2 w : Value)
    (hto : toBinOp op = some b) :
    (MIR.evalBinOp b v1 v2 = some w) ↔
      (Morph.Executable.evalBinop op (.lit v1) (.lit v2) = some (.lit w)) := by
  have hco := toBinOp_toOperator op b hto
  constructor
  · intro hmir
    simp only [MIR.evalBinOp] at hmir ⊢
    rw [hco] at hmir
    obtain ⟨a, ha1, ha2⟩ := bind_some_eq hmir
    cases a with
    | lit w' =>
        simp only [Option.some.injEq] at ha2
        rw [← ha2]
        exact ha1
    | _ => simp at ha2
  · intro hex
    simp only [MIR.evalBinOp]
    rw [hco, hex]
    simp

/-- One-step MIR execution of a lowered `unop` instruction, in the
register-update form the bridge composes with. -/
theorem evalInstrFull_unop_step (fenv : FullEnv) (dst : ValId)
    (u : UnOp) (src : ValId) (τ : Typ) :
    evalInstrFull fenv (.unop dst u src τ) =
      (do
        let v ← fenv.env src
        let r ← evalUnOp u v
        some ⟨(fenv.env).update dst r, fenv.store⟩) := rfl

/-- One-step MIR execution of a lowered `binop` instruction. -/
theorem evalInstrFull_binop_step (fenv : FullEnv) (dst : ValId)
    (b : BinOp) (l r : ValId) (τ : Typ) :
    evalInstrFull fenv (.binop dst b l r τ) =
      (do
        let vl ← fenv.env l
        let vr ← fenv.env r
        let v ← evalBinOp b vl vr
        some ⟨(fenv.env).update dst v, fenv.store⟩) := rfl

/-! ## The straight-line fragment -/

/-- The constructs the lowering handles. Restricting fuel monotonicity to
this fragment keeps the induction arms to the six shapes the bridge
actually composes (`app`/`lam`/`ifThenElse`/`whileLoop`/`match`/`infer`
all lower to `none` and need no arms). -/
def SLExpr : HIR.Expr → Prop
  | .var _ => True
  | .lit _ => True
  | .unop _ e => SLExpr e
  | .binop _ a b => SLExpr a ∧ SLExpr b
  | .«let» _ init body => SLExpr init ∧ SLExpr body
  | .block es => ∀ x ∈ es, SLExpr x
  | _ => False

theorem SLExpr_block_mem {es : List HIR.Expr} (hx : SLExpr (.block es))
    {x : HIR.Expr} (hmem : x ∈ es) : SLExpr x := by
  simp only [SLExpr] at hx
  exact hx x hmem

/-! ## Fuel monotonicity -/

/-- Membership from indexed access (`xs[i]? = some x` implies `x ∈ xs`). -/
theorem getElem?_to_mem {α : Type} (xs : List α) :
    ∀ (i : Nat) (x : α), xs[i]? = some x → x ∈ xs := by
  induction xs with
  | nil => intro i x hx; simp at hx
  | cons a rest ih =>
      intro i x hx
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact List.mem_cons_self
      | succ i' =>
          simp only [List.getElem?_cons_succ] at hx
          exact List.mem_cons_of_mem _ (ih i' x hx)

/-- Element-success agreement lifts to `List.mapM`: if the smaller-fuel
side succeeds on members with results that the larger-fuel side reproduces,
the whole `mapM` result agrees. Built on HIREval's `mapM_loop_pointwise` /
`mapM_loop_of_pointwise` gadgets; generic in `f`/`g` so it never leans on
`evalHIR_mono`, keeping the two lemmas independent. -/
theorem mapM_mono_pointwise {α β : Type} (f g : α → Option β) (xs : List α)
    (P : α → Prop) (vs : List β)
    (hs : ∀ x, x ∈ xs → P x)
    (h : ∀ x, P x → ∀ y, f x = some y → g x = some y)
    (hm : xs.mapM f = some vs) :
    xs.mapM g = some vs := by
  have hloop : xs.mapM f = List.mapM.loop f xs [] := rfl
  rw [hloop] at hm
  obtain ⟨zs, hlen, hpoint, hshape⟩ := mapM_loop_pointwise xs [] vs f hm
  have hvs : vs = zs := by rw [hshape]; simp
  subst hvs
  have hpoint' : ∀ (i : Nat) (x : α), xs[i]? = some x → ∃ y, vs[i]? = some y ∧ g x = some y := by
    intro i x hxa
    obtain ⟨y, hya, hfy⟩ := hpoint i x hxa
    exact ⟨y, hya, h x (hs x (getElem?_to_mem xs i x hxa)) y hfy⟩
  have hloop2 : xs.mapM g = List.mapM.loop g xs [] := rfl
  rw [hloop2, mapM_loop_of_pointwise xs [] vs g hlen hpoint']
  simp

/-- Fuel monotonicity of `evalHIR` on the straight-line fragment: running
with more fuel keeps the same successful result. Structural on the fuel
argument, mirroring the step-shapes of each fragment construct. -/
theorem evalHIR_mono (fuel : Nat) (m : Nat) (env : HEnv) (e : HIR.Expr)
    (r : HIR.Expr) (hle : fuel ≤ m) (hs : SLExpr e)
    (h : evalHIR fuel env e = some r) :
    evalHIR m env e = some r := by
  induction fuel generalizing m env e r with
  | zero => simp [evalHIR] at h
  | succ k ih =>
      cases m with
      | zero => omega
      | succ m' =>
        have hle' : k ≤ m' := Nat.le_of_succ_le_succ hle
        cases e with
        | var id => simp only [evalHIR] at h ⊢; exact h
        | lit v => simp only [evalHIR] at h ⊢; exact h
        | infer => simp [SLExpr] at hs h
        | lam params body => simp [SLExpr] at hs h
        | app fid args => simp [SLExpr] at hs h
        | ifThenElse c t f => simp [SLExpr] at hs h
        | whileLoop c body => simp [SLExpr] at hs h
        | «match» scrut arms => simp [SLExpr] at hs h
        | unop op e =>
            simp only [SLExpr] at hs
            simp only [evalHIR] at h ⊢
            obtain ⟨v, hv, hw⟩ := bind_some_eq h
            rw [ih m' env e v hle' hs hv]
            exact hw
        | binop op a b =>
            simp only [SLExpr] at hs
            obtain ⟨hsa, hsb⟩ := hs
            simp only [evalHIR] at h ⊢
            obtain ⟨va, hva, hmid⟩ := bind_some_eq h
            obtain ⟨vb, hvb, hw⟩ := bind_some_eq hmid
            rw [ih m' env a va hle' hsa hva, ih m' env b vb hle' hsb hvb]
            exact hw
        | «let» id init body =>
            simp only [SLExpr] at hs
            obtain ⟨hsi, hsb⟩ := hs
            simp only [evalHIR] at h ⊢
            obtain ⟨iv, hiv, hhb⟩ := bind_some_eq h
            rw [ih m' env init iv hle' hsi hiv]
            exact ih m' ((id, iv) :: env) body r hle' hsb hhb
        | block es =>
            simp only [SLExpr] at hs
            simp only [evalHIR] at h ⊢
            obtain ⟨vs, hmv, hpost⟩ := bind_some_eq h
            have hmono : es.mapM (evalHIR m' env) = some vs :=
              mapM_mono_pointwise (evalHIR k env) (evalHIR m' env) es SLExpr vs
                (fun x hmem => hs x hmem)
                (fun x hp y hxy => ih m' env x y hle' hp hxy)
                hmv
            rw [hmono]
            exact hpost

/-! ## Fuel budget: a structural weight bounds what `evalHIR` needs -/

/-
The statement runner `runHIRStmts` evaluates every expression position with
a fixed `evalHIR 256`, so the statement bridge cannot hand it an
unspecified fuel: it needs an expression-local budget that fits in 256.
`SLWeight` is that budget — one unit per construct plus the subterm
weights, so `.block` pays the sum of its elements (`mapM` walks them all
at one shared fuel level).
-/

/-- Structural weight of an expression, an upper bound on the number of
`evalHIR` steps beyond the caller's own fuel. -/
def SLWeight : HIR.Expr → Nat
  | .var _ => 1
  | .lit _ => 1
  | .unop _ e => SLWeight e + 1
  | .binop _ a b => SLWeight a + SLWeight b + 1
  | .«let» _ init body => SLWeight init + SLWeight body + 1
  | .block es => (es.map SLWeight).sum + 1
  | _ => 1

/-- Every element weighs at most the sum, so `block` is the most expensive
shape and its elements are strictly cheaper. -/
theorem le_sum_map_weight : ∀ {es : List HIR.Expr} {x : HIR.Expr},
    x ∈ es → SLWeight x ≤ (es.map SLWeight).sum := by
  intro es
  induction es with
  | nil => intro x hx; simp at hx
  | cons a rest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.map_cons, List.sum_cons]
        omega
      · have h := ih hx
        simp only [List.map_cons, List.sum_cons]
        omega

theorem one_le_SLWeight (e : HIR.Expr) : 1 ≤ SLWeight e := by
  cases e <;> simp only [SLWeight] <;> omega

/-- Budget: a straight-line expression that evaluates at all evaluates within
`SLWeight` units. Proved by induction on the budget (not on the successful
run's fuel): each subterm is strictly lighter, so the parent's remaining
budget covers it, and the existential "some fuel works" hypothesis is all the
subterms need. This is the direction the statement runner uses — it supplies
its own fixed fuel, so it needs a bound on what the expression can demand. -/
theorem evalHIR_budget : ∀ (n : Nat) (env : HEnv) (e : HIR.Expr) (r : HIR.Expr),
    SLWeight e ≤ n → SLExpr e → (∃ fuel, evalHIR fuel env e = some r) →
    evalHIR n env e = some r := by
  intro n
  induction n with
  | zero =>
      intro env e r hw _ _
      have h1 := one_le_SLWeight e
      omega
  | succ k ih =>
      intro env e r hw hs hsome
      obtain ⟨fuel, hfuel⟩ := hsome
      cases fuel with
      | zero => simp [evalHIR] at hfuel
      | succ fu =>
        cases e with
        | var id => simp only [evalHIR] at hfuel ⊢; exact hfuel
        | lit v => simp only [evalHIR] at hfuel ⊢; exact hfuel
        | infer => simp [SLExpr] at hs
        | lam params body => simp [SLExpr] at hs
        | app fid args => simp [SLExpr] at hs
        | ifThenElse c t f => simp [SLExpr] at hs
        | whileLoop c body => simp [SLExpr] at hs
        | «match» scrut arms => simp [SLExpr] at hs
        | unop op e =>
            simp only [SLExpr] at hs
            simp only [SLWeight] at hw
            simp only [evalHIR] at hfuel ⊢
            obtain ⟨v, hv, hw2⟩ := bind_some_eq hfuel
            have hsub : evalHIR k env e = some v := ih env e v (by omega) hs ⟨fu, hv⟩
            rw [hsub]
            exact hw2
        | binop op a b =>
            simp only [SLExpr] at hs
            obtain ⟨hsa, hsb⟩ := hs
            simp only [SLWeight] at hw
            simp only [evalHIR] at hfuel ⊢
            obtain ⟨va, hva, hmid⟩ := bind_some_eq hfuel
            obtain ⟨vb, hvb, hw2⟩ := bind_some_eq hmid
            have hva' : evalHIR k env a = some va := ih env a va (by omega) hsa ⟨fu, hva⟩
            have hvb' : evalHIR k env b = some vb := ih env b vb (by omega) hsb ⟨fu, hvb⟩
            rw [hva', hvb']
            exact hw2
        | «let» id init body =>
            simp only [SLExpr] at hs
            obtain ⟨hsi, hsb⟩ := hs
            simp only [SLWeight] at hw
            simp only [evalHIR] at hfuel ⊢
            obtain ⟨iv, hiv, hhb⟩ := bind_some_eq hfuel
            have hsub : evalHIR k env init = some iv := ih env init iv (by omega) hsi ⟨fu, hiv⟩
            rw [hsub]
            exact ih ((id, iv) :: env) body r (by omega) hsb ⟨fu, hhb⟩
        | block es =>
            simp only [SLExpr] at hs
            simp only [SLWeight] at hw
            simp only [evalHIR] at hfuel ⊢
            obtain ⟨vs, hmv, hpost⟩ := bind_some_eq hfuel
            have hmono : es.mapM (evalHIR k env) = some vs :=
              mapM_mono_pointwise (evalHIR fu env) (evalHIR k env) es
                (fun x => SLExpr x ∧ SLWeight x ≤ k) vs
                (fun x hmem =>
                  ⟨hs x hmem, by
                    have hle := le_sum_map_weight hmem
                    omega⟩)
                (fun x hp y hxy => ih env x y hp.2 hp.1 ⟨fu, hxy⟩)
                hmv
            rw [hmono]
            exact hpost

/-! ## The environment relation -/

/-- Relation between HIR ids and register ids: `rhoLookup` and `lookupHEnv`
mirror each other (both first-match), and the HIR binding is a literal
holding the same value the MIR register stores. -/
def RelEnv (henv : HEnv) (ρ : List (HIR.Id × ValId)) (env : Morph.MIR.Env) : Prop :=
  ∀ id u, rhoLookup ρ id = some u →
    ∃ w, lookupHEnv henv id = some (HIR.Expr.lit w) ∧ env u = some w

theorem rhoLookup_cons_head (id : HIR.Id) (u : ValId) (ρ : List (HIR.Id × ValId)) :
    rhoLookup ((id, u) :: ρ) id = some u := by
  simp [rhoLookup]

theorem rhoLookup_cons_ne {id id' : HIR.Id} {u : ValId} (hne : ¬ id = id')
    (ρ : List (HIR.Id × ValId)) :
    rhoLookup ((id, u) :: ρ) id' = rhoLookup ρ id' := by
  simp [rhoLookup, hne]

/-! ## Lowered code: def registers, purity, straight-line shape -/

/-- Every def register in the emitted code is at or above the incoming
supply: lowering allocates upward and its fresh registers are never
below the starting supply. -/
theorem lower_defs_gt :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr) (v : ValId)
      (is : List Instr) (s' : Nat), lowerExpr ρ supply e = some (v, is, s') →
      ∀ d, d ∈ is.flatMap defOf → supply ≤ d) ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat), lowerBlock ρ supply es = some (v, is, s') →
      ∀ d, d ∈ is.flatMap defOf → supply ≤ d) := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') →
      ∀ d, d ∈ is.flatMap defOf → supply ≤ d)
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') →
      ∀ d, d ∈ is.flatMap defOf → supply ≤ d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- lit
    intro ρ supply v v' is s' h
    simp only [lowerExpr] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro d hd
    obtain ⟨i, hi, hdi⟩ := List.mem_flatMap.mp hd
    simp only [List.mem_singleton] at hi
    subst hi
    simp only [defOf, List.mem_singleton] at hdi
    subst hdi
    exact Nat.le_refl _
  · -- var
    intro ρ supply id v' is s' h
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some u =>
        simp only [hr] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        intro d hd
        simp at hd
  · -- unop, success
    intro ρ supply op e u v is s h1 h2 ih v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    have his : is' = is ++ [.unop s u v (unopTyp u)] :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) (Option.some.inj h)).symm
    intro d hd
    rw [his] at hd
    rw [List.flatMap_append] at hd
    rcases List.mem_append.mp hd with hdd | hdd
    · exact ih v is s h1 d hdd
    · have hd_eq : d = s := by simpa [defOf] using hdd
      subst hd_eq
      exact lower_mono.1 _ _ _ _ _ _ h1
  · -- unop, fail
    intro ρ supply op e hfail ih v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · -- binop, success
    intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    have his : is' = ia ++ ib ++ [.binop s2 bo va vb (binopTyp bo)] :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) (Option.some.inj h)).symm
    intro d hd
    rw [his] at hd
    rw [List.flatMap_append] at hd
    rcases List.mem_append.mp hd with hdd | hdd
    · rw [List.flatMap_append] at hdd
      rcases List.mem_append.mp hdd with hda | hdb
      · exact ihA va ia s1 h1 d hda
      · have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
        have := ihB vb ib s2 h3 d hdb
        omega
    · have hd_eq : d = s2 := by simpa [defOf] using hdd
      rw [hd_eq]
      have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
      have hle2 : s1 ≤ s2 := lower_mono.1 _ _ _ _ _ _ h3
      omega
  · -- binop, body fail
    intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · -- binop, operator fail
    intro ρ supply op a b hfail ihA v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some b =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail b p.1 p.2.1 p.2.2 hto ha)
  · -- let, success
    intro ρ supply id init body va ia s1 h1 vb ib s2 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro d hd
    rw [List.flatMap_append] at hd
    rcases List.mem_append.mp hd with hdd | hdd
    · exact ihI va ia s1 h1 d hdd
    · have hle : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
      have := ihB vb ib s2 h2 d hdd
      omega
  · -- let, body fail
    intro ρ supply id init body va ia s1 h1 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · -- let, init fail
    intro ρ supply id init body hfail ihI v' is' s' h
    simp only [lowerExpr, hfail] at h
    simp at h
  · -- block delegate
    intro ρ supply es ih v' is' s' h
    simp only [lowerExpr] at h
    exact ih v' is' s' h
  · -- non-lowering constructors
    intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h
    cases t with
    | lit v => exact False.elim (d1 v rfl)
    | var id => exact False.elim (d2 id rfl)
    | unop op e => exact False.elim (d3 op e rfl)
    | binop op a b => exact False.elim (d4 op a b rfl)
    | «let» id a b => exact False.elim (d5 id a b rfl)
    | block es => exact False.elim (d6 es rfl)
    | app f args => simp [lowerExpr] at h
    | lam p b => simp [lowerExpr] at h
    | ifThenElse c t f => simp [lowerExpr] at h
    | whileLoop c b => simp [lowerExpr] at h
    | «match» s a => simp [lowerExpr] at h
    | infer => simp [lowerExpr] at h
  · -- block, empty
    intro ρ supply v' is' s' h
    simp only [lowerBlock] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro d hd
    obtain ⟨i, hi, hdi⟩ := List.mem_flatMap.mp hd
    simp only [List.mem_singleton] at hi
    subst hi
    simp only [defOf, List.mem_singleton] at hdi
    subst hdi
    exact Nat.le_refl _
  · -- block, singleton
    intro ρ supply e ih v' is' s' h
    simp only [lowerBlock] at h
    exact ih v' is' s' h
  · -- block, cons
    intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro d hd
    rw [List.flatMap_append] at hd
    rcases List.mem_append.mp hd with hdd | hdd
    · exact ihE vb ib s2 h1 d hdd
    · have hle : supply ≤ s2 := lower_mono.1 _ _ _ _ _ _ h1
      have := ihEs vb' ib' s2' h2 d hdd
      omega
  · -- block, tail fail
    intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · -- block, head fail
    intro ρ supply e es hne hfail ihE v' is' s' h
    simp only [lowerBlock, hfail] at h
    simp at h

/-- Emitted code is pure: every instruction the lowering produces is one
of `const`/`copy`/`unop`/`binop`. -/
inductive IsPure : Instr → Prop where
  | const (dst : ValId) (v : Value) : IsPure (.const dst v)
  | copy (dst src : ValId) : IsPure (.copy dst src)
  | unop (dst : ValId) (op : UnOp) (src : ValId) (τ : Typ) : IsPure (.unop dst op src τ)
  | binop (dst : ValId) (op : BinOp) (l r : ValId) (τ : Typ) : IsPure (.binop dst op l r τ)

theorem lower_isPure :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr) (v : ValId)
      (is : List Instr) (s' : Nat), lowerExpr ρ supply e = some (v, is, s') →
      ∀ i, i ∈ is → IsPure i) ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr) (v : ValId)
      (is : List Instr) (s' : Nat), lowerBlock ρ supply es = some (v, is, s') →
      ∀ i, i ∈ is → IsPure i) := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') →
      ∀ i, i ∈ is → IsPure i)
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') →
      ∀ i, i ∈ is → IsPure i)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ρ supply v v' is s' h
    simp only [lowerExpr] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact IsPure.const _ _
  · intro ρ supply id v' is s' h
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some u =>
        simp only [hr] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        intro i hi
        simp at hi
  · intro ρ supply op e u v is s h1 h2 ih v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ih v is s h1 i hi
    · simp only [List.mem_singleton] at hi
      subst hi
      exact IsPure.unop _ _ _ _
  · intro ρ supply op e hfail ih v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hia | hib
      · exact ihA va ia s1 h1 i hia
      · exact ihB vb ib s2 h3 i hib
    · simp only [List.mem_singleton] at hi
      subst hi
      exact IsPure.binop _ _ _ _ _
  · intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · intro ρ supply op a b hfail ihA v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some b =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail b p.1 p.2.1 p.2.2 hto ha)
  · intro ρ supply id init body va ia s1 h1 vb ib s2 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ihI va ia s1 h1 i hi
    · exact ihB vb ib s2 h2 i hi
  · intro ρ supply id init body va ia s1 h1 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · intro ρ supply id init body hfail ihI v' is' s' h
    simp only [lowerExpr, hfail] at h
    simp at h
  · intro ρ supply es ih v' is' s' h
    simp only [lowerExpr] at h
    exact ih v' is' s' h
  · intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h
    cases t with
    | lit v => exact False.elim (d1 v rfl)
    | var id => exact False.elim (d2 id rfl)
    | unop op e => exact False.elim (d3 op e rfl)
    | binop op a b => exact False.elim (d4 op a b rfl)
    | «let» id a b => exact False.elim (d5 id a b rfl)
    | block es => exact False.elim (d6 es rfl)
    | app f args => simp [lowerExpr] at h
    | lam p b => simp [lowerExpr] at h
    | ifThenElse c t f => simp [lowerExpr] at h
    | whileLoop c b => simp [lowerExpr] at h
    | «match» s a => simp [lowerExpr] at h
    | infer => simp [lowerExpr] at h
  · intro ρ supply v' is' s' h
    simp only [lowerBlock] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact IsPure.const _ _
  · intro ρ supply e ih v' is' s' h
    simp only [lowerBlock] at h
    exact ih v' is' s' h
  · intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ihE vb ib s2 h1 i hi
    · exact ihEs vb' ib' s2' h2 i hi
  · intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · intro ρ supply e es hne hfail ihE v' is' s' h
    simp only [lowerBlock, hfail] at h
    simp at h

/-- Lowering success implies the straight-line shape. -/
theorem lower_isStraight :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr) (v : ValId)
      (is : List Instr) (s' : Nat), lowerExpr ρ supply e = some (v, is, s') →
      IsStraight e) ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr) (v : ValId)
      (is : List Instr) (s' : Nat), lowerBlock ρ supply es = some (v, is, s') →
      IsStraight (.block es)) := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → IsStraight e)
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → IsStraight (.block es))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ρ supply v v' is s' h
    simp only [lowerExpr] at h
    exact IsStraight.lit _
  · intro ρ supply id v' is s' h
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some u =>
        simp only [hr] at h
        exact IsStraight.var _
  · intro ρ supply op e u v is s h1 h2 ih v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    exact IsStraight.unop _ _ (by rw [h2]; simp) (ih v is s h1)
  · intro ρ supply op e hfail ih v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    exact IsStraight.binop _ _ _ (by rw [h2]; simp) (ihA va ia s1 h1) (ihB vb ib s2 h3)
  · intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · intro ρ supply op a b hfail ihA v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some b =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail b p.1 p.2.1 p.2.2 hto ha)
  · intro ρ supply id init body va ia s1 h1 vb ib s2 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    exact IsStraight.let_ _ _ _ (ihI va ia s1 h1) (ihB vb ib s2 h2)
  · intro ρ supply id init body va ia s1 h1 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · intro ρ supply id init body hfail ihI v' is' s' h
    simp only [lowerExpr, hfail] at h
    simp at h
  · intro ρ supply es ih v' is' s' h
    simp only [lowerExpr] at h
    exact ih v' is' s' h
  · intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h
    cases t with
    | lit v => exact False.elim (d1 v rfl)
    | var id => exact False.elim (d2 id rfl)
    | unop op e => exact False.elim (d3 op e rfl)
    | binop op a b => exact False.elim (d4 op a b rfl)
    | «let» id a b => exact False.elim (d5 id a b rfl)
    | block es => exact False.elim (d6 es rfl)
    | app f args => simp [lowerExpr] at h
    | lam p b => simp [lowerExpr] at h
    | ifThenElse c t f => simp [lowerExpr] at h
    | whileLoop c b => simp [lowerExpr] at h
    | «match» s a => simp [lowerExpr] at h
    | infer => simp [lowerExpr] at h
  · intro ρ supply v' is' s' h
    simp only [lowerBlock] at h
    exact IsStraight.block [] (by simp)
  · intro ρ supply e ih v' is' s' h
    simp only [lowerBlock] at h
    exact IsStraight.block [e]
      (by intro x hx; simp at hx; subst hx; exact ih v' is' s' h)
  · intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    refine IsStraight.block _ ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ihE vb ib s2 h1
    · cases ihEs vb' ib' s2' h2 with
      | block es' hall => exact hall x hx
  · intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · intro ρ supply e es hne hfail ihE v' is' s' h
    simp only [lowerBlock, hfail] at h
    simp at h

/-- `IsStraight` gives the inductive fragment shape the fuel-monotonicity
lemma consumes. -/
theorem IsStraight_to_SLExpr {e : HIR.Expr} (hs : IsStraight e) : SLExpr e := by
  induction hs with
  | var id => simp only [SLExpr]
  | lit v => simp only [SLExpr]
  | unop op e _ hne hi => simp only [SLExpr]; exact hi
  | binop op a b _ ha hb ihA ihB =>
      simp only [SLExpr]; exact ⟨ihA, ihB⟩
  | let_ id init body hi hb ihI ihB =>
      simp only [SLExpr]; exact ⟨ihI, ihB⟩
  | block es hall ihX =>
      simp only [SLExpr]; exact ihX

/-! ## Exec-side preservation: registers below the supply and the store -/

/-- One pure instruction step: registers strictly below `n` keep their
values and the store is untouched (`n` bounds every def register). -/
theorem evalInstrFull_pure_below (fenv : FullEnv) (i : Instr)
    (hp : IsPure i) (n : Nat) (hn : ∀ d, d ∈ defOf i → n ≤ d)
    (u : ValId) (hu : u < n)
    (fenv1 : FullEnv) (h : evalInstrFull fenv i = some fenv1) :
    fenv1.env u = fenv.env u ∧ fenv1.store = fenv.store := by
  have key : ∀ (dst : ValId) (v : Value), u < dst →
      (fun x => if x == dst then some v else fenv.env x) u = fenv.env u := by
    intro dst v hlt
    have hbb : (u == dst) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp [hbb]
  cases i with
  | const dst v =>
      cases hp
      have hlt : u < dst := Nat.lt_of_lt_of_le hu (hn dst (by simp [defOf]))
      simp only [evalInstrFull] at h
      have hfe : fenv1 = ⟨(fenv.env).update dst v, fenv.store⟩ :=
        (Option.some.inj h).symm
      subst hfe
      exact ⟨key dst v hlt, rfl⟩
  | copy dst src =>
      cases hp
      have hlt : u < dst := Nat.lt_of_lt_of_le hu (hn dst (by simp [defOf]))
      simp only [evalInstrFull] at h
      obtain ⟨a, _hsrc, hrest⟩ := bind_some_eq h
      have hfe : fenv1 = ⟨(fenv.env).update dst a, fenv.store⟩ :=
        (Option.some.inj hrest).symm
      subst hfe
      exact ⟨key dst a hlt, rfl⟩
  | unop dst op src τ =>
      cases hp
      have hlt : u < dst := Nat.lt_of_lt_of_le hu (hn dst (by simp [defOf]))
      simp only [evalInstrFull] at h
      obtain ⟨_a, _hsrc, hstep⟩ := bind_some_eq h
      obtain ⟨r, _hr, h2⟩ := bind_some_eq hstep
      have hfe : fenv1 = ⟨(fenv.env).update dst r, fenv.store⟩ :=
        (Option.some.inj h2).symm
      subst hfe
      exact ⟨key dst r hlt, rfl⟩
  | binop dst op l r τ =>
      cases hp
      have hlt : u < dst := Nat.lt_of_lt_of_le hu (hn dst (by simp [defOf]))
      simp only [evalInstrFull] at h
      obtain ⟨_a, _hl, hstep1⟩ := bind_some_eq h
      obtain ⟨_b, _hr, hstep2⟩ := bind_some_eq hstep1
      obtain ⟨c, _hc, hstep3⟩ := bind_some_eq hstep2
      have hfe : fenv1 = ⟨(fenv.env).update dst c, fenv.store⟩ :=
        (Option.some.inj hstep3).symm
      subst hfe
      exact ⟨key dst c hlt, rfl⟩
  | load dst loc cap => cases hp
  | store loc src cap => cases hp
  | alloc dst cap τ => cases hp
  | free loc => cases hp
  | call dst fn args => cases hp
  | allocClosure dst fn captures => cases hp
  | callClosure dst clo args => cases hp
  | phi dst srcs τ => cases hp

/-- Multi-instruction version: a pure sequence only re-allocates registers
at or above `n`, so every register below `n` survives and the store is
never touched. -/
theorem execInstrsFull_preservLow (n : Nat) (fenv : FullEnv) :
    ∀ (is : List Instr) (fenv2 : FullEnv),
      (∀ i, i ∈ is → IsPure i) →
      (∀ d, d ∈ is.flatMap defOf → n ≤ d) →
      execInstrsFull fenv is = some fenv2 →
      ∀ u, u < n → fenv2.env u = fenv.env u ∧ fenv2.store = fenv.store := by
  intro is
  induction is generalizing fenv with
  | nil =>
      intro fenv2 _ _ h u _
      have h2 : fenv2 = fenv := by
        rw [execInstrsFull_nil] at h
        exact (Option.some.inj h).symm
      subst h2
      exact ⟨rfl, rfl⟩
  | cons i is ih =>
      intro fenv2 hpure hdefs h u hu
      have hpi : IsPure i := hpure i List.mem_cons_self
      have hni : ∀ d, d ∈ defOf i → n ≤ d := by
        intro d hd
        exact hdefs d (by rw [List.flatMap_cons]; exact List.mem_append_left _ hd)
      have hdefs' : ∀ d, d ∈ is.flatMap defOf → n ≤ d := by
        intro d hd
        exact hdefs d (by rw [List.flatMap_cons]; exact List.mem_append_right _ hd)
      rw [execInstrsFull_cons] at h
      cases hx : evalInstrFull fenv i with
      | none => rw [hx] at h; simp at h
      | some fenv1 =>
          rw [hx] at h
          obtain ⟨henv_u, hstore1⟩ :=
            evalInstrFull_pure_below fenv i hpi n hni u hu fenv1 hx
          obtain ⟨henv_u', hstore'⟩ :=
            ih fenv1 fenv2 (fun j hj => hpure j (List.mem_cons_of_mem _ hj)) hdefs'
              (by simpa using h) u hu
          exact ⟨by rw [henv_u', henv_u], by rw [hstore', hstore1]⟩

/-- Loop success gives per-index results for `List.mapM` (the `bs = []` case
of `mapM_loop_pointwise`). -/
theorem mapM_pointwise {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), List.mapM f xs = some ys →
      ∀ (i : Nat) (x : α), xs[i]? = some x →
        ∃ y, ys[i]? = some y ∧ f x = some y := by
  intro xs ys h i x hx
  have h' : List.mapM.loop f xs [] = some ys := by rw [← mapM_eq_loop]; exact h
  obtain ⟨zs, -, hpt, hshape⟩ := mapM_loop_pointwise xs [] ys f h'
  have hzy : ys = zs := by simpa using hshape
  rw [hzy]
  exact hpt i x hx

/-- A successful `List.mapM` has as many results as inputs. -/
theorem mapM_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), List.mapM f xs = some ys → xs.length = ys.length := by
  intro xs ys h
  have h' : List.mapM.loop f xs [] = some ys := by rw [← mapM_eq_loop]; exact h
  obtain ⟨zs, hlen, -, hshape⟩ := mapM_loop_pointwise xs [] ys f h'
  have hzy : ys = zs := by simpa using hshape
  rw [hzy]
  exact hlen

/-- `mapM` on a cons list splits into the head result and the tail `mapM`.
Bridged through HIREval's loop gadgets so it holds for the core
`List.mapM` implementation. -/
theorem mapM_cons_eq {α β : Type} (f : α → Option β) (a : α) (as : List α)
    (v : β) (vs : List β) :
    List.mapM f (a :: as) = some (v :: vs) ↔
      (f a = some v ∧ List.mapM f as = some vs) := by
  constructor
  · intro h
    have h' : List.mapM.loop f (a :: as) [] = some (v :: vs) := by
      rw [← mapM_eq_loop]; exact h
    obtain ⟨zs, hlen, hpoint, hshape⟩ :=
      mapM_loop_pointwise (a :: as) [] (v :: vs) f h'
    have hz : v :: vs = zs := by simpa using hshape
    subst hz
    obtain ⟨y, hy, hfy⟩ := hpoint 0 a (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    have hlen2 : as.length = vs.length := by
      simp only [List.length_cons] at hlen
      omega
    have hpt' : ∀ (i : Nat) (x : α), as[i]? = some x →
        ∃ y, vs[i]? = some y ∧ f x = some y := by
      intro i x hxa
      obtain ⟨y, hy, hfy⟩ :=
        hpoint (i + 1) x (by simp only [List.getElem?_cons_succ]; exact hxa)
      exact ⟨y, by simpa using hy, hfy⟩
    refine ⟨hfy, ?_⟩
    rw [mapM_eq_loop, mapM_loop_of_pointwise as [] vs f hlen2 hpt']
    simp
  · intro h
    obtain ⟨ha, htail⟩ := h
    have hlen2 : as.length = vs.length := mapM_length f as vs htail
    have hpt' : ∀ (i : Nat) (x : α), (a :: as)[i]? = some x →
        ∃ y, (v :: vs)[i]? = some y ∧ f x = some y := by
      intro i x hxa
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hxa
          subst hxa
          exact ⟨v, by simp, ha⟩
      | succ i' =>
          simp only [List.getElem?_cons_succ] at hxa
          obtain ⟨y, hy, hfy⟩ := mapM_pointwise f as vs htail i' x hxa
          exact ⟨y, by simpa using hy, hfy⟩
    have hlen : (a :: as).length = (v :: vs).length := by
      simp only [List.length_cons]
      omega
    rw [mapM_eq_loop, mapM_loop_of_pointwise (a :: as) [] (v :: vs) f hlen hpt']
    simp

/-! ## `IsStraight` projections -/

theorem IsStraight_unop_sub {op : Operator} {e : HIR.Expr}
    (h : IsStraight (.unop op e)) : IsStraight e := by
  cases h with
  | unop _ _ _ hi => exact hi

theorem IsStraight_binop_sub_l {op : Operator} {a b : HIR.Expr}
    (h : IsStraight (.binop op a b)) : IsStraight a := by
  cases h with
  | binop _ _ _ _ ha _ => exact ha

theorem IsStraight_binop_sub_r {op : Operator} {a b : HIR.Expr}
    (h : IsStraight (.binop op a b)) : IsStraight b := by
  cases h with
  | binop _ _ _ _ _ hb => exact hb

theorem IsStraight_let_init {id : HIR.Id} {init body : HIR.Expr}
    (h : IsStraight (.let id init body)) : IsStraight init := by
  cases h with
  | let_ _ _ _ hi _ => exact hi

theorem IsStraight_let_body {id : HIR.Id} {init body : HIR.Expr}
    (h : IsStraight (.let id init body)) : IsStraight body := by
  cases h with
  | let_ _ _ _ _ hb => exact hb

theorem IsStraight_block_mem {es : List HIR.Expr} (h : IsStraight (.block es)) :
    ∀ x ∈ es, IsStraight x := by
  cases h with
  | block _ hall => exact hall

/-! ## Execution agreement -/

/-- `getLast!` of a mapped non-empty list is the mapping of the last element. -/
theorem getLast_map_lit : ∀ (vs : List Value), vs ≠ [] →
    (vs.map HIR.Expr.lit).getLast! = HIR.Expr.lit (vs.getLastD .unit) := by
  intro vs
  induction vs with
  | nil => intro h; exact absurd rfl h
  | cons w rest ih =>
      intro _
      cases rest with
      | nil => rfl
      | cons w' rest' =>
          have ih2 : ((w' :: rest').map HIR.Expr.lit).getLast!
              = HIR.Expr.lit ((w' :: rest').getLastD .unit) := ih (by simp)
          simpa using ih2

/-- `getLastD` ignores the head when the tail is non-empty. -/
theorem getLastD_cons_of_ne {w : Value} {vs : List Value} (h : vs ≠ []) :
    (w :: vs).getLastD .unit = vs.getLastD .unit := by
  cases vs with
  | nil => exact absurd rfl h
  | cons v vs' => rfl

/-- Fuel monotonicity of a block's `mapM` run. -/
theorem mapM_evalHIR_mono (fuel m : Nat) (hle : fuel ≤ m) (henv : HEnv)
    (es : List HIR.Expr) (vs : List Value)
    (hs : ∀ x ∈ es, SLExpr x)
    (h : es.mapM (evalHIR fuel henv) = some (vs.map HIR.Expr.lit)) :
    es.mapM (evalHIR m henv) = some (vs.map HIR.Expr.lit) := by
  have hlen : es.length = (vs.map HIR.Expr.lit).length :=
    mapM_length (evalHIR fuel henv) es _ h
  have hpt : ∀ (i : Nat) (x : HIR.Expr), es[i]? = some x →
      ∃ y, (vs.map HIR.Expr.lit)[i]? = some y ∧ evalHIR m henv x = some y := by
    intro i x hxa
    obtain ⟨y, hya, hfy⟩ :=
      mapM_pointwise (evalHIR fuel henv) es (vs.map HIR.Expr.lit) h i x hxa
    exact ⟨y, hya,
      evalHIR_mono fuel m henv x y hle (hs x (getElem?_to_mem es i x hxa)) hfy⟩
  rw [mapM_eq_loop,
    mapM_loop_of_pointwise es [] (vs.map HIR.Expr.lit) (evalHIR m henv) hlen hpt]
  simp

/-- Block-level evaluation from the `mapM`-level claim. -/
theorem block_eval_of_mapM {es : List HIR.Expr} {vs : List Value} {fuel : Nat}
    {henv : HEnv}
    (h : es.mapM (evalHIR fuel henv) = some (vs.map HIR.Expr.lit)) :
    evalHIR (fuel + 1) henv (.block es) = some (.lit (vs.getLastD .unit)) := by
  cases vs with
  | nil =>
      have hlen : es.length = 0 := by
        have hl := mapM_length (evalHIR fuel henv) es (List.map HIR.Expr.lit []) h
        simpa using hl
      cases es with
      | nil => simp [evalHIR]
      | cons e rest => simp at hlen
  | cons w rest =>
      have hmap : es.mapM (evalHIR fuel henv)
          = some (HIR.Expr.lit w :: rest.map HIR.Expr.lit) := by
        simpa using h
      have hgl : (HIR.Expr.lit w :: rest.map HIR.Expr.lit).getLast!
          = HIR.Expr.lit ((w :: rest).getLastD .unit) :=
        getLast_map_lit (w :: rest) (by simp)
      simp only [evalHIR]
      rw [hmap]
      show some ((HIR.Expr.lit w :: rest.map HIR.Expr.lit).getLast!)
        = some (HIR.Expr.lit ((w :: rest).getLastD .unit))
      rw [hgl]

/-! ## Evaluator step lemmas -/

theorem evalHIR_unop_step (fuel : Nat) (henv : HEnv) (op : Operator)
    (e : HIR.Expr) (va : Value)
    (ha : evalHIR fuel henv e = some (.lit va)) :
    evalHIR (fuel + 1) henv (.unop op e) =
      (match Morph.Executable.evalUnop op (.lit va) with
       | some (.lit w) => some (.lit w)
       | _ => none) := by
  simp only [evalHIR]
  rw [ha]
  rfl

theorem evalHIR_binop_step (fuel : Nat) (henv : HEnv) (op : Operator)
    (a b : HIR.Expr) (va vb : Value)
    (ha : evalHIR fuel henv a = some (.lit va))
    (hb : evalHIR fuel henv b = some (.lit vb)) :
    evalHIR (fuel + 1) henv (.binop op a b) =
      (match Morph.Executable.evalBinop op (.lit va) (.lit vb) with
       | some (.lit w) => some (.lit w)
       | _ => none) := by
  simp only [evalHIR]
  rw [ha, hb]
  rfl

theorem evalHIR_let_step (fuel : Nat) (henv : HEnv) (id : HIR.Id)
    (init body : HIR.Expr) (w w2 : Value)
    (hinit : evalHIR fuel henv init = some (.lit w))
    (hbody : evalHIR fuel ((id, .lit w) :: henv) body = some (.lit w2)) :
    evalHIR (fuel + 1) henv (.let id init body) = some (.lit w2) := by
  simp only [evalHIR]
  rw [hinit]
  exact hbody

/-! ## MIR step results -/

/-- A successful `unop` step pins the operator result and the new register file. -/
theorem evalInstrFull_unop_result (fenv : FullEnv) (dst : ValId) (u : UnOp)
    (src : ValId) (τ : Typ) (w : Value) (hsrc : fenv.env src = some w)
    (fenv1 : FullEnv) (h : evalInstrFull fenv (.unop dst u src τ) = some fenv1) :
    ∃ r, evalUnOp u w = some r ∧
      fenv1 = ⟨(fenv.env).update dst r, fenv.store⟩ := by
  rw [evalInstrFull_unop_step] at h
  rw [hsrc] at h
  obtain ⟨a, ha, hb⟩ := bind_some_eq h
  have haw : a = w := (Option.some.inj ha).symm
  obtain ⟨r, hr, hc⟩ := bind_some_eq hb
  refine ⟨r, ?_, (Option.some.inj hc).symm⟩
  rw [← haw]
  exact hr

/-- A successful `binop` step pins the operator result and the new register file. -/
theorem evalInstrFull_binop_result (fenv : FullEnv) (dst : ValId) (b : BinOp)
    (l r : ValId) (τ : Typ) (vl vr : Value)
    (hl : fenv.env l = some vl) (hr : fenv.env r = some vr)
    (fenv1 : FullEnv) (h : evalInstrFull fenv (.binop dst b l r τ) = some fenv1) :
    ∃ w, evalBinOp b vl vr = some w ∧
      fenv1 = ⟨(fenv.env).update dst w, fenv.store⟩ := by
  rw [evalInstrFull_binop_step] at h
  rw [hl, hr] at h
  obtain ⟨a, ha, hb⟩ := bind_some_eq h
  obtain ⟨c, hc, hd⟩ := bind_some_eq hb
  obtain ⟨w, hw, he⟩ := bind_some_eq hd
  have hav : a = vl := (Option.some.inj ha).symm
  have hcv : c = vr := (Option.some.inj hc).symm
  refine ⟨w, ?_, (Option.some.inj he).symm⟩
  rw [← hav, ← hcv]
  exact hw

/-- A successful singleton run pins the single step's result. -/
theorem execInstrsFull_singleton_elim (fenv fenv' : FullEnv) (i : Instr)
    (h : execInstrsFull fenv [i] = some fenv') :
    ∃ fenv1, evalInstrFull fenv i = some fenv1 ∧ fenv' = fenv1 := by
  rw [execInstrsFull_cons] at h
  cases hx : evalInstrFull fenv i with
  | none => rw [hx] at h; simp at h
  | some fenv1 =>
      rw [hx] at h
      refine ⟨fenv1, rfl, ?_⟩
      have h' : some fenv1 = some fenv' := by simpa [execInstrsFull] using h
      exact (Option.some.inj h').symm

/-- Emitted code preserves registers below its starting supply. -/
theorem lower_preserv_regs (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
    (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerExpr ρ supply e = some (v, is, s')) (fenv fenv2 : FullEnv)
    (hexec : execInstrsFull fenv is = some fenv2) :
    ∀ u, u < supply → fenv2.env u = fenv.env u := by
  intro u hu
  exact (execInstrsFull_preservLow supply fenv is fenv2
    (lower_isPure.1 _ _ _ _ _ _ h) (lower_defs_gt.1 _ _ _ _ _ _ h) hexec u hu).1

theorem lowerBlock_preserv_regs (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (es : List HIR.Expr) (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerBlock ρ supply es = some (v, is, s')) (fenv fenv2 : FullEnv)
    (hexec : execInstrsFull fenv is = some fenv2) :
    ∀ u, u < supply → fenv2.env u = fenv.env u := by
  intro u hu
  exact (execInstrsFull_preservLow supply fenv is fenv2
    (lower_isPure.2 _ _ _ _ _ _ h) (lower_defs_gt.2 _ _ _ _ _ _ h) hexec u hu).1

/-- The environment relation survives emitted code. -/
theorem RelEnv_exec (henv : HEnv) (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (e : HIR.Expr) (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerExpr ρ supply e = some (v, is, s'))
    (fenv fenv2 : FullEnv) (hrel : RelEnv henv ρ fenv.env)
    (hf : FreshAbove ρ supply) (hexec : execInstrsFull fenv is = some fenv2) :
    RelEnv henv ρ fenv2.env := by
  intro id u hlook
  obtain ⟨w, hlookH, hreg⟩ := hrel id u hlook
  have hu : u < supply := hf id u (rhoLookup_some_mem ρ id u hlook)
  have heq := lower_preserv_regs ρ supply e v is s' h fenv fenv2 hexec u hu
  exact ⟨w, hlookH, by rw [heq]; exact hreg⟩

/-! ## The agreement theorem -/

/-- One-directional bridge (D-2/D-4): if lowering succeeds and the lowered
code runs successfully, the source evaluates to the same value, the result
register holds it, and the store is untouched. -/
theorem lower_correct :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → IsStraight e →
      FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fenv' : FullEnv), execInstrsFull fenv is = some fenv' →
      ∃ (w : Value) (fuel : Nat),
        evalHIR fuel henv e = some (.lit w) ∧
        fenv'.env v = some w ∧ fenv'.store = fenv.store) ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') →
      (∀ x ∈ es, IsStraight x) → FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fenv' : FullEnv), execInstrsFull fenv is = some fenv' →
      ∃ (vs : List Value) (fuel : Nat),
        es.mapM (evalHIR fuel henv) = some (vs.map HIR.Expr.lit) ∧
        fenv'.env v = some (vs.getLastD .unit) ∧
        fenv'.store = fenv.store) := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → IsStraight e →
      FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fenv' : FullEnv), execInstrsFull fenv is = some fenv' →
      ∃ (w : Value) (fuel : Nat),
        evalHIR fuel henv e = some (.lit w) ∧
        fenv'.env v = some w ∧ fenv'.store = fenv.store)
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') →
      (∀ x ∈ es, IsStraight x) → FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fenv' : FullEnv), execInstrsFull fenv is = some fenv' →
      ∃ (vs : List Value) (fuel : Nat),
        es.mapM (evalHIR fuel henv) = some (vs.map HIR.Expr.lit) ∧
        fenv'.env v = some (vs.getLastD .unit) ∧
        fenv'.store = fenv.store)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- lit
    intro ρ supply v v' is s' h _hs _hf henv fenv _hrel fenv' hexec
    simp only [lowerExpr] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hfe : fenv' = ⟨(fenv.env).update supply v, fenv.store⟩ := by
      have h' : some ⟨(fenv.env).update supply v, fenv.store⟩ = some fenv' := by
        simpa [execInstrsFull, evalInstrFull] using hexec
      exact (Option.some.inj h').symm
    subst hfe
    exact ⟨v, 1, by simp [evalHIR], by simp [Env.update], rfl⟩
  · -- var
    intro ρ supply id v' is s' h _hs _hf henv fenv hrel fenv' hexec
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some u =>
        simp only [hr] at h
        have hpair := Option.some.inj h
        have hvu : v' = u :=
          (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
        have his : is = [] :=
          (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
        have hfe : fenv' = fenv := by
          have h' : execInstrsFull fenv [] = some fenv' := by rw [← his]; exact hexec
          rw [execInstrsFull_nil] at h'
          exact (Option.some.inj h').symm
        obtain ⟨w, hlook, hreg⟩ := hrel id u hr
        rw [hfe, hvu]
        exact ⟨w, 1, by simp [evalHIR, hlook], hreg, rfl⟩
  · -- unop, success
    intro ρ supply op e u v is s h1 h2 ih v' is' s' h hs hf henv fenv hrel fenv' hexec
    simp only [lowerExpr, h1, h2] at h
    have hpair := Option.some.inj h
    have his : is' = is ++ [.unop s u v (unopTyp u)] :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvs : v' = s :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    rw [his, execInstrsFull_append] at hexec
    cases hpre : execInstrsFull fenv is with
    | none => rw [hpre] at hexec; simp at hexec
    | some fenv1 =>
        rw [hpre] at hexec
        have hexec1 : execInstrsFull fenv1 [.unop s u v (unopTyp u)] = some fenv' :=
          by simpa using hexec
        have hstraight : IsStraight e := IsStraight_unop_sub hs
        obtain ⟨w, fuel, heval, hreg, hstore⟩ :=
          ih v is s h1 hstraight hf henv fenv hrel fenv1 hpre
        obtain ⟨fenv2, hstep, hfe2⟩ :=
          execInstrsFull_singleton_elim fenv1 fenv' (.unop s u v (unopTyp u)) hexec1
        obtain ⟨r, hr, hfe3⟩ :=
          evalInstrFull_unop_result fenv1 s u v (unopTyp u) w hreg fenv2 hstep
        have hglue : Morph.Executable.evalUnop op (.lit w) = some (.lit r) :=
          (evalUnop_glue op u w r h2).mp hr
        refine ⟨r, fuel + 1, ?_, ?_, ?_⟩
        · rw [evalHIR_unop_step fuel henv op e w heval, hglue]
        · rw [hvs, hfe2, hfe3]
          simp [Env.update]
        · rw [hfe2, hfe3]
          exact hstore
  · -- unop, fail
    intro ρ supply op e hfail ih v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · -- binop, success
    intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 ihA ihB v' is' s' h hs hf henv fenv hrel fenv' hexec
    simp only [lowerExpr, h1, h2, h3] at h
    have hpair := Option.some.inj h
    have his : is' = ia ++ ib ++ [.binop s2 bo va vb (binopTyp bo)] :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvs : v' = s2 :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    rw [his, execInstrsFull_append] at hexec
    cases hpreM : execInstrsFull fenv (ia ++ ib) with
    | none => rw [hpreM] at hexec; simp at hexec
    | some fenv2 =>
        rw [hpreM] at hexec
        have hexec2 : execInstrsFull fenv2 [.binop s2 bo va vb (binopTyp bo)]
            = some fenv' := by simpa using hexec
        rw [execInstrsFull_append] at hpreM
        cases hpre : execInstrsFull fenv ia with
        | none => rw [hpre] at hpreM; simp at hpreM
        | some fenv1 =>
            rw [hpre] at hpreM
            have hpre2 : execInstrsFull fenv1 ib = some fenv2 := by simpa using hpreM
            have hsa : IsStraight a := IsStraight_binop_sub_l hs
            have hsb : IsStraight b := IsStraight_binop_sub_r hs
            obtain ⟨wa, fuelA, hevalA, hregA, hstoreA⟩ :=
              ihA va ia s1 h1 hsa hf henv fenv hrel fenv1 hpre
            have hf' : FreshAbove ρ s1 :=
              FreshAbove.mono ρ supply s1 (lower_mono.1 _ _ _ _ _ _ h1) hf
            have hrel1 : RelEnv henv ρ fenv1.env :=
              RelEnv_exec henv ρ supply a va ia s1 h1 fenv fenv1 hrel hf hpre
            obtain ⟨wb, fuelB, hevalB, hregB, hstoreB⟩ :=
              ihB vb ib s2 h3 hsb hf' henv fenv1 hrel1 fenv2 hpre2
            have hva_lt : va < s1 := lower_result_lt.1 ρ supply a va ia s1 h1 hf
            have hregA' : fenv2.env va = some wa := by
              have heq := lower_preserv_regs ρ s1 b vb ib s2 h3 fenv1 fenv2 hpre2 va hva_lt
              rw [heq]
              exact hregA
            obtain ⟨fenv3, hstep, hfe3⟩ :=
              execInstrsFull_singleton_elim fenv2 fenv'
                (.binop s2 bo va vb (binopTyp bo)) hexec2
            obtain ⟨r, hbin, hfe4⟩ :=
              evalInstrFull_binop_result fenv2 s2 bo va vb (binopTyp bo) wa wb
                hregA' hregB fenv3 hstep
            have hglue : Morph.Executable.evalBinop op (.lit wa) (.lit wb)
                = some (.lit r) := (evalBinop_glue op bo wa wb r h2).mp hbin
            have hA : evalHIR (max fuelA fuelB) henv a = some (.lit wa) :=
              evalHIR_mono fuelA (max fuelA fuelB) henv a (.lit wa)
                (Nat.le_max_left _ _) (IsStraight_to_SLExpr hsa) hevalA
            have hB : evalHIR (max fuelA fuelB) henv b = some (.lit wb) :=
              evalHIR_mono fuelB (max fuelA fuelB) henv b (.lit wb)
                (Nat.le_max_right _ _) (IsStraight_to_SLExpr hsb) hevalB
            refine ⟨r, max fuelA fuelB + 1, ?_, ?_, ?_⟩
            · rw [evalHIR_binop_step (max fuelA fuelB) henv op a b wa wb hA hB, hglue]
            · rw [hvs, hfe3, hfe4]
              simp [Env.update]
            · rw [hfe3, hfe4, hstoreB, hstoreA]
  · -- binop, body fail
    intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · -- binop, operator fail
    intro ρ supply op a b hfail ihA v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some b =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail b p.1 p.2.1 p.2.2 hto ha)
  · -- let, success
    intro ρ supply id init body va ia s1 h1 vb ib s2 h2 ihI ihB v' is' s' h hs hf henv fenv hrel fenv' hexec
    simp only [lowerExpr, h1, h2] at h
    have hpair := Option.some.inj h
    have his : is' = ia ++ ib :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvv : v' = vb :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    rw [his, execInstrsFull_append] at hexec
    cases hpre : execInstrsFull fenv ia with
    | none => rw [hpre] at hexec; simp at hexec
    | some fenv1 =>
        rw [hpre] at hexec
        have hexec1 : execInstrsFull fenv1 ib = some fenv' := by simpa using hexec
        have hsi : IsStraight init := IsStraight_let_init hs
        have hsb : IsStraight body := IsStraight_let_body hs
        obtain ⟨w, fuelI, hevalI, hregI, hstoreI⟩ :=
          ihI va ia s1 h1 hsi hf henv fenv hrel fenv1 hpre
        have hva : va < s1 := lower_result_lt.1 ρ supply init va ia s1 h1 hf
        have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
        have hf' : FreshAbove ((id, va) :: ρ) s1 := by
          intro j u hmem
          rcases List.mem_cons.mp hmem with heq | hmem
          · cases heq
            exact hva
          · exact Nat.lt_of_lt_of_le (hf j u hmem) hle1
        have hrel' : RelEnv ((id, HIR.Expr.lit w) :: henv) ((id, va) :: ρ) fenv1.env := by
          intro j u hlook
          by_cases hid : id = j
          · subst hid
            have hu : u = va := by
              have hh : rhoLookup ((id, va) :: ρ) id = some va :=
                rhoLookup_cons_head id va ρ
              rw [hh] at hlook
              exact (Option.some.inj hlook).symm
            subst hu
            exact ⟨w, by simp [lookupHEnv], hregI⟩
          · have hlook' : rhoLookup ρ j = some u := by
              rw [rhoLookup_cons_ne hid] at hlook
              exact hlook
            obtain ⟨w', hlookH, hreg⟩ := hrel j u hlook'
            have hu_lt : u < supply := hf j u (rhoLookup_some_mem ρ j u hlook')
            have heq := lower_preserv_regs ρ supply init va ia s1 h1 fenv fenv1 hpre u hu_lt
            exact ⟨w', by rw [lookupHEnv_cons_ne hid]; exact hlookH,
              by rw [heq]; exact hreg⟩
        obtain ⟨wb, fuelB, hevalB, hregB, hstoreB⟩ :=
          ihB vb ib s2 h2 hsb hf' ((id, .lit w) :: henv) fenv1 hrel' fenv' hexec1
        have hI : evalHIR (max fuelI fuelB) henv init = some (.lit w) :=
          evalHIR_mono fuelI (max fuelI fuelB) henv init (.lit w)
            (Nat.le_max_left _ _) (IsStraight_to_SLExpr hsi) hevalI
        have hB : evalHIR (max fuelI fuelB) ((id, .lit w) :: henv) body
            = some (.lit wb) :=
          evalHIR_mono fuelB (max fuelI fuelB) ((id, .lit w) :: henv) body (.lit wb)
            (Nat.le_max_right _ _) (IsStraight_to_SLExpr hsb) hevalB
        refine ⟨wb, max fuelI fuelB + 1,
          evalHIR_let_step (max fuelI fuelB) henv id init body w wb hI hB,
          ?_, ?_⟩
        · rw [hvv]
          exact hregB
        · rw [hstoreB, hstoreI]
  · -- let, body fail
    intro ρ supply id init body va ia s1 h1 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · -- let, init fail
    intro ρ supply id init body hfail ihI v' is' s' h
    simp only [lowerExpr, hfail] at h
    simp at h
  · -- block delegate
    intro ρ supply es ih v' is' s' h hs hf henv fenv hrel fenv' hexec
    simp only [lowerExpr] at h
    have hs' : ∀ x ∈ es, IsStraight x := by
      cases hs with
      | block _ hall => exact hall
    obtain ⟨vs, fuel, hmap, hreg, hstore⟩ :=
      ih v' is' s' h hs' hf henv fenv hrel fenv' hexec
    exact ⟨vs.getLastD .unit, fuel + 1, block_eval_of_mapM hmap, hreg, hstore⟩
  · -- non-lowering constructors
    intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h
    cases t with
    | lit v => exact False.elim (d1 v rfl)
    | var id => exact False.elim (d2 id rfl)
    | unop op e => exact False.elim (d3 op e rfl)
    | binop op a b => exact False.elim (d4 op a b rfl)
    | «let» id a b => exact False.elim (d5 id a b rfl)
    | block es => exact False.elim (d6 es rfl)
    | app f args => simp [lowerExpr] at h
    | lam p b => simp [lowerExpr] at h
    | ifThenElse c t f => simp [lowerExpr] at h
    | whileLoop c b => simp [lowerExpr] at h
    | «match» s a => simp [lowerExpr] at h
    | infer => simp [lowerExpr] at h
  · -- block, empty
    intro ρ supply v' is s' h _hs _hf henv fenv _hrel fenv' hexec
    simp only [lowerBlock] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hfe : fenv' = ⟨(fenv.env).update supply Value.unit, fenv.store⟩ := by
      have h' : some ⟨(fenv.env).update supply Value.unit, fenv.store⟩ = some fenv' := by
        simpa [execInstrsFull, evalInstrFull] using hexec
      exact (Option.some.inj h').symm
    subst hfe
    exact ⟨[], 1, by simp, by simp [Env.update], rfl⟩
  · -- block, singleton
    intro ρ supply e ih v' is' s' h hs hf henv fenv hrel fenv' hexec
    simp only [lowerBlock] at h
    obtain ⟨w, fuel, heval, hreg, hstore⟩ :=
      ih v' is' s' h (hs e (by simp)) hf henv fenv hrel fenv' hexec
    refine ⟨[w], fuel, ?_, ?_, hstore⟩
    · have hmm : List.mapM (evalHIR fuel henv) (e :: [])
          = some (HIR.Expr.lit w :: ([] : List Value).map HIR.Expr.lit) :=
        (mapM_cons_eq (evalHIR fuel henv) e [] (HIR.Expr.lit w) []).mpr
          ⟨heval, by simp⟩
      simpa using hmm
    · simpa using hreg
  · -- block, cons
    intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' h hs hf henv fenv hrel fenv' hexec
    simp only [lowerBlock, h1, h2] at h
    have hpair := Option.some.inj h
    have his : is' = ib ++ ib' :=
      (congrArg (fun p : ValId × List Instr × Nat => p.2.1) hpair).symm
    have hvv : v' = vb' :=
      (congrArg (fun p : ValId × List Instr × Nat => p.1) hpair).symm
    rw [his, execInstrsFull_append] at hexec
    cases hpre : execInstrsFull fenv ib with
    | none => rw [hpre] at hexec; simp at hexec
    | some fenv1 =>
        rw [hpre] at hexec
        have hexec1 : execInstrsFull fenv1 ib' = some fenv' := by simpa using hexec
        obtain ⟨wa, fuelE, hevalE, _hregE, hstoreE⟩ :=
          ihE vb ib s2 h1 (hs e (by simp)) hf henv fenv hrel fenv1 hpre
        have hf' : FreshAbove ρ s2 :=
          FreshAbove.mono ρ supply s2 (lower_mono.1 _ _ _ _ _ _ h1) hf
        have hrel1 : RelEnv henv ρ fenv1.env :=
          RelEnv_exec henv ρ supply e vb ib s2 h1 fenv fenv1 hrel hf hpre
        obtain ⟨vs, fuelEs, hmapEs, hregEs, hstoreEs⟩ :=
          ihEs vb' ib' s2' h2 (fun x hx => hs x (List.mem_cons_of_mem e hx)) hf'
            henv fenv1 hrel1 fenv' hexec1
        have hE : evalHIR (max fuelE fuelEs) henv e = some (.lit wa) :=
          evalHIR_mono fuelE (max fuelE fuelEs) henv e (.lit wa)
            (Nat.le_max_left _ _) (IsStraight_to_SLExpr (hs e (by simp))) hevalE
        have hEs : es.mapM (evalHIR (max fuelE fuelEs) henv)
            = some (vs.map HIR.Expr.lit) :=
          mapM_evalHIR_mono fuelEs (max fuelE fuelEs) (Nat.le_max_right _ _) henv es vs
            (fun x hx => IsStraight_to_SLExpr (hs x (List.mem_cons_of_mem e hx))) hmapEs
        have hmap : (e :: es).mapM (evalHIR (max fuelE fuelEs) henv)
            = some (HIR.Expr.lit wa :: vs.map HIR.Expr.lit) :=
          (mapM_cons_eq (evalHIR (max fuelE fuelEs) henv) e es (HIR.Expr.lit wa)
            (vs.map HIR.Expr.lit)).mpr ⟨hE, hEs⟩
        have hne_vs : vs ≠ [] := by
          intro hv
          have hlen := mapM_length (evalHIR fuelEs henv) es (vs.map HIR.Expr.lit) hmapEs
          rw [hv] at hlen
          cases es with
          | nil => exact absurd rfl hne
          | cons x xs => simp at hlen
        refine ⟨wa :: vs, max fuelE fuelEs, ?_, ?_, ?_⟩
        · simpa using hmap
        · rw [getLastD_cons_of_ne hne_vs, hvv]
          exact hregEs
        · rw [hstoreEs, hstoreE]
  · -- block, tail fail
    intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · -- block, head fail
    intro ρ supply e es hne hfail ihE v' is' s' h
    simp only [lowerBlock, hfail] at h
    simp at h

/-! ## Statement fragment: predicate, budget, and env bookkeeping -/

/-- The value a run outcome carries. On the straight-line fragment an
outcome is `.value` (no `return` reached) or `.returned` (a `return`
fired); the control-flow outcomes carry no value. -/
def runValue? : HFlow → Option HIR.Expr
  | .value e => some e
  | .returned e => some e
  | _ => none

/-- Statements the lowering accepts, each carrying the budget its
expression positions need. `budget` is 256 at the program level: the
pattern is the runner's own fixed expression fuel, so the statement
bridge can feed `runHIRStmts` directly. `returnStmt` stops the sequence,
so its tail is unconstrained (and never lowered). -/
inductive StraightStmts (budget : Nat) : List HIR.Stmt → Prop where
  | nil : StraightStmts budget []
  | exprStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → StraightStmts budget rest →
      StraightStmts budget (.exprStmt e :: rest)
  | varDecl (id : HIR.Id) (τ : Typ) (init : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight init → SLWeight init < budget → StraightStmts budget rest →
      StraightStmts budget (.varDecl id τ init :: rest)
  | assign (id : HIR.Id) (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → StraightStmts budget rest →
      StraightStmts budget (.assign id e :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget →
      StraightStmts budget (.returnStmt e :: rest)
  | nop (rest : List HIR.Stmt) :
      StraightStmts budget rest → StraightStmts budget (.nop :: rest)

/-- Projections rather than `cases`: `cases` on the predicate in a proof
arm can eliminate locals the arm still needs, the same trap the
expression-side `IsStraight_*` lemmas avoid. -/
theorem StraightStmts_exprStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : StraightStmts budget (.exprStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ StraightStmts budget rest := by
  cases h with
  | exprStmt _ _ hs hb hr => exact ⟨hs, hb, hr⟩

theorem StraightStmts_varDecl {budget : Nat} {id : HIR.Id} {τ : Typ}
    {init : HIR.Expr} {rest : List HIR.Stmt}
    (h : StraightStmts budget (.varDecl id τ init :: rest)) :
    IsStraight init ∧ SLWeight init < budget ∧ StraightStmts budget rest := by
  cases h with
  | varDecl _ _ _ _ hs hb hr => exact ⟨hs, hb, hr⟩

theorem StraightStmts_assign {budget : Nat} {id : HIR.Id} {e : HIR.Expr}
    {rest : List HIR.Stmt} (h : StraightStmts budget (.assign id e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ StraightStmts budget rest := by
  cases h with
  | assign _ _ _ hs hb hr => exact ⟨hs, hb, hr⟩

theorem StraightStmts_returnStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : StraightStmts budget (.returnStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | returnStmt _ _ hs hb => exact ⟨hs, hb⟩

theorem StraightStmts_nop {budget : Nat} {rest : List HIR.Stmt}
    (h : StraightStmts budget (.nop :: rest)) : StraightStmts budget rest := by
  cases h with
  | nop _ hr => exact hr

/-- An expression that fits the runner's budget evaluates at `256`
whenever it evaluates at all: the weight bound plus fuel monotonicity. -/
theorem evalHIR_256 (fuel : Nat) (env : HEnv) (e : HIR.Expr) (r : HIR.Expr)
    (hb : SLWeight e < 256) (hs : SLExpr e) (h : evalHIR fuel env e = some r) :
    evalHIR 256 env e = some r :=
  evalHIR_budget 256 env e r (by omega) hs ⟨fuel, h⟩

/-! ## Assignment: `updAssoc` mirrors `updateHEnv` -/

/-- Updating a present name makes it read back as the new value. -/
theorem lookupHEnv_updateHEnv_id {henv : HEnv} {id : HIR.Id} {w : HIR.Expr}
    (h : lookupHEnv henv id ≠ none) :
    lookupHEnv (updateHEnv henv id w) id = some w := by
  induction henv with
  | nil => simp [lookupHEnv] at h
  | cons p rest ih =>
      obtain ⟨j, v⟩ := p
      by_cases hji : j = id
      · subst hji
        simp [updateHEnv, lookupHEnv]
      · have hr : lookupHEnv rest id ≠ none := by
          simpa [lookupHEnv, hji] using h
        simpa [updateHEnv, lookupHEnv, hji] using ih hr

/-- Updating one name leaves every other name's lookup alone. -/
theorem lookupHEnv_updateHEnv_ne {henv : HEnv} {id j : HIR.Id} {w : HIR.Expr}
    (hne : ¬ id = j) :
    lookupHEnv (updateHEnv henv id w) j = lookupHEnv henv j := by
  induction henv with
  | nil => simp [updateHEnv, lookupHEnv]
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      by_cases hki : k = id
      · subst hki
        simp [updateHEnv, lookupHEnv, hne]
      · by_cases hkj : k = j
        · subst hkj
          simp [updateHEnv, lookupHEnv, hki]
        · simp [updateHEnv, lookupHEnv, hki, hkj, ih]

/-- Assignment preserves the environment relation: `updateHEnv` and
`updAssoc` both replace the first binding of the assigned name and leave
the other names alone, and the new value is the register's value. -/
theorem rhoLookup_updAssoc_id (ρ : List (HIR.Id × ValId)) (id : HIR.Id) (v : ValId) :
    rhoLookup (updAssoc ρ id v) id = (rhoLookup ρ id).map (fun _ => v) := by
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, u0⟩ := p
      by_cases hki : k = id
      · have h1 : updAssoc ((k, u0) :: rest) id v = (k, v) :: rest := by
          show (if k = id then (k, v) :: rest
            else (k, u0) :: updAssoc rest id v) = (k, v) :: rest
          rw [if_pos hki]
        have h2 : rhoLookup ((k, u0) :: rest) id = some u0 := by
          show (if k = id then some u0 else rhoLookup rest id) = some u0
          rw [if_pos hki]
        have h3 : rhoLookup ((k, v) :: rest) id = some v := by
          show (if k = id then some v else rhoLookup rest id) = some v
          rw [if_pos hki]
        rw [h1, h3, h2, Option.map_some]
      · have h1 : updAssoc ((k, u0) :: rest) id v = (k, u0) :: updAssoc rest id v := by
          show (if k = id then (k, v) :: rest
            else (k, u0) :: updAssoc rest id v) = (k, u0) :: updAssoc rest id v
          rw [if_neg hki]
        have h2 : rhoLookup ((k, u0) :: rest) id = rhoLookup rest id := by
          show (if k = id then some u0 else rhoLookup rest id) = rhoLookup rest id
          rw [if_neg hki]
        have h3 : rhoLookup ((k, u0) :: updAssoc rest id v) id
            = rhoLookup (updAssoc rest id v) id := by
          show (if k = id then some u0 else rhoLookup (updAssoc rest id v) id)
            = rhoLookup (updAssoc rest id v) id
          rw [if_neg hki]
        rw [h1, h3, ih, h2]

/-- Assignment leaves every other register alone. -/
theorem rhoLookup_updAssoc_ne {id j : HIR.Id} {v : ValId} (hne : ¬ id = j) :
    ∀ ρ : List (HIR.Id × ValId), rhoLookup (updAssoc ρ id v) j = rhoLookup ρ j := by
  intro ρ
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, u0⟩ := p
      by_cases hki : k = id
      · have h1 : updAssoc ((k, u0) :: rest) id v = (k, v) :: rest := by
          show (if k = id then (k, v) :: rest
            else (k, u0) :: updAssoc rest id v) = (k, v) :: rest
          rw [if_pos hki]
        have hkj : ¬ k = j := fun h => hne (hki.symm.trans h)
        have h2 : rhoLookup ((k, u0) :: rest) j = rhoLookup rest j := by
          show (if k = j then some u0 else rhoLookup rest j) = rhoLookup rest j
          rw [if_neg hkj]
        have h3 : rhoLookup ((k, v) :: rest) j = rhoLookup rest j := by
          show (if k = j then some v else rhoLookup rest j) = rhoLookup rest j
          rw [if_neg hkj]
        rw [h1, h3, h2]
      · have h1 : updAssoc ((k, u0) :: rest) id v
            = (k, u0) :: updAssoc rest id v := by
          show (if k = id then (k, v) :: rest
            else (k, u0) :: updAssoc rest id v) = (k, u0) :: updAssoc rest id v
          rw [if_neg hki]
        rw [h1]
        by_cases hkj : k = j
        · have h2 : rhoLookup ((k, u0) :: rest) j = some u0 := by
            show (if k = j then some u0 else rhoLookup rest j) = some u0
            rw [if_pos hkj]
          have h3 : rhoLookup ((k, u0) :: updAssoc rest id v) j = some u0 := by
            show (if k = j then some u0 else rhoLookup (updAssoc rest id v) j) = some u0
            rw [if_pos hkj]
          rw [h3, h2]
        · have h2 : rhoLookup ((k, u0) :: rest) j = rhoLookup rest j := by
            show (if k = j then some u0 else rhoLookup rest j) = rhoLookup rest j
            rw [if_neg hkj]
          have h3 : rhoLookup ((k, u0) :: updAssoc rest id v) j
              = rhoLookup (updAssoc rest id v) j := by
            show (if k = j then some u0 else rhoLookup (updAssoc rest id v) j)
              = rhoLookup (updAssoc rest id v) j
            rw [if_neg hkj]
          rw [h3, h2, ih]

/-- Assignment preserves the environment relation: both sides replace the
first binding of the assigned name, and the new value is the register's
value (the evaluated expression's result). -/
theorem RelEnv_update (ρ : List (HIR.Id × ValId)) (henv : HEnv)
    (env : Morph.MIR.Env) (id : HIR.Id) (v : ValId) (w : Value)
    (hrel : RelEnv henv ρ env) (hreg : env v = some w) :
    RelEnv (updateHEnv henv id (.lit w)) (updAssoc ρ id v) env := by
  intro j u hlook
  by_cases hji : id = j
  · rw [← hji] at hlook ⊢
    rw [rhoLookup_updAssoc_id] at hlook
    cases hr : rhoLookup ρ id with
    | none => rw [hr] at hlook; simp at hlook
    | some u0 =>
        rw [hr] at hlook
        simp only [Option.map_some, Option.some.injEq] at hlook
        obtain ⟨w', hlookH, -⟩ := hrel id u0 hr
        refine ⟨w, lookupHEnv_updateHEnv_id ?_, ?_⟩
        · simp [hlookH]
        · rw [← hlook]
          exact hreg
  · have hlook' : rhoLookup ρ j = some u := by
      rw [rhoLookup_updAssoc_ne hji] at hlook
      exact hlook
    obtain ⟨w', hlookH, hreg'⟩ := hrel j u hlook'
    exact ⟨w', by rw [lookupHEnv_updateHEnv_ne hji]; exact hlookH, hreg'⟩

/-! ## Statement bridge -/

/-- Statement-level bridge: when `lowerStmts` succeeds on the straight-line
fragment and the emitted instructions run, the HIR statement machine reaches
a value that the lowering's register holds and the store is untouched.
`lastVal`/`acc` carry the running program value — the register the lowering
threads forward, and the literal sitting in it — so the accumulator that
`runHIRStmts` passes along is the same value on both sides. -/
theorem lowerStmts_correct :
    ∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (lastVal : ValId)
      (ss : List HIR.Stmt) (ρ' : List (HIR.Id × ValId)) (v : ValId)
      (is : List Instr) (s' : Nat),
      lowerStmts ρ supply lastVal ss = some (ρ', v, is, s') →
      StraightStmts 256 ss → FreshAbove ρ supply → lastVal < supply →
      ∀ (acc : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env → fenv.env lastVal = some acc →
      ∀ (fenv' : FullEnv), execInstrsFull fenv is = some fenv' →
      ∃ (w : Value) (fuel : Nat) (henv' : HEnv) (out : HFlow),
        runHIRStmts fuel henv ss (.value (.lit acc)) = (out, henv') ∧
        runValue? out = some (.lit w) ∧
        fenv'.env v = some w ∧ fenv'.store = fenv.store ∧
        RelEnv henv' ρ' fenv'.env := by
  intro ρ supply lastVal ss
  induction ss generalizing ρ supply lastVal with
  | nil =>
      intro ρ' v is s' h _hss _hf _hlast acc henv fenv hrel hacc fenv' hexec
      simp only [lowerStmts] at h
      have hp : (ρ, lastVal, ([] : List Instr), supply) = (ρ', v, is, s') :=
        Option.some.inj h
      have hρ' : ρ' = ρ :=
        (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
      have hv : v = lastVal :=
        (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
      have his : is = [] :=
        (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
      have hst : fenv' = fenv := by
        have h' : execInstrsFull fenv [] = some fenv' := by rw [← his]; exact hexec
        rw [execInstrsFull_nil] at h'
        exact (Option.some.inj h').symm
      exact ⟨acc, 1, henv, .value (.lit acc), rfl, rfl, by rw [hv, hst]; exact hacc,
        by rw [hst], by rw [hρ', hst]; exact hrel⟩
  | cons st rest ih =>
    cases st with
    | exprStmt e =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fenv' hexec
      obtain ⟨hstr, hb, hss'⟩ := StraightStmts_exprStmt hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨v0, ie, s1⟩ := p
        rw [he] at h
        simp only [] at h
        cases hr : lowerStmts ρ s1 v0 rest with
        | none => rw [hr] at h; simp at h
        | some q =>
          obtain ⟨ρ'', v', ie', s2⟩ := q
          rw [hr] at h
          simp only [] at h
          have hp : (ρ'', v', ie ++ ie', s2) = (ρ', v, is, s') := Option.some.inj h
          have hρ' : ρ' = ρ'' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
          have hv : v = v' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
          have his : is = ie ++ ie' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
          rw [his, execInstrsFull_append] at hexec
          cases hpre : execInstrsFull fenv ie with
          | none => rw [hpre] at hexec; simp at hexec
          | some fenv1 =>
            rw [hpre] at hexec
            have hexec1 : execInstrsFull fenv1 ie' = some fenv' := by simpa using hexec
            obtain ⟨w, fuelE, hevalE, hregE, hstoreE⟩ :=
              lower_correct.1 ρ supply e v0 ie s1 he hstr hf henv fenv hrel fenv1 hpre
            have h256 : evalHIR 256 henv e = some (.lit w) :=
              evalHIR_256 fuelE henv e (.lit w) hb (IsStraight_to_SLExpr hstr) hevalE
            have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
            have hf1 : FreshAbove ρ s1 := FreshAbove.mono ρ supply s1 hs1 hf
            have hrel1 : RelEnv henv ρ fenv1.env :=
              RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1 hrel hf hpre
            have hlast1 : v0 < s1 := lower_result_lt.1 ρ supply e v0 ie s1 he hf
            obtain ⟨w', fuelR, henv', out, hrun, hvalR, hregR, hstoreR, hrelR⟩ :=
              ih ρ s1 v0 ρ'' v' ie' s2 hr hss' hf1 hlast1 w henv fenv1 hrel1 hregE
                fenv' hexec1
            have hstep : runHIRStmts (fuelR + 1) henv (.exprStmt e :: rest)
                (.value (.lit acc)) =
                (match evalHIR 256 henv e with
                  | none => (HFlow.stuck, henv)
                  | some v => runHIRStmts fuelR henv rest (.value v)) := rfl
            refine ⟨w', fuelR + 1, henv', out, ?_, hvalR, by rw [hv]; exact hregR,
              by rw [hstoreR, hstoreE], by rw [hρ']; exact hrelR⟩
            rw [hstep, h256]
            exact hrun
    | varDecl id τ init =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fenv' hexec
      obtain ⟨hstr, hb, hss'⟩ := StraightStmts_varDecl hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply init with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨va, ia, s1⟩ := p
        rw [he] at h
        simp only [] at h
        cases hr : lowerStmts ((id, va) :: ρ) s1 lastVal rest with
        | none => rw [hr] at h; simp at h
        | some q =>
          obtain ⟨ρ'', v', ia', s2⟩ := q
          rw [hr] at h
          simp only [] at h
          have hp : (ρ'', v', ia ++ ia', s2) = (ρ', v, is, s') := Option.some.inj h
          have hρ' : ρ' = ρ'' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
          have hv : v = v' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
          have his : is = ia ++ ia' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
          rw [his, execInstrsFull_append] at hexec
          cases hpre : execInstrsFull fenv ia with
          | none => rw [hpre] at hexec; simp at hexec
          | some fenv1 =>
            rw [hpre] at hexec
            have hexec1 : execInstrsFull fenv1 ia' = some fenv' := by simpa using hexec
            obtain ⟨w, fuelE, hevalE, hregE, hstoreE⟩ :=
              lower_correct.1 ρ supply init va ia s1 he hstr hf henv fenv hrel fenv1 hpre
            have h256 : evalHIR 256 henv init = some (.lit w) :=
              evalHIR_256 fuelE henv init (.lit w) hb (IsStraight_to_SLExpr hstr) hevalE
            have hva : va < s1 := lower_result_lt.1 ρ supply init va ia s1 he hf
            have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
            have hf1 : FreshAbove ((id, va) :: ρ) s1 := by
              intro j u hmem
              rcases List.mem_cons.mp hmem with heq | hmem
              · cases heq
                exact hva
              · exact Nat.lt_of_lt_of_le (hf j u hmem) hs1
            have hrel1 : RelEnv henv ρ fenv1.env :=
              RelEnv_exec henv ρ supply init va ia s1 he fenv fenv1 hrel hf hpre
            have hrel2 : RelEnv ((id, .lit w) :: henv) ((id, va) :: ρ) fenv1.env := by
              intro j u hlook
              by_cases hid : id = j
              · subst hid
                have hu : u = va := by
                  have hh : rhoLookup ((id, va) :: ρ) id = some va :=
                    rhoLookup_cons_head id va ρ
                  rw [hh] at hlook
                  exact (Option.some.inj hlook).symm
                subst hu
                exact ⟨w, by simp [lookupHEnv], hregE⟩
              · have hlook' : rhoLookup ρ j = some u := by
                  rw [rhoLookup_cons_ne hid] at hlook
                  exact hlook
                obtain ⟨w', hlookH, hreg⟩ := hrel1 j u hlook'
                exact ⟨w', by rw [lookupHEnv_cons_ne hid]; exact hlookH, hreg⟩
            have hacc1 : fenv1.env lastVal = some acc := by
              rw [lower_preserv_regs ρ supply init va ia s1 he fenv fenv1 hpre lastVal hlast]
              exact hacc
            have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
            obtain ⟨w', fuelR, henv', out, hrun, hvalR, hregR, hstoreR, hrelR⟩ :=
              ih ((id, va) :: ρ) s1 lastVal ρ'' v' ia' s2 hr hss' hf1 hlast1 acc
                ((id, .lit w) :: henv) fenv1 hrel2 hacc1 fenv' hexec1
            have hstep : runHIRStmts (fuelR + 1) henv (.varDecl id τ init :: rest)
                (.value (.lit acc)) =
                (match evalHIR 256 henv init with
                  | none => (HFlow.stuck, henv)
                  | some v => runHIRStmts fuelR ((id, v) :: henv) rest (.value (.lit acc))) := rfl
            refine ⟨w', fuelR + 1, henv', out, ?_, hvalR, by rw [hv]; exact hregR,
              by rw [hstoreR, hstoreE], by rw [hρ']; exact hrelR⟩
            rw [hstep, h256]
            exact hrun
    | assign id e =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fenv' hexec
      obtain ⟨hstr, hb, hss'⟩ := StraightStmts_assign hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨v0, ie, s1⟩ := p
        rw [he] at h
        simp only [] at h
        cases hr : lowerStmts (updAssoc ρ id v0) s1 lastVal rest with
        | none => rw [hr] at h; simp at h
        | some q =>
          obtain ⟨ρ'', v', ie', s2⟩ := q
          rw [hr] at h
          simp only [] at h
          have hp : (ρ'', v', ie ++ ie', s2) = (ρ', v, is, s') := Option.some.inj h
          have hρ' : ρ' = ρ'' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
          have hv : v = v' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
          have his : is = ie ++ ie' :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
          rw [his, execInstrsFull_append] at hexec
          cases hpre : execInstrsFull fenv ie with
          | none => rw [hpre] at hexec; simp at hexec
          | some fenv1 =>
            rw [hpre] at hexec
            have hexec1 : execInstrsFull fenv1 ie' = some fenv' := by simpa using hexec
            obtain ⟨w, fuelE, hevalE, hregE, hstoreE⟩ :=
              lower_correct.1 ρ supply e v0 ie s1 he hstr hf henv fenv hrel fenv1 hpre
            have h256 : evalHIR 256 henv e = some (.lit w) :=
              evalHIR_256 fuelE henv e (.lit w) hb (IsStraight_to_SLExpr hstr) hevalE
            have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
            have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
              intro j u hmem
              rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ | hmem
              · rw [hwu]
                exact lower_result_lt.1 ρ supply e v0 ie s1 he hf
              · exact Nat.lt_of_lt_of_le (hf j u hmem) hs1
            have hrel1 : RelEnv henv ρ fenv1.env :=
              RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1 hrel hf hpre
            have hrel2 : RelEnv (updateHEnv henv id (.lit w)) (updAssoc ρ id v0) fenv1.env :=
              RelEnv_update ρ henv fenv1.env id v0 w hrel1 hregE
            have hacc1 : fenv1.env lastVal = some acc := by
              rw [lower_preserv_regs ρ supply e v0 ie s1 he fenv fenv1 hpre lastVal hlast]
              exact hacc
            have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
            obtain ⟨w', fuelR, henv', out, hrun, hvalR, hregR, hstoreR, hrelR⟩ :=
              ih (updAssoc ρ id v0) s1 lastVal ρ'' v' ie' s2 hr hss' hf1 hlast1 acc
                (updateHEnv henv id (.lit w)) fenv1 hrel2 hacc1 fenv' hexec1
            have hstep : runHIRStmts (fuelR + 1) henv (.assign id e :: rest)
                (.value (.lit acc)) =
                (match evalHIR 256 henv e with
                  | none => (HFlow.stuck, henv)
                  | some v => runHIRStmts fuelR (updateHEnv henv id v) rest
                      (.value (.lit acc))) := rfl
            refine ⟨w', fuelR + 1, henv', out, ?_, hvalR, by rw [hv]; exact hregR,
              by rw [hstoreR, hstoreE], by rw [hρ']; exact hrelR⟩
            rw [hstep, h256]
            exact hrun
    | returnStmt e =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fenv' hexec
      obtain ⟨hstr, hb⟩ := StraightStmts_returnStmt hss
      simp only [lowerStmts] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
        obtain ⟨ve, ie, s1⟩ := p
        rw [he] at h
        have hp : (ρ, ve, ie, s1) = (ρ', v, is, s') := Option.some.inj h
        have hρ' : ρ' = ρ :=
          (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
        have hv : v = ve :=
          (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
        have his : is = ie :=
          (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
        rw [his] at hexec
        obtain ⟨w, fuelE, hevalE, hregE, hstoreE⟩ :=
          lower_correct.1 ρ supply e ve ie s1 he hstr hf henv fenv hrel fenv' hexec
        have h256 : evalHIR 256 henv e = some (.lit w) :=
          evalHIR_256 fuelE henv e (.lit w) hb (IsStraight_to_SLExpr hstr) hevalE
        have hrel' : RelEnv henv ρ fenv'.env :=
          RelEnv_exec henv ρ supply e ve ie s1 he fenv fenv' hrel hf hexec
        have hstep : runHIRStmts 1 henv (.returnStmt e :: rest) (.value (.lit acc)) =
            (match evalHIR 256 henv e with
              | none => (HFlow.stuck, henv)
              | some v => (HFlow.returned v, henv)) := rfl
        refine ⟨w, 1, henv, .returned (.lit w), ?_, rfl, by rw [hv]; exact hregE,
          hstoreE, by rw [hρ']; exact hrel'⟩
        rw [hstep, h256]
    | nop =>
      intro ρ' v is s' h hss hf hlast acc henv fenv hrel hacc fenv' hexec
      have hss' := StraightStmts_nop hss
      simp only [lowerStmts] at h
      obtain ⟨w', fuelR, henv', out, hrun, hvalR, hregR, hstoreR, hrelR⟩ :=
        ih ρ supply lastVal ρ' v is s' h hss' hf hlast acc henv fenv hrel hacc fenv' hexec
      exact ⟨w', fuelR + 1, henv', out, hrun, hvalR, hregR, hstoreR, hrelR⟩
    | «break» =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _
      nomatch hss
    | «continue» =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _
      nomatch hss
    | whileLoop cond body =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _
      nomatch hss
    | ifStmt cond th el =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _
      nomatch hss
    | matchStmt scrut arms =>
      intro ρ' v is s' h hss _ _ _ _ _ _ _ _ _
      nomatch hss

/-! ## Program closure: `lowerProgram` to `execFunc` -/

/-
The program lowering prepends a `const 0 .unit` prologue (so register `0`
already holds the empty program's value) and closes the block with
`return_ v`, which is exactly the shape A1's `execFunc_single_block`
consumes. The remaining work is bookkeeping: run the prologue to get the
statement bridge's accumulator, then read the return register.
-/

theorem FreshAbove_nil (n : Nat) : FreshAbove ([] : List (HIR.Id × ValId)) n := by
  intro j u hmem
  simp at hmem

theorem RelEnv_nil (henv : HEnv) (env : Morph.MIR.Env) : RelEnv henv [] env := by
  intro id u hlook
  simp [rhoLookup] at hlook

/-- The `const` prologue: after it, register `0` holds unit and the store is
unchanged, so the statement bridge's accumulator hypothesis is satisfied. -/
theorem execInstrsFull_prologue (store : Store) (is : List Instr) (fenv'' : FullEnv)
    (hexec : execInstrsFull ⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩ is
      = some fenv'') :
    execInstrsFull ⟨fun _ => none, store⟩ ([.const 0 .unit] ++ is) = some fenv'' := by
  rw [execInstrsFull_append]
  have hc : execInstrsFull ⟨fun _ => none, store⟩ [.const 0 .unit]
      = some ⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩ :=
    rfl
  rw [hc]
  exact hexec

/-- Register `0` after the prologue. -/
theorem prologue_env_zero (store : Store) :
    (⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩ : FullEnv).env 0 = some .unit := by
  simp [Morph.MIR.Env.update]

/-- Program-level `compile_correct` for the straight-line fragment: when
`lowerProgram` accepts a program and its emitted instructions run, `execFunc`
of the produced function returns the value the HIR statement machine reaches,
and reading the lowered result register agrees. The MIR-success hypothesis is
explicit: the bridge is one-directional (D-2/D-4), so it never claims that
lowered code cannot fail on its own. -/
theorem compile_correct (prog : HIR.Program) (func : Func) (store : Store)
    (h : lowerProgram prog = some func) (hss : StraightStmts 256 prog.stmts)
    (ρ' : List (HIR.Id × ValId)) (v : ValId) (is : List Instr) (s' : Nat)
    (hs : lowerStmts [] 1 0 prog.stmts = some (ρ', v, is, s'))
    (fenv'' : FullEnv)
    (hexec : execInstrsFull ⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩ is
      = some fenv'') :
    ∃ (w : Value) (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      execFunc 2 func ⟨fun _ => none, store⟩ = some w ∧
      runHIRStmts fuelH [] prog.stmts (.value (.lit .unit)) = (out, henv') ∧
      runValue? out = some (.lit w) ∧ fenv''.env v = some w := by
  simp only [lowerProgram] at h
  rw [hs] at h
  simp only [] at h
  have hfunc : func = ⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0, .unitType⟩ :=
    (Option.some.inj h).symm
  have hlt : (0 : ValId) < 1 := Nat.zero_lt_one
  obtain ⟨w, fuelH, henv', out, hrun, hval, hreg, -⟩ :=
    lowerStmts_correct [] 1 0 prog.stmts ρ' v is s' hs hss (FreshAbove_nil 1) hlt
      (.unit) [] ⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩
      (RelEnv_nil [] _) (prologue_env_zero store) fenv'' hexec
  have hall : execInstrsFull ⟨fun _ => none, store⟩ ([.const 0 .unit] ++ is) = some fenv'' :=
    execInstrsFull_prologue store is fenv'' hexec
  have hrun2 : execFunc 2 func ⟨fun _ => none, store⟩ = some w := by
    rw [hfunc]
    rw [execFunc_single_block (fuel := 0) _ ⟨0, [.const 0 .unit] ++ is, .return_ v⟩ _ v
      rfl rfl rfl]
    rw [hall]
    exact hreg
  exact ⟨w, fuelH, henv', out, hrun2, hrun, hval, hreg⟩

end Morph.HIRToMIRCorrect

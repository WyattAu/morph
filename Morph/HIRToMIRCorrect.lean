/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIR
import Morph.Frontend.HIREval
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

open Morph.HIRToMIR Morph.MIR Morph.Frontend.HIREval Morph.Core

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

end Morph.HIRToMIRCorrect

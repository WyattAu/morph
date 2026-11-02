/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.HIRInterp
import Morph.LoweringLemmas

/-!
# HIR → MIR lowering, straight-line fragment (loops 95–96, Era 2 Sprint 11)

Stage A of the verified compiler: lower straight-line HIR (literals,
variables, `unop`/`binop` over MIR-representable operators, `let`, `block`;
`varDecl`/`assign`/`exprStmt`/`returnStmt`/`nop` statements) to a
single-block MIR function, and prove it correct.

* Sprint 11 (this file): operator maps, the `IsStraight` fragment
  characterization, `lowerExpr`/`lowerStmts`/`lowerProgram`, and the
  well-formedness theorem (`lowerProgram_WF`) — lowered code passes
  `MIR.WF`.
* Sprint 12 (`Morph.MIR`): the computable checks themselves —
  `wfBlockUse`/`WFCFG`/`WFParams`/`WF`/`WFProg` with soundness,
  completeness, and monotonicity lemmas.
* Sprint 13 (this file): the compositional correctness lemmas the WF
  theorem goes through — supply monotonicity (`lower_mono`), result
  freshness (`lower_result_lt`), and use coverage (`lower_useCheck`,
  `lowerStmts_useCheck`) over the `RanIn` environment invariant.
* Sprint 14: `compile_correct` for the straight-line fragment —
  executing the lowered function yields exactly what
  `evalHIR`/`runHIRStmts` produce — plus control flow (`whileLoop`,
  `match`, calls), which needs multi-block CFGs.

Control flow (`whileLoop`, `match`, calls) is Sprint 14: it needs
multi-block CFGs. The agreement is one-directional (HIR success implies
MIR agreement), like the loop-88 statement preservation.
-/

namespace Morph.HIRToMIR

open Morph.HIR Morph.MIR Morph.Core Morph.Frontend.HIREval

/-! ## Operator maps -/

/-- HIR binary operators MIR represents (`BinOp.not` kept for surface
parity: lowering `app`/`lam` is rejected, but a bare `.not` binop maps). -/
def toBinOp : Operator → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .eq => some .eq
  | .neq => some .neq
  | .lt => some .lt
  | .leq => some .leq
  | .gt => some .gt
  | .geq => some .geq
  | .and => some .and
  | .or => some .or
  | .not => some .not
  | .andb => some .andb
  | .orb => some .orb
  | .xorb => some .xorb
  | .shl => some .shl
  | .shr => some .shr
  | _ => none

/-- Result type of a lowered binop. The `τ` annotation is unchecked
metadata (the oracle ignores it); comparisons and logical ops produce
booleans, the rest integers — matching `Executable.evalBinop`. -/
def binopTyp : BinOp → Typ
  | .eq => .boolType
  | .neq => .boolType
  | .lt => .boolType
  | .leq => .boolType
  | .gt => .boolType
  | .geq => .boolType
  | .and => .boolType
  | .or => .boolType
  | .not => .boolType
  | _ => .intType

/-- HIR unary operators MIR represents. -/
def toUnOp : Operator → Option UnOp
  | .not => some .not
  | .notb => some .notb
  | _ => none

/-- Result type of a lowered unop (same unchecked-metadata status). -/
def unopTyp : UnOp → Typ
  | .not => .boolType
  | .notb => .intType

/-- Pointer operators have no MIR counterpart. -/
example : toBinOp .ptrAdd = none := rfl

/-- `notb` is unary-only, so it is not a binop. -/
example : toBinOp .notb = none := rfl

/-- Comparisons produce booleans. -/
example : binopTyp .lt = .boolType := rfl

/-! ## The straight-line fragment -/

/-- Straight-line HIR expressions: everything `lowerExpr` accepts. The
operator side-conditions keep the characterization exact: membership
implies lowering succeeds (given a covering environment), and lowering
success implies membership. -/
inductive IsStraight : HIR.Expr → Prop where
  | var (id : HIR.Id) : IsStraight (.var id)
  | lit (v : Value) : IsStraight (.lit v)
  | unop (op : Operator) (e : HIR.Expr) (_ : toUnOp op ≠ none) :
      IsStraight e → IsStraight (.unop op e)
  | binop (op : Operator) (a b : HIR.Expr) (_ : toBinOp op ≠ none) :
      IsStraight a → IsStraight b → IsStraight (.binop op a b)
  | let_ (id : HIR.Id) (init body : HIR.Expr) :
      IsStraight init → IsStraight body → IsStraight (.let id init body)
  | block (es : List HIR.Expr) (_ : ∀ e ∈ es, IsStraight e) :
      IsStraight (.block es)

/-- First-match register lookup, mirroring `lookupHEnv`. -/
def rhoLookup : List (HIR.Id × ValId) → HIR.Id → Option ValId
  | [], _ => none
  | (j, v) :: rest, id => if j = id then some v else rhoLookup rest id

/-- Replace-or-unchanged register update, mirroring `updateHEnv`
(assignment never introduces a name). -/
def updAssoc : List (HIR.Id × ValId) → HIR.Id → ValId → List (HIR.Id × ValId)
  | [], _, _ => []
  | (j, w) :: rest, id, v =>
      if j = id then (j, v) :: rest else (j, w) :: updAssoc rest id v

/-- Freshness: every mapped register is below the supply. Lowering
allocates upward from `supply` and never reuses a mapped register. -/
def FreshAbove (ρ : List (HIR.Id × ValId)) (lo : Nat) : Prop :=
  ∀ j v, (j, v) ∈ ρ → v < lo

theorem FreshAbove.mono (ρ : List (HIR.Id × ValId)) (lo lo' : Nat)
    (h : lo ≤ lo') (hf : FreshAbove ρ lo) : FreshAbove ρ lo' := by
  intro j v hmem
  exact Nat.lt_of_lt_of_le (hf j v hmem) h

/-! ## Expression lowering -/

mutual
/-- Lower a straight-line expression. `ρ` maps HIR ids to registers,
`supply` is the next fresh register. Returns the result register, the
instructions, and the next supply. -/
def lowerExpr (ρ : List (HIR.Id × ValId)) (supply : Nat) :
    HIR.Expr → Option (ValId × List Instr × Nat)
  | .lit v => some (supply, [.const supply v], supply + 1)
  | .var id =>
      (rhoLookup ρ id).map fun v => (v, [], supply)
  | .unop op e =>
      match toUnOp op, lowerExpr ρ supply e with
      | some u, some (v, is, s) =>
          some (s, is ++ [.unop s u v (unopTyp u)], s + 1)
      | _, _ => none
  | .binop op a b =>
      match toBinOp op, lowerExpr ρ supply a with
      | some bo, some (va, ia, s1) =>
          match lowerExpr ρ s1 b with
          | some (vb, ib, s2) =>
              some (s2, ia ++ ib ++ [.binop s2 bo va vb (binopTyp bo)], s2 + 1)
          | none => none
      | _, _ => none
  | .let id init body =>
      match lowerExpr ρ supply init with
      | some (va, ia, s1) =>
          match lowerExpr ((id, va) :: ρ) s1 body with
          | some (vb, ib, s2) => some (vb, ia ++ ib, s2)
          | none => none
      | none => none
  | .block es => lowerBlock ρ supply es
  | _ => none
/-- Lower a block: sequence the elements, result is the last value;
empty blocks are unit (mirroring `evalHIR`). -/
def lowerBlock (ρ : List (HIR.Id × ValId)) (supply : Nat) :
    List HIR.Expr → Option (ValId × List Instr × Nat)
  | [] => some (supply, [.const supply .unit], supply + 1)
  | [e] => lowerExpr ρ supply e
  | e :: es =>
      -- Thread the supply: the tail allocates after the head.
      match lowerExpr ρ supply e with
      | some (_, ie, s1) =>
          match lowerBlock ρ s1 es with
          | some (v', ibe', s2') => some (v', ie ++ ibe', s2')
          | none => none
      | none => none
end

/-! ## Lowering lemmas: supply monotonicity -/

/-- Registers and supplies only grow. Proved by functional induction
(`lowerExpr.mutual_induct` splits exactly along the match arms). -/
theorem lower_mono :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → supply ≤ s') ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → supply ≤ s') := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → supply ≤ s')
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → supply ≤ s')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ρ supply v v' is s' h
    simp only [lowerExpr] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Nat.le_succ _
  · intro ρ supply id v' is s' h
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some w =>
        simp only [hr] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact Nat.le_refl _
  · intro ρ supply op e u v is s h1 h2 ih v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hle := ih v is s h1
    omega
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
    have hA := ihA va ia s1 h1
    have hB := ihB vb ib s2 h3
    omega
  · intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · intro ρ supply op a b hfail ihA v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some bo =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail bo p.1 p.2.1 p.2.2 hto ha)
  · intro ρ supply id init body vb ib s2 h1 vb' ib' s2' h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hI := ihI vb ib s2 h1
    have hB := ihB vb' ib' s2' h2
    omega
  · intro ρ supply id init body vb ib s2 h1 h2 ihI ihB v' is' s' h
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
    exact Nat.le_succ _
  · intro ρ supply e ih v' is' s' h
    simp only [lowerBlock] at h
    exact ih v' is' s' h
  · intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hE := ihE vb ib s2 h1
    have hEs := ihEs vb' ib' s2' h2
    omega
  · intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · intro ρ supply e es hne hfail ihE v' is' s' h
    simp only [lowerBlock, hfail] at h
    simp at h

/-! ## Statement and program lowering (Sprint 11, second half)

Straight-line statements threaded with the current program value
(`lastVal`, mirroring `runHIRStmts`' accumulator): `exprStmt` evaluates
and becomes the new value, `varDecl` extends the register file (value
preserved), `assign` re-points the identifier (value preserved),
`returnStmt` stops with its value, `nop` skips.
`break`/`continue`/`whileLoop` are control flow: Sprint 14 rejects them
here with `none`. Lowering is total on the fragment, in the same
one-directional style as the expression bridge.
-/
def lowerStmts (ρ : List (HIR.Id × ValId)) (supply : Nat) (lastVal : ValId) :
    List HIR.Stmt → Option (List (HIR.Id × ValId) × ValId × List Instr × Nat)
  | [] => some (ρ, lastVal, [], supply)
  | .exprStmt e :: rest =>
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerStmts ρ s1 v rest with
          | some (ρ', v', ie', s2) => some (ρ', v', ie ++ ie', s2)
          | none => none
      | none => none
  | .varDecl id _ init :: rest =>
      match lowerExpr ρ supply init with
      | some (va, ia, s1) =>
          match lowerStmts ((id, va) :: ρ) s1 lastVal rest with
          | some (ρ', v', ia', s2) => some (ρ', v', ia ++ ia', s2)
          | none => none
      | none => none
  | .assign id e :: rest =>
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerStmts (updAssoc ρ id v) s1 lastVal rest with
          | some (ρ', v', ie', s2) => some (ρ', v', ie ++ ie', s2)
          | none => none
      | none => none
  | .returnStmt e :: _ =>
      (lowerExpr ρ supply e).map fun (v, ie, s1) => (ρ, v, ie, s1)
  | .nop :: rest => lowerStmts ρ supply lastVal rest
  | _ :: _ => none

/-- Lower a whole program to a single-block MIR function. Register `0` is
reserved for `unit` (emitted first, so the empty program returns unit);
user code allocates from supply `1`. The entry block runs every
instruction, then returns the program's value. `retType` is unchecked
metadata (like the `τ` annotations on `unop`/`binop`); the executor and
the WF check never consult it. -/
def lowerProgram (prog : HIR.Program) : Option Func :=
  match lowerStmts [] 1 0 prog.stmts with
  | some (_, v, is, _) =>
      some ⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0, .unitType⟩
  | none => none

/-! ## Lowering lemmas: register-file facts -/

/-- `rhoLookup` only returns registers bound in `ρ`. -/
theorem rhoLookup_some_mem (ρ : List (HIR.Id × ValId)) (id : HIR.Id)
    (w : ValId) (h : rhoLookup ρ id = some w) : (id, w) ∈ ρ := by
  induction ρ with
  | nil => simp [rhoLookup] at h
  | cons p rest ih =>
      obtain ⟨j, v⟩ := p
      simp only [rhoLookup] at h
      by_cases hj : j = id
      · subst hj
        simp at h
        subst h
        exact List.mem_cons.mpr (Or.inl rfl)
      · simp [hj] at h
        exact List.mem_cons.mpr (Or.inr (ih h))

/-- `updAssoc` only ever mentions the assigned value or old bindings. -/
theorem updAssoc_mem (ρ : List (HIR.Id × ValId)) (id : HIR.Id)
    (v : ValId) (j : HIR.Id) (w : ValId)
    (h : (j, w) ∈ updAssoc ρ id v) : (j = id ∧ w = v) ∨ (j, w) ∈ ρ := by
  induction ρ with
  | nil => simp [updAssoc] at h
  | cons p rest ih =>
      obtain ⟨k, u⟩ := p
      simp only [updAssoc] at h
      by_cases hk : k = id
      · rw [if_pos hk] at h
        simp only [List.mem_cons] at h
        rcases h with h | h
        · obtain ⟨rfl, rfl⟩ := h
          exact Or.inl ⟨hk, rfl⟩
        · exact Or.inr (List.mem_cons.mpr (Or.inr h))
      · rw [if_neg hk] at h
        simp only [List.mem_cons] at h
        rcases h with h | h
        · obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- Membership in a flattened definition list distributes over append. -/
theorem mem_defs_append_left {l₁ l₂ : List Instr} {w : ValId}
    (h : w ∈ l₁.flatMap defOf) : w ∈ (l₁ ++ l₂).flatMap defOf := by
  rw [List.flatMap_append]
  exact List.mem_append_left _ h

theorem mem_defs_append_right {l₁ l₂ : List Instr} {w : ValId}
    (h : w ∈ l₂.flatMap defOf) : w ∈ (l₁ ++ l₂).flatMap defOf := by
  rw [List.flatMap_append]
  exact List.mem_append_right _ h

/-- A freshly allocated result register is defined by its own instruction. -/
theorem mem_defs_singleton (x : Instr) (w : ValId) (h : w ∈ defOf x) :
    w ∈ [x].flatMap defOf :=
  List.mem_flatMap.mpr ⟨x, by simp, h⟩

/-! ## Lowering lemmas: result freshness

Every construct returns a register strictly above the incoming supply:
literals and operations allocate; variables read below-supply registers
that `FreshAbove` keeps below the (grown-or-equal) supply. The fail arms
are vacuous, exactly as in `lower_mono`. -/
theorem lower_result_lt :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → FreshAbove ρ supply → v < s') ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → FreshAbove ρ supply → v < s') := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → FreshAbove ρ supply → v < s')
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → FreshAbove ρ supply → v < s')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ρ supply v v' is s' h hFresh
    simp only [lowerExpr] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Nat.lt_succ_self _
  · intro ρ supply id v' is s' h hFresh
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some w =>
        simp only [hr] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact hFresh id v' (rhoLookup_some_mem _ _ _ hr)
  · intro ρ supply op e u v is s h1 h2 _ih v' is' s' h hFresh
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Nat.lt_succ_self _
  · intro ρ supply op e hfail _ih v' is' s' h hFresh
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 _ihA _ihB v' is' s' h hFresh
    simp only [lowerExpr, h1, h2, h3] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Nat.lt_succ_self _
  · intro ρ supply op a b bo va ia s1 h1 h2 h3 _ihA _ihB v' is' s' h hFresh
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · intro ρ supply op a b hfail _ihA v' is' s' h hFresh
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some bo =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail bo p.1 p.2.1 p.2.2 hto ha)
  · intro ρ supply id init body vb ib s2 h1 vb' ib' s2' h2 ihI ihB v' is' s' h hFresh
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hle : supply ≤ s2 := lower_mono.1 _ _ _ _ _ _ h1
    have hlt : vb < s2 := ihI vb ib s2 h1 hFresh
    have hF2 : FreshAbove ((id, vb) :: ρ) s2 := by
      intro j w hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h
      · obtain ⟨rfl, rfl⟩ := h
        exact hlt
      · exact Nat.lt_of_lt_of_le (hFresh j w h) hle
    exact ihB vb' ib' s2' h2 hF2
  · intro ρ supply id init body vb ib s2 h1 h2 _ihI _ihB v' is' s' h hFresh
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · intro ρ supply id init body hfail _ihI v' is' s' h hFresh
    simp only [lowerExpr, hfail] at h
    simp at h
  · intro ρ supply es ih v' is' s' h hFresh
    simp only [lowerExpr] at h
    exact ih v' is' s' h hFresh
  · intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h hFresh
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
  · intro ρ supply v' is' s' h hFresh
    simp only [lowerBlock] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Nat.lt_succ_self _
  · intro ρ supply e ih v' is' s' h hFresh
    simp only [lowerBlock] at h
    exact ih v' is' s' h hFresh
  · intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 _ihE ihEs v' is' s' h hFresh
    simp only [lowerBlock, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hle : supply ≤ s2 := lower_mono.1 _ _ _ _ _ _ h1
    exact ihEs vb' ib' s2' h2 (FreshAbove.mono _ _ _ hle hFresh)
  · intro ρ supply e es hne vb ib s2 h1 h2 _ihE _ihEs v' is' s' h hFresh
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · intro ρ supply e es hne hfail _ihE v' is' s' h hFresh
    simp only [lowerBlock, hfail] at h
    simp at h

/-! ## Lowering lemmas: use coverage

The compositional correctness statement: every use in the emitted code
is covered by the ambient available set (`acc`: params plus prefix
defs), and the result register is either already available or defined
by the emitted code. `RanIn` ties `ρ` to `acc`: lowering extends both
in lockstep (`let` binds the init result and appends its defs), so the
invariant threads through. This concludes with `blockUseGo` directly
— the computable check `wfBlockUse` is built on — so statement and
program lowering compose via `blockUseGo_append`/`blockUseGo_mono`.
-/

/-- Environment coverage: every register bound in `ρ` is available. -/
def RanIn (ρ : List (HIR.Id × ValId)) (avail : List ValId) : Prop :=
  ∀ id u, (id, u) ∈ ρ → u ∈ avail

/-- A trailing instruction's defined register lands in the flattened
defs of the appended code. Discharges the result-register side for
every allocating construct. -/
theorem mem_defs_tail (is : List Instr) (x : Instr) (w : ValId)
    (h : w ∈ defOf x) : w ∈ (is ++ [x]).flatMap defOf := by
  rw [List.flatMap_append]
  exact List.mem_append_right _ (mem_defs_singleton x w h)

/-- A single instruction whose uses are all available passes the
use check. Workhorse for the allocating arms (`lit`, `unop`,
`binop`, empty block): the trailing instruction's uses are the child
result registers, covered by the induction hypotheses. -/
theorem blockUseGo_singleton (avail : List ValId) (i : Instr)
    (h : ∀ v ∈ usesOf i, v ∈ avail) : blockUseGo avail [i] = true := by
  have hall : (usesOf i).all (avail.contains ·) = true := by
    rw [List.all_eq_true]
    intro v hv
    rw [List.contains_iff_mem]
    exact h v hv
  simp only [blockUseGo]
  rw [Bool.and_true]
  exact hall

theorem lower_useCheck :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → FreshAbove ρ supply →
      ∀ (acc : List ValId), RanIn ρ acc →
      blockUseGo acc is = true ∧ (v ∈ acc ∨ v ∈ is.flatMap defOf)) ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → FreshAbove ρ supply →
      ∀ (acc : List ValId), RanIn ρ acc →
      blockUseGo acc is = true ∧ (v ∈ acc ∨ v ∈ is.flatMap defOf)) := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → FreshAbove ρ supply →
      ∀ (acc : List ValId), RanIn ρ acc →
      blockUseGo acc is = true ∧ (v ∈ acc ∨ v ∈ is.flatMap defOf))
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → FreshAbove ρ supply →
      ∀ (acc : List ValId), RanIn ρ acc →
      blockUseGo acc is = true ∧ (v ∈ acc ∨ v ∈ is.flatMap defOf))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ρ supply v v' is s' h hFresh acc hran
    simp only [lowerExpr] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨blockUseGo_singleton acc (.const supply v) (by simp [usesOf]), ?_⟩
    exact Or.inr (mem_defs_tail [] (.const supply v) supply (by simp [defOf]))
  · intro ρ supply id v' is s' h hFresh acc hran
    simp only [lowerExpr] at h
    cases hr : rhoLookup ρ id with
    | none => simp [hr] at h
    | some u =>
        simp only [hr] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, Or.inl (hran id v' (rhoLookup_some_mem _ _ _ hr))⟩
  · intro ρ supply op e u v is s h1 h2 ih v' is' s' h hFresh acc hran
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hsub := ih v is s h1 hFresh acc hran
    have hmem : v ∈ is.flatMap defOf ++ acc := by
      rcases hsub.2 with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    have htail := blockUseGo_singleton (is.flatMap defOf ++ acc)
      (.unop s u v (unopTyp u)) (by
        intro w hw
        simp [usesOf] at hw
        subst hw
        exact hmem)
    refine ⟨blockUseGo_append acc is [.unop s u v (unopTyp u)] hsub.1 htail, ?_⟩
    exact Or.inr (mem_defs_tail _ _ _ (by simp [defOf]))
  · intro ρ supply op e hfail ih v' is' s' h hFresh acc hran
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 ihA ihB v' is' s' h hFresh acc hran
    simp only [lowerExpr, h1, h2, h3] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
    have hF1 : FreshAbove ρ s1 := FreshAbove.mono _ _ _ hle1 hFresh
    have hA := ihA va ia s1 h1 hFresh acc hran
    have hB := ihB vb ib s2 h3 hF1 acc hran
    have hB' : blockUseGo (ia.flatMap defOf ++ acc) ib = true :=
      blockUseGo_mono acc _ _ (fun w hw => List.mem_append_right _ hw) hB.1
    have hAB : blockUseGo acc (ia ++ ib) = true :=
      blockUseGo_append acc ia ib hA.1 hB'
    have hva : va ∈ (ia ++ ib).flatMap defOf ++ acc := by
      rcases hA.2 with h | h
      · exact List.mem_append_right _ h
      · rw [List.flatMap_append]
        exact List.mem_append_left _ (List.mem_append_left _ h)
    have hvb : vb ∈ (ia ++ ib).flatMap defOf ++ acc := by
      rcases hB.2 with h | h
      · exact List.mem_append_right _ h
      · rw [List.flatMap_append]
        exact List.mem_append_left _ (List.mem_append_right _ h)
    have hC := blockUseGo_singleton _ (.binop s2 bo va vb (binopTyp bo)) (by
      intro w hw
      simp [usesOf] at hw
      rcases hw with rfl | rfl
      · exact hva
      · exact hvb)
    refine ⟨blockUseGo_append acc (ia ++ ib) [.binop s2 bo va vb (binopTyp bo)] hAB hC, ?_⟩
    exact Or.inr (mem_defs_tail _ _ _ (by simp [defOf]))
  · intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h hFresh acc hran
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · intro ρ supply op a b hfail ihA v' is' s' h hFresh acc hran
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some bo =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail bo p.1 p.2.1 p.2.2 hto ha)
  · intro ρ supply id init body vb ib s2 h1 vb' ib' s2' h2 ihI ihB v' is' s' h hFresh acc hran
    simp only [lowerExpr, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hle : supply ≤ s2 := lower_mono.1 _ _ _ _ _ _ h1
    have hlt : vb < s2 := lower_result_lt.1 _ _ _ _ _ _ h1 hFresh
    have hF2 : FreshAbove ((id, vb) :: ρ) s2 := by
      intro j u hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h
      · obtain ⟨rfl, rfl⟩ := h
        exact hlt
      · exact Nat.lt_of_lt_of_le (hFresh j u h) hle
    have hI := ihI vb ib s2 h1 hFresh acc hran
    have hacc2 : RanIn ((id, vb) :: ρ) (acc ++ ib.flatMap defOf) := by
      intro j u hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h
      · obtain ⟨rfl, rfl⟩ := h
        rcases hI.2 with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (hran j u h)
    have hB := ihB vb' ib' s2' h2 hF2 (acc ++ ib.flatMap defOf) hacc2
    have hB' : blockUseGo (ib.flatMap defOf ++ acc) ib' = true :=
      blockUseGo_mono _ _ _ (fun w hw => by
        rcases List.mem_append.mp hw with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ h) hB.1
    refine ⟨blockUseGo_append acc ib ib' hI.1 hB', ?_⟩
    rcases hB.2 with h | h
    · rcases List.mem_append.mp h with hl | hr
      · exact Or.inl hl
      · exact Or.inr (by
          rw [List.flatMap_append]
          exact List.mem_append_left _ hr)
    · exact Or.inr (by
        rw [List.flatMap_append]
        exact List.mem_append_right _ h)
  · intro ρ supply id init body vb ib s2 h1 h2 ihI ihB v' is' s' h hFresh acc hran
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · intro ρ supply id init body hfail ihI v' is' s' h hFresh acc hran
    simp only [lowerExpr, hfail] at h
    simp at h
  · intro ρ supply es ih v' is' s' h hFresh acc hran
    simp only [lowerExpr] at h
    exact ih v' is' s' h hFresh acc hran
  · intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h hFresh acc hran
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
  · intro ρ supply v' is' s' h hFresh acc hran
    simp only [lowerBlock] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨blockUseGo_singleton acc (.const supply .unit) (by simp [usesOf]), ?_⟩
    exact Or.inr (mem_defs_tail [] (.const supply .unit) supply (by simp [defOf]))
  · intro ρ supply e ih v' is' s' h hFresh acc hran
    simp only [lowerBlock] at h
    exact ih v' is' s' h hFresh acc hran
  · intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' h hFresh acc hran
    simp only [lowerBlock, h1, h2] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hle : supply ≤ s2 := lower_mono.1 _ _ _ _ _ _ h1
    have hF2 : FreshAbove ρ s2 := FreshAbove.mono _ _ _ hle hFresh
    have hE := ihE vb ib s2 h1 hFresh acc hran
    have hacc2 : RanIn ρ (acc ++ ib.flatMap defOf) :=
      fun j u h => List.mem_append_left _ (hran j u h)
    have hEs := ihEs vb' ib' s2' h2 hF2 (acc ++ ib.flatMap defOf) hacc2
    have hEs' : blockUseGo (ib.flatMap defOf ++ acc) ib' = true :=
      blockUseGo_mono _ _ _ (fun w hw => by
        rcases List.mem_append.mp hw with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ h) hEs.1
    refine ⟨blockUseGo_append acc ib ib' hE.1 hEs', ?_⟩
    rcases hEs.2 with h | h
    · rcases List.mem_append.mp h with hl | hr
      · exact Or.inl hl
      · exact Or.inr (by
          rw [List.flatMap_append]
          exact List.mem_append_left _ hr)
    · exact Or.inr (by
        rw [List.flatMap_append]
        exact List.mem_append_right _ h)
  · intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h hFresh acc hran
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · intro ρ supply e es hne hfail ihE v' is' s' h hFresh acc hran
    simp only [lowerBlock, hfail] at h
    simp at h

/-! ## Statement lowering correctness (Sprint 11, second half)

If statement lowering succeeds, the emitted code passes the use check
and the program value is available or defined — the statement analogue
of `lower_useCheck`, by induction on the statement list. The proof
pattern throughout: `simp only [lowerStmts]` exposes the head match,
`cases` on the head result (single-dependent hypotheses, so no
substitution — the equation rewrites explicitly), then the expression
lemma plus the induction hypothesis compose via `blockUseGo_append`.
`break`/`continue`/`whileLoop` lower to `none`, so those arms reduce
to a contradiction. -/
theorem lowerStmts_useCheck : ∀ (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (lastVal : ValId) (stmts : List HIR.Stmt) (ρ' : List (HIR.Id × ValId))
    (v : ValId) (is : List Instr) (s' : Nat),
    lowerStmts ρ supply lastVal stmts = some (ρ', v, is, s') →
    FreshAbove ρ supply →
    ∀ (acc : List ValId), RanIn ρ acc → lastVal ∈ acc →
    blockUseGo acc is = true ∧ (v ∈ acc ∨ v ∈ is.flatMap defOf) := by
  intro ρ supply lastVal stmts
  induction stmts generalizing ρ supply lastVal with
  | nil =>
      intro ρ' v is s' h hFresh acc hran hlast
      simp only [lowerStmts] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, Or.inl hlast⟩
  | cons s rest ih =>
      cases s with
      | exprStmt e =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          cases he : lowerExpr ρ supply e with
          | none => simp [he] at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              simp only [he] at h
              cases hr : lowerStmts ρ s1 v0 rest with
              | none => simp [hr] at h
              | some q =>
                  obtain ⟨ρ2, v2, ie2, s2⟩ := q
                  simp only [hr] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  have hE := lower_useCheck.1 _ _ _ _ _ _ he hFresh acc hran
                  have hle : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  have hF1 : FreshAbove ρ s1 := FreshAbove.mono _ _ _ hle hFresh
                  have hacc2 : RanIn ρ (acc ++ ie.flatMap defOf) :=
                    fun j u h => List.mem_append_left _ (hran j u h)
                  have hlast2 : v0 ∈ acc ++ ie.flatMap defOf := by
                    rcases hE.2 with h | h
                    · exact List.mem_append_left _ h
                    · exact List.mem_append_right _ h
                  have hR := ih ρ s1 v0 _ _ _ _ hr hF1 _ hacc2 hlast2
                  have hswap : blockUseGo (ie.flatMap defOf ++ acc) ie2 = true :=
                    blockUseGo_mono _ _ _ (fun w hw => by
                      rcases List.mem_append.mp hw with h | h
                      · exact List.mem_append_right _ h
                      · exact List.mem_append_left _ h) hR.1
                  refine ⟨blockUseGo_append acc ie ie2 hE.1 hswap, ?_⟩
                  rcases hR.2 with h | h
                  · rcases List.mem_append.mp h with hl | hrr
                    · exact Or.inl hl
                    · exact Or.inr (mem_defs_append_left hrr)
                  · exact Or.inr (mem_defs_append_right h)
      | varDecl id ty init =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          cases ha : lowerExpr ρ supply init with
          | none => simp [ha] at h
          | some p =>
              obtain ⟨va, ia, s1⟩ := p
              simp only [ha] at h
              cases hr : lowerStmts ((id, va) :: ρ) s1 lastVal rest with
              | none => simp [hr] at h
              | some q =>
                  obtain ⟨ρ2, v2, ia2, s2⟩ := q
                  simp only [hr] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  have hA := lower_useCheck.1 _ _ _ _ _ _ ha hFresh acc hran
                  have hle : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ ha
                  have hlt : va < s1 := lower_result_lt.1 _ _ _ _ _ _ ha hFresh
                  have hF2 : FreshAbove ((id, va) :: ρ) s1 := by
                    intro j u hmem
                    simp only [List.mem_cons] at hmem
                    rcases hmem with h | h
                    · obtain ⟨rfl, rfl⟩ := h
                      exact hlt
                    · exact Nat.lt_of_lt_of_le (hFresh j u h) hle
                  have hacc2 : RanIn ((id, va) :: ρ) (acc ++ ia.flatMap defOf) := by
                    intro j u hmem
                    simp only [List.mem_cons] at hmem
                    rcases hmem with h | h
                    · obtain ⟨rfl, rfl⟩ := h
                      rcases hA.2 with h | h
                      · exact List.mem_append_left _ h
                      · exact List.mem_append_right _ h
                    · exact List.mem_append_left _ (hran j u h)
                  have hlast2 : lastVal ∈ acc ++ ia.flatMap defOf :=
                    List.mem_append_left _ hlast
                  have hR := ih _ s1 lastVal _ _ _ _ hr hF2 _ hacc2 hlast2
                  have hswap : blockUseGo (ia.flatMap defOf ++ acc) ia2 = true :=
                    blockUseGo_mono _ _ _ (fun w hw => by
                      rcases List.mem_append.mp hw with h | h
                      · exact List.mem_append_right _ h
                      · exact List.mem_append_left _ h) hR.1
                  refine ⟨blockUseGo_append acc ia ia2 hA.1 hswap, ?_⟩
                  rcases hR.2 with h | h
                  · rcases List.mem_append.mp h with hl | hrr
                    · exact Or.inl hl
                    · exact Or.inr (mem_defs_append_left hrr)
                  · exact Or.inr (mem_defs_append_right h)
      | assign id e =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          cases he : lowerExpr ρ supply e with
          | none => simp [he] at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              simp only [he] at h
              cases hr : lowerStmts (updAssoc ρ id v0) s1 lastVal rest with
              | none => simp [hr] at h
              | some q =>
                  obtain ⟨ρ2, v2, ie2, s2⟩ := q
                  simp only [hr] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  have hE := lower_useCheck.1 _ _ _ _ _ _ he hFresh acc hran
                  have hle : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  have hlt : v0 < s1 := lower_result_lt.1 _ _ _ _ _ _ he hFresh
                  have hF2 : FreshAbove (updAssoc ρ id v0) s1 := by
                    intro j u hmem
                    rcases updAssoc_mem _ _ _ _ _ hmem with h | h
                    · obtain ⟨rfl, rfl⟩ := h
                      exact hlt
                    · exact Nat.lt_of_lt_of_le (hFresh j u h) hle
                  have hacc2 : RanIn (updAssoc ρ id v0) (acc ++ ie.flatMap defOf) := by
                    intro j u hmem
                    rcases updAssoc_mem _ _ _ _ _ hmem with h | h
                    · obtain ⟨rfl, rfl⟩ := h
                      rcases hE.2 with h | h
                      · exact List.mem_append_left _ h
                      · exact List.mem_append_right _ h
                    · exact List.mem_append_left _ (hran j u h)
                  have hlast2 : lastVal ∈ acc ++ ie.flatMap defOf :=
                    List.mem_append_left _ hlast
                  have hR := ih _ s1 lastVal _ _ _ _ hr hF2 _ hacc2 hlast2
                  have hswap : blockUseGo (ie.flatMap defOf ++ acc) ie2 = true :=
                    blockUseGo_mono _ _ _ (fun w hw => by
                      rcases List.mem_append.mp hw with h | h
                      · exact List.mem_append_right _ h
                      · exact List.mem_append_left _ h) hR.1
                  refine ⟨blockUseGo_append acc ie ie2 hE.1 hswap, ?_⟩
                  rcases hR.2 with h | h
                  · rcases List.mem_append.mp h with hl | hrr
                    · exact Or.inl hl
                    · exact Or.inr (mem_defs_append_left hrr)
                  · exact Or.inr (mem_defs_append_right h)
      | returnStmt e =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          cases he : lowerExpr ρ supply e with
          | none => simp [he] at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              simp only [he, Option.map_some] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact lower_useCheck.1 _ _ _ _ _ _ he hFresh acc hran
      | nop =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          exact ih ρ supply lastVal _ _ _ _ h hFresh acc hran hlast
      | «break» =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          simp at h
      | «continue» =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          simp at h
      | whileLoop c b =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          simp at h
      | ifStmt c th el =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          simp at h
      | matchStmt s arms =>
          intro ρ' v is s' h hFresh acc hran hlast
          simp only [lowerStmts] at h
          simp at h

/-- Closed programs lower to use-checked code: the empty environment is
trivially fresh and covered, and register `0` (the pre-emitted unit) is
available. -/
theorem lowerProgram_useCheck (prog : HIR.Program) (ρ' : List (HIR.Id × ValId))
    (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerStmts [] 1 0 prog.stmts = some (ρ', v, is, s')) :
    blockUseGo ([] : List ValId) ([.const 0 .unit] ++ is) = true := by
  have hFresh : FreshAbove ([] : List (HIR.Id × ValId)) 1 := by
    intro j w hmem
    simp at hmem
  have hran : RanIn ([] : List (HIR.Id × ValId))
      ([.const 0 .unit].flatMap defOf) := by
    intro id u hmem
    simp at hmem
  have hlast : (0 : ValId) ∈ [.const 0 .unit].flatMap defOf :=
    mem_defs_singleton _ _ (by simp [defOf])
  have h1 : blockUseGo ([] : List ValId) [.const 0 .unit] = true :=
    blockUseGo_singleton _ _ (by simp [usesOf])
  have h2 := (lowerStmts_useCheck [] 1 0 _ _ _ _ _ h hFresh _ hran hlast).1
  have h2' : blockUseGo ([.const 0 .unit].flatMap defOf ++ []) is = true := by
    simpa using h2
  exact blockUseGo_append [] [.const 0 .unit] is h1 h2'

/-- The single-block function `lowerProgram` builds inherits the check:
`wfBlockUse` is `blockUseGo` over the block's instructions. -/
theorem lowerProgram_sound (prog : HIR.Program) (ρ' : List (HIR.Id × ValId))
    (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerStmts [] 1 0 prog.stmts = some (ρ', v, is, s')) :
    lowerProgram prog =
      some ⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
        .unitType⟩ := by
  unfold lowerProgram
  rw [h]

/-- Lowered programs are well-formed functions: the CFG side is concrete
(single block `0`, entry `0`, `return_` with no targets) and the use side
is `lowerProgram_useCheck`. -/
theorem lowerProgram_WF (prog : HIR.Program) (ρ' : List (HIR.Id × ValId))
    (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerStmts [] 1 0 prog.stmts = some (ρ', v, is, s')) :
    WF ⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
      .unitType⟩ = true := by
  have hUse := lowerProgram_useCheck prog ρ' v is s' h
  have hUse' : blockUseGo ([] : List ValId) (.const 0 .unit :: is) = true := hUse
  simp [WF, WFCFG, WFParams, wfBlockUse, blockTargets, noDups, hUse']

end Morph.HIRToMIR

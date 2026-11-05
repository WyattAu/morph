/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.MIR
import Morph.Store

/-!
# MIR execution composition (Era 2, Stage A1 groundwork — loop 133)

Unfrozen per `docs/ERA2-UNFREEZE.md`. The straight-line `compile_correct`
(Stage A2) runs lowered single-block functions through `execBlockFuel` /
`execFunc`. That proof needs three facts about the execution machinery in
`Morph.MIR`, proved here so the preservation file can build on them:

* sequential composition for `execInstrsFull` (`nil` / `cons` / `append`);
* pure instructions preserve the store and agree with the `evalInstr`
  oracle on the environment projection;
* a single-block `return_` function's `execFunc` run is exactly
  "run the instructions, read the return register".

All statements are one-directional and fuel-explicit, matching the
pipeline's existing preservation style (`agreeBoth`).
-/

namespace Morph.MIR

open Morph.Core

/-! ## Sequential composition for `execInstrsFull` -/

/-- Running zero instructions is the identity. -/
theorem execInstrsFull_nil (fenv : FullEnv) :
    execInstrsFull fenv [] = some fenv := rfl

/-- Running `i :: is` threads the single-step result. -/
theorem execInstrsFull_cons (fenv : FullEnv) (i : Instr) (is : List Instr) :
    execInstrsFull fenv (i :: is) =
      match evalInstrFull fenv i with
      | none => none
      | some fenv' => execInstrsFull fenv' is := rfl

/-- Sequential composition: running `l₁ ++ l₂` is running `l₁`, then `l₂`
from the resulting environment. The workhorse for lowering correctness,
where each construct appends its own instructions after its children's. -/
theorem execInstrsFull_append (fenv : FullEnv) (l₁ l₂ : List Instr) :
    execInstrsFull fenv (l₁ ++ l₂) =
      match execInstrsFull fenv l₁ with
      | none => none
      | some fenv' => execInstrsFull fenv' l₂ := by
  induction l₁ generalizing fenv with
  | nil => simp [execInstrsFull]
  | cons i rest ih =>
      simp only [List.cons_append, execInstrsFull]
      cases h : evalInstrFull fenv i with
      | none => rfl
      | some fenv' => simp [ih]

/-! ## Pure instructions: store preservation + oracle agreement -/

/-- `const` keeps the store and matches `evalInstr` on the environment. -/
theorem evalInstrFull_const_agrees (env : Env) (store : Store)
    (dst : ValId) (v : Value) :
    evalInstrFull ⟨env, store⟩ (.const dst v) =
      some ⟨(evalInstr env (.const dst v)).getD env, store⟩ := by
  simp [evalInstrFull, evalInstr]

/-- `copy` keeps the store and matches `evalInstr` on the environment. -/
theorem evalInstrFull_copy_agrees (env : Env) (store : Store)
    (dst src : ValId) :
    (evalInstrFull ⟨env, store⟩ (.copy dst src)).map FullEnv.env =
      evalInstr env (.copy dst src) := by
  cases h : env src <;> simp [evalInstrFull, evalInstr, h]

/-- `unop` keeps the store when it succeeds, and succeeds exactly when the
oracle does: the environment projections agree. -/
theorem evalInstrFull_unop_agrees (env : Env) (store : Store)
    (dst : ValId) (op : UnOp) (src : ValId) (τ : Typ) :
    (evalInstrFull ⟨env, store⟩ (.unop dst op src τ)).map FullEnv.env =
      evalInstr env (.unop dst op src τ) := by
  cases h1 : env src with
  | none => simp [evalInstrFull, evalInstr, h1]
  | some v =>
      cases h2 : evalUnOp op v with
      | none => simp [evalInstrFull, evalInstr, h1, h2]
      | some r => simp [evalInstrFull, evalInstr, h1, h2]

/-- `binop` keeps the store when it succeeds, and succeeds exactly when the
oracle does: the environment projections agree. -/
theorem evalInstrFull_binop_agrees (env : Env) (store : Store)
    (dst : ValId) (op : BinOp) (l r : ValId) (τ : Typ) :
    (evalInstrFull ⟨env, store⟩ (.binop dst op l r τ)).map FullEnv.env =
      evalInstr env (.binop dst op l r τ) := by
  cases h1 : env l with
  | none => simp [evalInstrFull, evalInstr, h1]
  | some vl =>
      cases h2 : env r with
      | none => simp [evalInstrFull, evalInstr, h1, h2]
      | some vr =>
          cases h3 : evalBinOp op vl vr with
          | none => simp [evalInstrFull, evalInstr, h1, h2, h3]
          | some v => simp [evalInstrFull, evalInstr, h1, h2, h3]

/-- `const` never touches the store. -/
theorem evalInstrFull_const_store (env : Env) (store : Store)
    (dst : ValId) (v : Value) (fenv' : FullEnv)
    (h : evalInstrFull ⟨env, store⟩ (.const dst v) = some fenv') :
    fenv'.store = store := by
  simp only [evalInstrFull] at h
  cases h
  rfl

/-- `copy` never touches the store on success. -/
theorem evalInstrFull_copy_store (fenv : FullEnv) (dst src : ValId)
    (fenv' : FullEnv)
    (h : evalInstrFull fenv (.copy dst src) = some fenv') :
    fenv'.store = fenv.store := by
  simp only [evalInstrFull] at h
  cases hsrc : fenv.env src with
  | none => simp [hsrc] at h
  | some v =>
      simp [hsrc] at h
      cases h
      rfl

/-- `unop` never touches the store on success. -/
theorem evalInstrFull_unop_store (fenv : FullEnv)
    (dst : ValId) (op : UnOp) (src : ValId) (τ : Typ)
    (fenv' : FullEnv)
    (h : evalInstrFull fenv (.unop dst op src τ) = some fenv') :
    fenv'.store = fenv.store := by
  simp only [evalInstrFull] at h
  cases hsrc : fenv.env src with
  | none => simp [hsrc] at h
  | some v =>
      simp only [hsrc] at h
      cases hop : evalUnOp op v with
      | none => simp [hop] at h
      | some r =>
          simp [hop] at h
          cases h
          rfl

/-- `binop` never touches the store on success. -/
theorem evalInstrFull_binop_store (fenv : FullEnv)
    (dst : ValId) (op : BinOp) (l r : ValId) (τ : Typ)
    (fenv' : FullEnv)
    (h : evalInstrFull fenv (.binop dst op l r τ) = some fenv') :
    fenv'.store = fenv.store := by
  simp only [evalInstrFull] at h
  cases hx : fenv.env l with
  | none => simp [hx] at h
  | some vl =>
      simp only [hx] at h
      cases hy : fenv.env r with
      | none => simp [hy] at h
      | some vr =>
          simp only [hy] at h
          cases hb : evalBinOp op vl vr with
          | none => simp [hb] at h
          | some v =>
              simp [hb] at h
              cases h
              rfl

/-! ## Single-block `return_` reduction -/

/-- Executing a single-block `return_` function is running its instructions
then reading the return register. This is the exact shape the straight-line
`compile_correct` (Stage A2) concludes with. -/
theorem execBlockFuel_return (fuel : Nat) (f : Func)
    (b : Block) (fenv : FullEnv) (v : ValId)
    (hTerm : b.terminator = .return_ v) :
    execBlockFuel (fuel + 1) f b fenv =
      match execInstrsFull fenv b.instrs with
      | none => none
      | some fenv' => fenv'.env v := by
  unfold execBlockFuel
  cases hx : execInstrsFull fenv b.instrs with
  | none => simp
  | some fenv' => simp [hTerm]

/-- Lookup in a single-block program finds the block. -/
theorem findBlock_singleton (f : Func) (b : Block)
    (hBlocks : f.blocks = [b]) (hEntry : f.entry = b.id) :
    findBlock f f.entry = some b := by
  unfold findBlock
  rw [hBlocks]
  simp [hEntry]

/-- `execFunc` on a single-block `return_` program: one fuel unit pays for
the entry-`goto` hop, the rest runs the block. Two fuel levels are stated
so both `execBlockFuel` unfolds (synthetic goto block, then the real block)
land on `succ` arms rather than the zero case. -/
theorem execFunc_single_block (fuel : Nat) (f : Func)
    (b : Block) (fenv : FullEnv) (v : ValId)
    (hBlocks : f.blocks = [b]) (hEntry : f.entry = b.id)
    (hTerm : b.terminator = .return_ v) :
    execFunc (fuel + 2) f fenv =
      match execInstrsFull fenv b.instrs with
      | none => none
      | some fenv' => fenv'.env v := by
  -- The synthetic entry block runs zero instructions, then `goto entry`;
  -- both `execBlockFuel` unfolds (synthetic + real block) reduce by simp.
  unfold execFunc
  have hFind : findBlock f f.entry = some b :=
    findBlock_singleton f b hBlocks hEntry
  cases hx : execInstrsFull fenv b.instrs with
  | none => simp only [execBlockFuel, execInstrsFull, hFind, hx]
  | some fenv' =>
      simp only [execBlockFuel, execInstrsFull, hFind, hTerm, hx]

end Morph.MIR

/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.MIR
import Morph.Executable

/-!
# Lowering the pure-arithmetic subset to MIR (ADR-011 stage 1, partial)

`lower` compiles a closed pure-arithmetic expression (integer literals,
`+`/`-`/`*`, `let`) into a single-block MIR function; `execMain` runs it.

## Status
Definitions complete and compiling. The correctness theorem
(`lowering_correct`: `execMain (lower e) env = exprVal (evalFuel n ctx e)`
for closed `e`, via a strong-agreement induction — see loop-07.md) is
designed but not yet proven; the two supporting lemmas needed are
`evalInstr_write` (per-instruction env-stability outside the written id)
and `execInstrs_agree` (agreement-preservation across instruction lists),
both drafted in the Loop 7 working notes.
-/

namespace Morph.Executable

open Morph.Core
open Morph.Syntax

instance : Inhabited Expr := ⟨Expr.lit Value.unit⟩

/-- Fuel-bounded total clone of the evaluator. This predates loop 38, which made
    `Executable.eval` itself total by fuel; the clone is kept because its
    semantics differ slightly (blocks return the last value, an armless `match`
    yields unit, `forLoop` recurses at `fuel - 1`) and the loop-7 lowering
    agreement proof is stated against exactly these rules. -/
def evalFuel : Nat → Context → Expr → Option Expr
  | 0, _, _ => none
  | fuel+1, ctx, e =>
    match e with
    | .lit v => some (Expr.lit v)
    | .bvar n => ctx.getBv? n
    | .fvar name => ctx.getFv? name
    | .binop op a b => do
        let v1 ← evalFuel fuel ctx a
        let v2 ← evalFuel fuel ctx b
        evalBinop op v1 v2
    | .unop op a => do
        let v ← evalFuel fuel ctx a
        evalUnop op v
    | .let_ a b => do
        let v1 ← evalFuel fuel ctx a
        evalFuel fuel (ctx.pushBv v1) b
    | .ifThenElse c t f => do
        let cv ← evalFuel fuel ctx c
        match cv with
        | Expr.lit (Value.bool true) => evalFuel fuel ctx t
        | Expr.lit (Value.bool false) => evalFuel fuel ctx f
        | _ => none
    | .block exprs => do
        let vs ← exprs.mapM (evalFuel fuel ctx)
        match vs with
        | [] => some (Expr.lit Value.unit)
        | vs' => some vs'.getLast!
    | .app fn args => do
        let fnVal ← evalFuel fuel ctx fn
        match fnVal with
        | Expr.lam n body =>
            if args.length ≠ n then none
            else do
              let argVals ← args.mapM (evalFuel fuel ctx)
              evalFuel fuel ctx (substAll argVals.reverse body)
        | _ => none
    | .forLoop start stop body => do
        let sv ← evalFuel fuel ctx start
        let ev ← evalFuel fuel ctx stop
        match sv, ev with
        | Expr.lit (Value.int a), Expr.lit (Value.int b) =>
            if a < b then do
              let _ ← evalFuel (fuel - 1) (ctx.pushBv (Expr.lit (Value.int a)))
                  (Expr.block body)
              evalFuel (fuel - 1) ctx
                  (Expr.forLoop (Expr.lit (Value.int (a + 1))) stop body)
            else some (Expr.lit Value.unit)
        | _, _ => none
    | .match_ scrut arms => do
        let sv ← evalFuel fuel ctx scrut
        match arms with
        | [] => some (Expr.lit Value.unit)
        | (pat, body) :: rest =>
            match matchPat pat sv with
            | some vs =>
              let ctx' := ctx.pushBvs vs
              match evalFuel fuel ctx' body with
              | some r => some r
              | none => evalFuel fuel ctx (Expr.match_ sv rest)
            | none => evalFuel fuel ctx (Expr.match_ sv rest)
    | .field_ e _ => evalFuel fuel ctx e
    | .pipe e f => do
        let v ← evalFuel fuel ctx e
        evalFuel fuel ctx (Expr.app f [v])
    | .typeAsc e _ => evalFuel fuel ctx e
    | .none_ => some (Expr.lit Value.none)
    | .lam _ _ => some e
    | .refCast e _ => do
        let _ ← evalFuel fuel ctx e
        some (Expr.lit Value.unit)
    | .some_ e => do
        let v ← evalFuel fuel ctx e
        match v with
        | Expr.lit inner => some (Expr.lit (Value.some inner))
        | Expr.none_ => some (Expr.lit (Value.some Value.none))
        | _ => none
    | .ok_ e => do
        let v ← evalFuel fuel ctx e
        match v with
        | Expr.lit inner => some (Expr.lit (Value.ok inner))
        | Expr.none_ => some (Expr.lit (Value.ok Value.none))
        | _ => none
    | .err_ e => do
        let v ← evalFuel fuel ctx e
        match v with
        | Expr.lit inner => some (Expr.lit (Value.err inner))
        | Expr.none_ => some (Expr.lit (Value.err Value.none))
        | _ => none
    | .nullCoalesce e1 e2 => do
        let v1 ← evalFuel fuel ctx e1
        match v1 with
        | Expr.lit (Value.some _) => some v1
        | Expr.lit Value.none => evalFuel fuel ctx e2
        | Expr.some_ _ => some v1
        | Expr.none_ => evalFuel fuel ctx e2
        | _ => none
    | .tuple_ elems => do
        let vals ← elems.mapM (evalFuel fuel ctx)
        if vals.length = elems.length then
          some (Expr.lit (Value.tuple_ (vals.filterMap fun v =>
            match v with | Expr.lit inner => some inner | _ => none)))
        else none
    | .arrayLit elems => do
        let vals ← elems.mapM (evalFuel fuel ctx)
        if vals.length = elems.length then
          some (Expr.lit (Value.array_ (vals.filterMap fun v =>
            match v with | Expr.lit inner => some inner | _ => none)))
        else none
    | .arrayIndex arr idx => do
        let arrVal ← evalFuel fuel ctx arr
        let idxVal ← evalFuel fuel ctx idx
        match arrVal, idxVal with
        | Expr.lit (Value.array_ elems), Expr.lit (Value.int n) =>
            if n ≥ 0 && n < elems.length then
              some (Expr.lit (elems.getD n.toNat Value.unit))
            else none
        | _, _ => none
    | .refCreate e _ _ => do
        let _ ← evalFuel fuel ctx e
        some (Expr.lit (Value.loc 0))
    | .refLoad e => do
        let _ ← evalFuel fuel ctx e
        some (Expr.lit Value.unit)
    | .refStore e v _ => do
        let _ ← evalFuel fuel ctx e
        let _ ← evalFuel fuel ctx v
        some (Expr.lit Value.unit)
    | .refFree e => do
        let _ ← evalFuel fuel ctx e
        some (Expr.lit Value.unit)
end Morph.Executable

namespace Morph.Lowering

open Morph.Core Morph.Syntax Morph.MIR Morph.Executable

/-! ## The pure-arithmetic fragment -/

/-- The MIR binary operator an arithmetic operator lowers to; `none` for
    operators MIR does not represent (comparisons, division, …). -/
def toBinOp : Operator → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | _ => none

/-- The fragment `lowerIn` handles. The `binop` case carries `bop` together
    with the equation `toBinOp op = some bop`, so membership in `IsPureArith`
    already guarantees the operator translates — without which the
    interpreter (whose `evalBinop` is richer than MIR's) could evaluate an
    expression `lowerIn` rejects. -/
inductive IsPureArith : Expr → Prop where
  | lit (n : Int) : IsPureArith (.lit (.int n))
  | binop (bop : BinOp) (a b : Expr) (hop : toBinOp op = some bop) :
      IsPureArith a → IsPureArith b → IsPureArith (.binop op a b)
  | let_ (a b : Expr) : IsPureArith a → IsPureArith b → IsPureArith (.let_ a b)

/-! ## Lowering -/


/-- Lower `e` to instructions computing it. `paramMap` resolves de Bruijn
    indices to ValIds; `supply` is the next fresh ValId. Returns
    `(resultValId, instructions, nextSupply)`. -/
def lowerIn (paramMap : Nat → ValId) (supply : Nat) : Expr → Option (ValId × List Instr × Nat)
  | .lit (.int n) => some (supply, [Instr.const supply (.int n)], supply + 1)
  | .lit _ => none
  | .bvar n => some (paramMap n, [], supply)
  | .binop op a b =>
      match toBinOp op, lowerIn paramMap supply a with
      | some bop, some (va, ia, s1) =>
          match lowerIn paramMap s1 b with
          | some (vb, ib, s2) =>
              some (s2, ia ++ ib ++ [Instr.binop s2 bop va vb .intType], s2 + 1)
          | none => none
      | _, _ => none
  | .let_ a b =>
      match lowerIn paramMap supply a with
      | some (va, ia, s1) =>
          let pm' := fun n => if n = 0 then va else paramMap (n - 1)
          match lowerIn pm' s1 b with
          | some (vb, ib, s2) => some (vb, ia ++ ib, s2)
          | none => none
      | none => none
  | _ => none

/-- Lower a CLOSED pure-arithmetic expression to a single-block,
    single-return function. Unbound de Bruijn indices lower to `ValId 0`,
    which no instruction writes (supplies start at 1), so such programs
    evaluate to `none` on both sides. -/
def lower (e : Expr) : Option Func :=
  match lowerIn (fun _ => 0) 1 e with
  | some (v, is, _) =>
      some { name := "main", params := []
             blocks := [{ id := 0, instrs := is, terminator := .return_ v }]
             entry := 0, retType := .intType }
  | none => none

/-! ## Execution (single-block fragment) -/

def execInstrs (env : MIR.Env) : List Instr → Option MIR.Env
  | [] => some env
  | i :: is =>
      match evalInstr env i with
      | none => none
      | some env' => execInstrs env' is

/-- Execute a single-block function. -/
def execMain (f : Func) (env : MIR.Env) : Option Value :=
  match f.blocks with
  | [b] =>
      match execInstrs env b.instrs with
      | some env' =>
          match b.terminator with
          | .return_ v => env' v
          | _ => none
      | none => none
  | _ => none

/-- The interpreter result coerced to a Value (our fragment only
    produces `.lit` results). -/
def exprVal (oe : Option Expr) : Option Value :=
  match oe with
  | some (.lit v) => some v
  | _ => none

/-- The bound-variable result coerced to a Value. -/
def bvVal (ctx : Context) (n : Nat) : Option Value :=
  match ctx.getBv? n with
  | some (.lit v) => some v
  | _ => none

end Morph.Lowering

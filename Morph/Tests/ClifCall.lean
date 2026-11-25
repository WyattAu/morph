/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.ClifSimulate
import Morph.ClifCfgEncode
import Morph.ClifEmit

/-!
# Tests for Stage C item C8: calls stop at the encoder, run in the models

`Morph.MIR` executes single-level calls (`execFuncCall`, pinned in
`Morph.Tests.MIR`), and `Morph.ClifTarget` now models them additively
(`CFunc`/`bindCArgs`/`runCallee`/`runCall`): the single-block target has no
`call` instruction by design, so the encoder still refuses call-bearing code
(`instrEncodes_of_hasCall`, pinned below) while resolved callees run through
the call-free `runInstrs`. These pins state the boundary from the target side
plus the value-passing correspondence that ties the two binders together:

* a lone `call` encodes to `none`, and any list containing one is refused;
* call-free code still encodes (the contrast case);
* `bindCArgs` binds on matching arity and fails on mismatch;
* the MIR and CLIF binders agree (`bindCallArgs_bindCArgs_agree`);
* `runCallee` runs a resolved callee, `runCall` stalls on unknown names and
  arity mismatches, and `callee_correct` certifies the run against a `Trace`.
-/

namespace Morph.Tests.ClifCall

open Morph.Clif
open Morph.MIR
open Morph.Core (Typ)

/-- A lone `call` has no CLIF encoding. -/
example : instrEncode (.call (some 0) "add" [0, 1]) = none := rfl

/-- A list containing a `call` is refused, via the general lemma. -/
example : instrEncodes
    [.const 0 (.int 5), .call (some 2) "add" [0, 1]] = none := by
  apply instrEncodes_of_hasCall
  exact ⟨some 2, "add", [0, 1],
    List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))⟩

/-- Call-free code still encodes: the contrast case. -/
example : instrEncodes [.const 0 (.int 5)] =
    some [Morph.Clif.Instr.iconst 0 5] := rfl

/-- Value-passing binds on matching arity (MIR side, pinned for the pair). -/
example : (bindCallArgs [(0, Typ.intType)] [.int 5]).isSome = true := rfl

/-- Arity mismatch fails to bind (MIR side). -/
example : bindCallArgs [(0, Typ.intType)] [] = none :=
  bindCallArgs_length_mismatch (by decide)

/-- Value-passing binds on matching arity (CLIF side). -/
example : (bindCArgs [0] [.int 5]).isSome = true := rfl

/-- Arity mismatch fails to bind (CLIF side). -/
example : bindCArgs [0] [] = none :=
  bindCArgs_length_mismatch (by decide)

/-- The two binders agree whenever the formals name the signature. -/
example (menv cenv)
    (hm : bindCallArgs [(0, Typ.intType)] [.int 5] = some menv)
    (hc : bindCArgs [0] [.int 5] = some cenv) :
    menv = cenv :=
  bindCallArgs_bindCArgs_agree rfl hm hc

/-- A two-argument adder, as a CLIF callable. -/
def addCF : CFunc := ⟨"add", [0, 1], ⟨[.iadd 2 0 1], 2⟩⟩

/-- A call-bearing block is refused by the CFG encoder. -/
example : Cfg.encodeBlock (⟨"f", [], [], 0, .unitType⟩ : Morph.MIR.Func)
    ⟨0, [.call (some 2) "add" [0, 1]], .return_ 2⟩ = none :=
  Cfg.encodeBlock_hasCall ⟨some 2, "add", [0, 1], by simp⟩

/-- A call-bearing function is refused by the CFG encoder. -/
example : Cfg.encodeFunc (⟨"f", [],
    [⟨0, [.call (some 2) "add" [0, 1]], .return_ 2⟩], 0,
    .unitType⟩ : Morph.MIR.Func) = none := by
  apply Cfg.encodeFunc_hasCall
    (b := (⟨0, [.call (some 2) "add" [0, 1]], .return_ 2⟩ :
      Morph.MIR.Block))
  · simp
  · refine ⟨some 2, "add", [0, 1], ?_⟩
    change Morph.MIR.Instr.call (some 2) "add" [0, 1] ∈
      [Morph.MIR.Instr.call (some 2) "add" [0, 1]]
    exact List.mem_cons.mpr (Or.inl rfl)

/-- A resolved callee runs: `5 + 7 = 12`. -/
example : runCallee addCF [.int 5, .int 7] = some (.int 12) := rfl

/-- Unknown callees stall. -/
example : runCall [addCF] "missing" [.int 1] = none :=
  runCall_none_unknown _ _ _ rfl

/-- Arity mismatches stall. -/
example : runCall [addCF] "add" [.int 1] = none :=
  runCall_none_arity [addCF] addCF [.int 1] rfl (by decide)

/-- The simulation certifies the run: the same argument values drive a MIR
`Trace` over the encoded body to the value `runCallee` returns. -/
example : runCallee addCF [.int 5, .int 7] = some (.int 12) :=
  callee_correct (ps := [(0, Typ.intType), (1, Typ.intType)]) (rs := [0, 1])
    (is := [Morph.MIR.Instr.binop 2 .add 0 1 Typ.intType])
    rfl rfl rfl rfl rfl
    (Trace.cons (Step.add (by rfl) (by rfl) ⟨by decide, by decide⟩)
      (Trace.nil _))
    rfl (by rfl)

/-! ## Typed-signature pins (D-7 option B, step 1)

The typed layer classifies values, refuses mismatches and
unrepresentables at the head, and agrees with the MIR binder. -/

/-- Values classify to their ABI types. -/
example : valueTyp (.int 5) = some Typ.intType := rfl

/-- Values classify to their ABI types. -/
example : valueTyp (.bool true) = some Typ.boolType := rfl

/-- `undef` has no call representation. -/
example : valueTyp .undef = none := rfl

/-- Typed binding accepts a matching actual.
`native_decide`: `Typ`'s derived `BEq` computes correctly but does not
reduce in the kernel, so `rfl`/`decide` stall on any goal that evaluates
it; compiled evaluation decides these closed goals. -/
example : (bindTArgs [(0, Typ.intType)] [.int 5]).isSome = true := by
  native_decide

/-- A head type mismatch refuses. -/
example : bindTArgs [(0, Typ.intType)] [.bool true] = none :=
  bindTArgs_head_mismatch rfl (by native_decide)

/-- An unrepresentable head actual refuses. -/
example : bindTArgs [(0, Typ.intType)] [.undef] = none :=
  bindTArgs_head_unrepresentable rfl

/-- The MIR and typed CLIF binders agree on the same formals. -/
example (menv cenv)
    (hm : bindCallArgs [(0, Typ.intType)] [.int 5] = some menv)
    (hc : bindTArgs [(0, Typ.intType)] [.int 5] = some cenv) :
    menv = cenv :=
  bindCallArgs_bindTArgs_agree rfl hm hc

/-! ## Declared-type pins (D-7 option B, step 2)

The mapping, the text, and the per-instruction result types. -/

/-- The mapping covers the ABI types. -/
example : clifTyOfTyp Typ.intType = some .i64 := rfl

/-- The mapping covers the ABI types. -/
example : clifTyOfTyp Typ.boolType = some .i8 := rfl

/-- Strings cross as addresses. -/
example : clifTyOfTyp Typ.stringType = some .addr := rfl

/-- Unit occupies no call slot. -/
example : clifTyOfTyp Typ.unitType = none := rfl

/-- Addresses render as `i64`. -/
example : ClifTy.text .addr = "i64" := rfl

/-- Comparisons produce bools. Fully qualified: `.dst` collides with the
`Cfg.Phi.dst` projection in scope, so trailing-dot notation cannot pick
the `Instr` field. -/
example : Morph.Clif.Instr.resultTyp (.icmp 2 .slt 0 1) = Typ.boolType := rfl

/-- Arithmetic produces ints. -/
example : Morph.Clif.Instr.resultTyp (.iadd 2 0 1) = Typ.intType := rfl

/-- Destinations are read off the constructor. -/
example : Morph.Clif.Instr.dst (.iadd 2 0 1) = 2 := rfl

/-- `step_resultTyp` fires on a concrete step: the written value has the
instruction's result type. The empty file is annotated: bare `none`
would be ambiguous between `Option.none` and `Value.none`. -/
example (env' : Morph.Clif.Env)
    (h : step (fun _ => (none : Option Morph.Core.Value)) (.iconst 3 7) = some env') :
    ∃ v, env' 3 = some v ∧ valueTyp v = some Typ.intType :=
  step_resultTyp h

/-! ## Body-type pins (D-7 option B, step 2)

`lastDef` finds the last writer; an `allI64` body that encodes has
`intType` everywhere, so the computed body type is `intType`. -/

/-- `lastDef` finds the last writer, not the first. -/
example : lastDef [.iconst 0 5, .iadd 2 0 1] 2 = some (.iadd 2 0 1) := rfl

/-- An untouched register keeps its earlier writer. -/
example : lastDef [.iconst 0 5, .iadd 2 0 1] 0 = some (.iconst 0 5) := rfl

/-- The computed body type of a one-instruction int body. -/
example : bodyResultTyp [.iadd 2 0 1] 2 = some Typ.intType := rfl

/-- An `allI64` body encodes to all-`intType` instructions. -/
example (cs : List Morph.Clif.Instr)
    (h : instrEncodes [.const 0 (.int 5), .binop 2 .add 0 1 Typ.intType] = some cs) :
    ∀ c ∈ cs, Morph.Clif.Instr.resultTyp c = Typ.intType :=
  Morph.Codegen.encodes_allI64_int (by decide) h

/-- The computed body type of that encoded body is `intType`. -/
example (cs : List Morph.Clif.Instr) (τ : Typ)
    (h : instrEncodes [.const 0 (.int 5)] = some cs)
    (hb : bodyResultTyp cs 0 = some τ) :
    τ = Typ.intType :=
  Morph.Codegen.encodes_bodyResultTyp_int (by decide) h hb

/-! ## Named-call pins (D-7 option B, slice A)

The target names calls; bare `step` stays program-blind, so a call
stalls there, while tokens round-trip. -/

/-- A call stalls in the program-blind step. -/
example : step (fun _ => (none : Option Morph.Core.Value))
    (.call 2 "add" [0, 1] Typ.intType) = none := rfl

/-- A call writes its declared return register. -/
example : Morph.Clif.Instr.dst (.call 2 "add" [0, 1] Typ.intType) = 2 := rfl

/-- A call's result type is its declared return type. -/
example : Morph.Clif.Instr.resultTyp (.call 2 "add" [0, 1] Typ.boolType)
    = Typ.boolType := rfl

/-- Calls tokenise and parse back. -/
example : parseInstr (toksInstr (.call 2 "add" [0, 1] Typ.intType))
    = some ((.call 2 "add" [0, 1] Typ.intType), []) := by
  simpa using parseInstr_toksInstr (.call 2 "add" [0, 1] Typ.intType) []

/-! ## Explicit-program encoder pins (D-7 option B, slice B1)

With a program the encoder admits int-world calls; without one (and
for unknown callees, arity mismatches, non-`int` results, and
effect-only calls) it refuses exactly as before. -/

/-- The callee side of the test program: `add` takes two ints. The
encoder never looks at the body, only name, params, and return type. -/
def addMIR : Morph.MIR.Func :=
  ⟨"add", [(0, Typ.intType), (1, Typ.intType)], [], 0, Typ.intType⟩

/-- A one-function program. -/
def progAdd : Morph.MIR.Program := ⟨[addMIR]⟩

/-- A known int-world call encodes. -/
example : instrEncode (.call (some 2) "add" [0, 1]) progAdd
    = some (.call 2 "add" [0, 1] Typ.intType) := rfl

/-- Unknown callees refuse, even with a program. -/
example : instrEncode (.call (some 2) "missing" [0, 1]) progAdd = none := rfl

/-- Arity mismatches refuse. -/
example : instrEncode (.call (some 2) "add" [0]) progAdd = none := rfl

/-- Effect-only calls refuse (no destination to write). -/
example : instrEncode (.call none "add" [0, 1]) progAdd = none := rfl

/-- A bool-returning callee refuses (int-world only in slice B1). -/
def notMIR : Morph.MIR.Func :=
  ⟨"notfn", [(0, Typ.boolType)], [], 0, Typ.boolType⟩

example : instrEncode (.call (some 2) "notfn" [0]) ⟨[notMIR]⟩ = none := rfl

/-- A mixed body encodes around its call. -/
example : instrEncodes [.const 0 (.int 5), .call (some 2) "add" [0, 1]] progAdd
    = some [.iconst 0 5,
      Morph.Clif.Instr.call 2 "add" [0, 1] Typ.intType] := rfl

/-- The encoded call satisfies the resolved-call contract. -/
example : callResolved progAdd (.call (some 2) "add" [0, 1]) :=
  ⟨addMIR, rfl, rfl, rfl⟩

/-! ## Typed-runner and stepping pins (D-7 option B, slice B1) -/

/-- The typed `add` callable. -/
def addTCF : TCFunc :=
  ⟨"add", [(0, Typ.intType), (1, Typ.intType)], ⟨[.iadd 2 0 1], 2⟩⟩

/-- A one-callable typed program. -/
def tprogAdd : TCProgram := [addTCF]

/-- A typed call runs. -/
example : (runTCall tprogAdd "add" [.int 5, .int 7]).isSome = true := by
  native_decide

/-- ...to the right value. -/
example : (runTCall tprogAdd "add" [.int 5, .int 7]).map (fun w => w == .int 12)
    = some true := by
  native_decide

/-- Unknown names stall. -/
example : runTCall tprogAdd "missing" [.int 1] = none :=
  runTCall_none_unknown _ _ _ rfl

/-- Arity mismatches stall. -/
example : runTCall tprogAdd "add" [.int 5] = none :=
  runTCall_none_bind tprogAdd addTCF [.int 5] rfl
    (bindTArgs_length_mismatch
      (show ([(0, Typ.intType), (1, Typ.intType)].length ≠ [.int 5].length)
        from by decide))

/-- Type mismatches stall, even past a well-typed head. -/
example : runTCall tprogAdd "add" [.int 5, .bool true] = none :=
  runTCall_none_bind tprogAdd addTCF [.int 5, .bool true] rfl
    (bindTArgs_cons_none (bindTArgs_head_mismatch rfl (by native_decide)))

/-- Pure instructions step program-blind, as before. -/
example : stepIn tprogAdd (fun _ => none) (.iconst 3 7)
    = step (fun _ => none) (.iconst 3 7) := rfl

/-- Unbound actuals stall the call step. -/
example : stepIn tprogAdd (fun _ => none)
    (.call 2 "add" [0, 1] Typ.intType) = none := rfl

/-- A resolved call step writes its return value. -/
example : (stepIn tprogAdd
    (fun r => if r == 0 then some (.int 5)
      else if r == 1 then some (.int 7)
      else (none : Option Morph.Core.Value))
    (.call 2 "add" [0, 1] Typ.intType)).map
    (fun e => match e 2 with | some (.int 12) => true | _ => false)
    = some true := by
  native_decide

/-- The emitter still refuses call-bearing bodies (slice B1 boundary:
the single-function emitter carries no program context). -/
example : Morph.Codegen.emitBlock
    ⟨0, [.const 0 .unit, .call (some 2) "add" [0, 1]], .return_ 2⟩ = none :=
  rfl

end Morph.Tests.ClifCall

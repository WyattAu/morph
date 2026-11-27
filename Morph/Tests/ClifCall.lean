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

/-! ## Explicit-program encoder pins (D-7 option B, slices B1/C1)

With a program the encoder admits slotted calls (any result with a
CLIF slot per the marshal table); without one (and for unknown
callees, arity mismatches, slotless results, and effect-only calls)
it refuses exactly as before. -/

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

/-- A bool-returning callee encodes (slot `.i8`, slice C1). -/
def notMIR : Morph.MIR.Func :=
  ⟨"notfn", [(0, Typ.boolType)], [], 0, Typ.boolType⟩

example : instrEncode (.call (some 2) "notfn" [0]) ⟨[notMIR]⟩
    = some (.call 2 "notfn" [0] Typ.boolType) := rfl

/-- ...and resolves, naming the slot. -/
example : callResolved ⟨[notMIR]⟩ (.call (some 2) "notfn" [0]) :=
  ⟨notMIR, rfl, rfl, Morph.Clif.ClifTy.i8, rfl⟩

/-- A unit-returning callee refuses (no slot). -/
def unitMIR : Morph.MIR.Func :=
  ⟨"unitfn", [(0, Typ.intType)], [], 0, Typ.unitType⟩

example : instrEncode (.call (some 2) "unitfn" [0]) ⟨[unitMIR]⟩ = none := rfl

/-- A mixed body encodes around its call. -/
example : instrEncodes [.const 0 (.int 5), .call (some 2) "add" [0, 1]] progAdd
    = some [.iconst 0 5,
      Morph.Clif.Instr.call 2 "add" [0, 1] Typ.intType] := rfl

/-- The encoded call satisfies the resolved-call contract. -/
example : callResolved progAdd (.call (some 2) "add" [0, 1]) :=
  ⟨addMIR, rfl, rfl, Morph.Clif.ClifTy.i64, rfl⟩

/-! ## Typed-runner and stepping pins (D-7 option B, slice B1) -/

/-- The typed `add` callable. -/
def addTCF : TCFunc :=
  ⟨"add", [(0, Typ.intType), (1, Typ.intType)], ⟨[.iadd 2 0 1], 2⟩⟩

/-- A one-callable typed program. -/
def tprogAdd : TCProgram := [addTCF]

/-- The typed simulation certifies the typed run: the same argument
values drive a MIR `Trace` over the encoded body to the value
`runTCallee` returns. The typed bind is proved by rewriting with the
two (decided) `typMatches` facts — kernel `rfl` cannot cross `Typ`'s
derived `BEq`, so the bind hypothesis is discharged by `simp` with
the checks as rewrite rules. -/
example : runTCallee addTCF [.int 5, .int 7] = some (.int 12) := by
  have e1 : typMatches (.int 5) Typ.intType = true := by native_decide
  have e2 : typMatches (.int 7) Typ.intType = true := by native_decide
  have ht : bindTArgs [(0, Typ.intType), (1, Typ.intType)] [.int 5, .int 7]
      = some (Morph.Clif.Env.set
        (Morph.Clif.Env.set (fun _ => none) 1 (.int 7)) 0 (.int 5)) := by
    simp [bindTArgs, e1, e2]
  exact tcallee_correct (ps := [(0, Typ.intType), (1, Typ.intType)])
    (ts := [(0, Typ.intType), (1, Typ.intType)])
    (is := [Morph.MIR.Instr.binop 2 .add 0 1 Typ.intType])
    rfl rfl ht rfl rfl
    (Trace.cons (Step.add (by rfl) (by rfl) ⟨by decide, by decide⟩)
      (Trace.nil _))
    rfl (by rfl)

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

/-- The emitter still refuses call-bearing bodies under the default
(empty) program. -/
example : Morph.Codegen.emitBlock
    ⟨0, [.const 0 .unit, .call (some 2) "add" [0, 1]], .return_ 2⟩ = none :=
  rfl

/-! ## Preamble and program-aware emission pins (D-7 option B, slice B2) -/

/-- A signature declaration tokenises and parses back. -/
example : parseSig (toksSig "add" [Typ.intType, Typ.intType] Typ.intType)
    = some ((("add", [Typ.intType, Typ.intType], Typ.intType)), []) := by
  simpa using parseSig_toksSig "add" [Typ.intType, Typ.intType] Typ.intType []

/-- A whole preamble round-trips. -/
example : parseSigs 1 (((("add", [Typ.intType, Typ.intType], Typ.intType) :: [] ).map
    fun s => toksSig s.1 s.2.1 s.2.2).flatten)
    = some ([(("add", [Typ.intType, Typ.intType], Typ.intType))], []) := by
  simpa using parseSigs_toksSigs [(("add", [Typ.intType, Typ.intType], Typ.intType))] []

/-- The `add` signature declares its ABI slots. -/
example : Morph.Codegen.sigDecl addMIR
    = some "function %add(i64, i64) -> i64\n" := rfl

/-- Empty programs declare nothing, so default emission is byte-identical. -/
example : Morph.Codegen.preamble ⟨[]⟩ = "" := rfl

/-- The test program's preamble. -/
example : Morph.Codegen.preamble progAdd
    = "function %add(i64, i64) -> i64\n" := rfl

/-- With a program, the emitter admits the int-world call. -/
example : Morph.Codegen.emitBlock
    ⟨0, [.const 0 .unit, .call (some 2) "add" [0, 1]], .return_ 2⟩ progAdd
    = some ⟨[Morph.Clif.Instr.call 2 "add" [0, 1] Typ.intType], 2⟩ := rfl

/-- ...and the artifact carries the preamble ahead of the body. -/
example : Morph.Codegen.emitClif
    ⟨"main", [], [⟨0, [.const 0 .unit, .call (some 2) "add" [0, 1]], .return_ 2⟩],
      0, Typ.intType⟩ progAdd
    = some ("function %add(i64, i64) -> i64\n" ++
      "function %main() -> i64 {\nblock0:\n  v2 = call %add(v0, v1) -> i64\n  return v2\n}\n") := rfl

/-! ## Bool-call acceptance pins (D-7 option B, slice C1)

The memo's test for the decision: the first bool-returning call must
encode, run, and agree. `iseq` compares two ints; its declaration
names the `.i8` slot, the typed run returns the comparison, and the
agreement proof ties the run to a `Trace` exactly as the int case
does — with `Step.eq`, which carries no range fact. -/

/-- A bool signature declaration tokenises and parses back. -/
example : parseSig (toksSig "iseq" [Typ.intType, Typ.intType] Typ.boolType)
    = some ((("iseq", [Typ.intType, Typ.intType], Typ.boolType)), []) := by
  simpa using parseSig_toksSig "iseq" [Typ.intType, Typ.intType] Typ.boolType []

/-- The `iseq` signature declares the `.i8` slot. -/
def isEqMIR : Morph.MIR.Func :=
  ⟨"iseq", [(0, Typ.intType), (1, Typ.intType)],
    [⟨0, [.const 0 .unit, .binop 2 .eq 0 1 .boolType], .return_ 2⟩],
    0, Typ.boolType⟩

example : Morph.Codegen.sigDecl isEqMIR
    = some "function %iseq(i64, i64) -> i8\n" := rfl

/-- The typed `iseq` callable. -/
def isEqTC : TCFunc :=
  ⟨"iseq", [(0, Typ.intType), (1, Typ.intType)],
    ⟨[.icmp 2 .eq 0 1], 2⟩⟩

/-- A bool call runs. -/
example : (runTCall [isEqTC] "iseq" [.int 1, .int 1]).map
    (fun w => w == .bool true)
    = some true := by
  native_decide

/-- ...to the comparison value, certified against a `Trace`. -/
example : runTCallee isEqTC [.int 1, .int 1] = some (.bool true) := by
  have e1 : typMatches (.int 1) Typ.intType = true := by native_decide
  have ht : bindTArgs [(0, Typ.intType), (1, Typ.intType)] [.int 1, .int 1]
      = some (Morph.Clif.Env.set
        (Morph.Clif.Env.set (fun _ => none) 1 (.int 1)) 0 (.int 1)) := by
    simp [bindTArgs, e1]
  exact tcallee_correct (ps := [(0, Typ.intType), (1, Typ.intType)])
    (ts := [(0, Typ.intType), (1, Typ.intType)])
    (is := [Morph.MIR.Instr.binop 2 .eq 0 1 Typ.boolType])
    rfl rfl ht rfl rfl
    (Trace.cons (Step.eq (by rfl) (by rfl))
      (Trace.nil _))
    rfl (by rfl)

/-- The caller: calls `iseq`, returns an int (the artifact printer is
still `-> i64` at the top level). -/
def isEqMainMIR : Morph.MIR.Func :=
  ⟨"main", [],
    [⟨0, [.const 0 .unit, .const 0 (.int 1), .const 1 (.int 1),
      .call (some 2) "iseq" [0, 1], .const 3 (.int 0)], .return_ 3⟩],
    0, Typ.intType⟩

/-- A two-function program. -/
def progBool : Morph.MIR.Program := ⟨[isEqMainMIR, isEqMIR]⟩

/-- Its preamble declares the `.i8` result — the callee only; the entry
is defined in the module and is excluded from the declarations. -/
example : Morph.Codegen.preamble progBool
    = "function %iseq(i64, i64) -> i8\n" := rfl

/-- ...and the artifact calls into it. -/
example : Morph.Codegen.emitClif isEqMainMIR progBool
    = some ("function %iseq(i64, i64) -> i8\n" ++
      "function %main() -> i64 {\nblock0:\n  v0 = iconst.i64 1\n  v1 = iconst.i64 1\n  v2 = call %iseq(v0, v1) -> i8\n  v3 = iconst.i64 0\n  return v3\n}\n") := by
  native_decide

/-! ## Gate succession pins (D-7 option B, slice C2)

Step 3's switch, pinned both ways: a body that computes a comparison
but returns an integer now emits (the old `allI64` scan refused it),
and a boolean result emits under its computed `-> i8` header. -/

/-- Compare-then-int emits: the gate is the computed type. -/
example : Morph.Codegen.emitBlock
    ⟨0, [.const 0 .unit, .const 0 (.int 1), .const 1 (.int 1),
      .binop 2 .eq 0 1 .boolType, .const 3 (.int 7)], .return_ 3⟩
    = some ⟨[.iconst 0 1, .iconst 1 1,
      .icmp 2 .eq 0 1, .iconst 3 7], 3⟩ := rfl

/-- ...with the comparison printed in the artifact. -/
example : Morph.Codegen.emitClif
    ⟨"main", [], [⟨0, [.const 0 .unit, .const 0 (.int 1), .const 1 (.int 1),
      .binop 2 .eq 0 1 .boolType, .const 3 (.int 7)], .return_ 3⟩],
      0, Typ.intType⟩ ⟨[]⟩
    = some ("function %main() -> i64 {\nblock0:\n  v0 = iconst.i64 1\n  v1 = iconst.i64 1\n  v2 = icmp eq v0, v1\n  v3 = iconst.i64 7\n  return v3\n}\n") := by
  native_decide

/-- ...and a boolean result emits under its computed header. -/
example : Morph.Codegen.emitBlock
    ⟨0, [.const 0 .unit, .const 0 (.int 1), .const 1 (.int 1),
      .binop 2 .eq 0 1 .boolType], .return_ 2⟩
    = some ⟨[.iconst 0 1, .iconst 1 1, .icmp 2 .eq 0 1], 2⟩ := rfl

/-- The single-function boolean artifact. -/
example : Morph.Codegen.emitClif
    ⟨"iseq", [], [⟨0, [.const 0 .unit, .binop 2 .eq 0 1 .boolType],
      .return_ 2⟩], 0, Typ.boolType⟩ ⟨[]⟩
    = some ("function %iseq() -> i8 {\nblock0:\n  v2 = icmp eq v0, v1\n  return v2\n}\n") := rfl

/-! ## Named rendering pins (D-7 option C, slice D1)

The header names the function and declares its return slot, matching
the line `sigDecl` contributes to the preamble; the historic
renderer is the `main`/`intType` case (`renderFuncFor_main`). -/

/-- A named body header matches its preamble declaration. -/
example : Morph.Clif.renderFuncFor "iseq" Typ.boolType ⟨[.icmp 2 .eq 0 1], 2⟩
    = "function %iseq() -> i8 {\nblock0:\n  v2 = icmp eq v0, v1\n  return v2\n}\n" := rfl

/-- A void header takes no suffix, like the declaration. -/
example : Morph.Clif.renderFuncFor "unitfn" Typ.unitType ⟨[], 0⟩
    = "function %unitfn() {\nblock0:\n\n  return v0\n}\n" := rfl

/-! ## Program emission pins (D-7 option C, slice D2)

One preamble for the program, then every function body under its
computed header. The empty program emits the empty artifact; full
int-world and mixed int/bool programs emit end to end. -/

/-- The empty program emits the empty artifact. -/
example : Morph.Codegen.emitProg ⟨[]⟩ = some "" :=
  Morph.Codegen.emitProg_nil

/-- The full int-world callee. -/
def addMIRFull : Morph.MIR.Func :=
  ⟨"add", [(0, Typ.intType), (1, Typ.intType)],
    [⟨0, [.const 0 .unit, .binop 2 .add 0 1 .intType], .return_ 2⟩],
    0, Typ.intType⟩

/-- The full int-world entry. -/
def addMainFull : Morph.MIR.Func :=
  ⟨"main", [],
    [⟨0, [.const 0 .unit, .const 0 (.int 5), .const 1 (.int 7),
      .call (some 2) "add" [0, 1]], .return_ 2⟩],
    0, Typ.intType⟩

/-- A two-function program. -/
def progAddFull : Morph.MIR.Program := ⟨[addMainFull, addMIRFull]⟩

/-- It emits end to end: callee preamble, entry, callee. -/
example : Morph.Codegen.emitProg progAddFull
    = some ("function %add(i64, i64) -> i64\n" ++
      "function %main() -> i64 {\nblock0:\n  v0 = iconst.i64 5\n  v1 = iconst.i64 7\n  v2 = call %add(v0, v1) -> i64\n  return v2\n}\n" ++
      "function %add() -> i64 {\nblock0:\n  v2 = iadd v0, v1\n  return v2\n}\n") := by
  native_decide

/-- ...and the mixed program emits end to end: preamble, int entry,
bool callee under its computed header. -/
example : Morph.Codegen.emitProg progBool
    = some ("function %iseq(i64, i64) -> i8\n" ++
      "function %main() -> i64 {\nblock0:\n  v0 = iconst.i64 1\n  v1 = iconst.i64 1\n  v2 = call %iseq(v0, v1) -> i8\n  v3 = iconst.i64 0\n  return v3\n}\n" ++
      "function %iseq() -> i8 {\nblock0:\n  v2 = icmp eq v0, v1\n  return v2\n}\n") := by
  native_decide

end Morph.Tests.ClifCall

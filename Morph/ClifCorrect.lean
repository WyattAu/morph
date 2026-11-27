/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifSimulate
import Morph.HIRToMIRTotal

/-!
# Stage B item B4: the program-level composition

`Morph/ClifSimulate.lean` proves the CLIF half — an encodable straight-line body
whose MIR execution is certified by a `Trace` runs in `Clif.run` to the same
value. `compile_total` proves the MIR half — a straight HIR program that runs
lowers to a `MIR.Func` whose `execFunc` returns the same value.

This file puts them in one statement. The conclusion is a conjunction on purpose:
both semantics are compared *through the HIR value*, which is the only thing both
theorems know. Neither side is compared to the other directly, so a bug in one
cannot mask a bug in the other — a claim about `execFunc` and a claim about
`Clif.run` are both statements about `.int n`, and `.int n` is what the HIR run
produced.

## What the trace still owes

The `Trace` hypothesis is not discharged here, and cannot be: it says the run
stays inside the fragment (integer operands, in-range results, shift amounts in
`[0,64)`). That is the fragment's obligation, stated as a certificate so it can
be checked against a program rather than assumed at a program. Nothing in this
file proves any particular program satisfies it.

## The prologue

`lowerProgram` prefixes the body with `.const 0 .unit`, and `Clif.run` starts from
an empty register file. The encoder cannot emit that instruction (CLIF has no unit
value), so the emitted function is the encoding of the body *after* the prologue;
`Trace` therefore starts at `update (fun _ => none) 0 .unit`. Register 0 is then
the only difference between the two register files, and `.unit` is a value no
`Step` reads, so `trace_transport` bridges them. The prologue is dropped from the
emitted function, not mistranslated.
-/

open Morph.Core
open Morph.HIR Morph.HIRToMIR Morph.HIRToMIRCorrect
open Morph.MIR Morph.Frontend.HIREval Morph.Frontend.HIRInterp

namespace Morph.ClifCorrect

/-- The MIR execution the trace certifies, in the store-aware semantics and
including the prologue: exactly the `execInstrsFull` call that `compile_total`'s
statement layer refers to. -/
theorem trace_execInstrsFull_prologue {instrs : List Morph.MIR.Instr}
    {m' : Morph.MIR.Env} {store : Morph.Store}
    (htr : Morph.Clif.Trace instrs (Morph.MIR.Env.update (fun _ => none) 0 .unit) m') :
    Morph.MIR.execInstrsFull ⟨fun _ => none, store⟩ ([.const 0 .unit] ++ instrs)
      = some ⟨m', store⟩ :=
  execInstrsFull_prologue store instrs ⟨m', store⟩
    (Morph.Clif.trace_execInstrsFull htr store)

/-- **Stage B end-to-end.** When `lowerProgram` accepts a straight HIR program,
the program's HIR run returns `.int n`, the lowered body's MIR execution is
certified by a `Trace`, and that body is encoded into `cf`, then both the MIR
function and the CLIF function return `.int n`.

The MIR conjunct is `compile_total`; the CLIF conjunct is `clif_correct`. Both
are stated against the *same* `n`, which is what makes this a composition and
not two independent claims. -/
theorem clif_correct_program {prog : HIR.Program} {instrs : List Morph.MIR.Instr}
    {v : ValId} {cf : Morph.Clif.Func} {store : Morph.Store} {fuelH : Nat}
    {henv' : HEnv} {out : HFlow} {m' : Morph.MIR.Env} {n : Int}
    (h : lowerProgram prog =
      some ⟨"main", [], [⟨0, [.const 0 .unit] ++ instrs, .return_ v⟩], 0, .unitType⟩)
    (hss : StraightStmts 256 prog.stmts)
    (hrun : runHIRStmts fuelH [] prog.stmts (.value (.lit .unit)) = (out, henv'))
    (hval : runValue? out = some (.lit (.int n)))
    (henc : Morph.Clif.blockEncode ⟨0, instrs, .return_ v⟩ [] = some cf)
    (htr : Morph.Clif.Trace instrs (Morph.MIR.Env.update (fun _ => none) 0 .unit) m')
    (hret : m' v = some (.int n)) :
    execFunc 2
        ⟨"main", [], [⟨0, [.const 0 .unit] ++ instrs, .return_ v⟩], 0, .unitType⟩
        ⟨fun _ => none, store⟩ = some (.int n) ∧
      Morph.Clif.run cf = some (.int n) :=
  ⟨compile_total prog _ store h hss fuelH henv' out (.int n) hrun hval,
   Morph.Clif.clif_correct henc htr hret⟩

end Morph.ClifCorrect

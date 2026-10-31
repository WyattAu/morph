/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.Parser
import Morph.Executable
import Morph.Interp
import Morph.Frontend.HIRLower
import Morph.Frontend.HIRInterp
import Morph.Frontend.DocComment
import Morph.TypeChecker
import Morph.Specs.MorphLanguage.Spec

/-!
# The Morph driver

The first end-to-end implementation on top of the verified pipeline: source
text in, evaluated result out, with every stage a component the specification
modules already prove total.

- `Morph.Frontend.parse` — the total, fuel-bounded parser (loops 9 and 39);
- `Morph.Executable.run` — the total, fuel-seeded evaluator (loop 38).

`runSource` is therefore total by construction: it cannot crash, diverge, or
throw. A parse failure or a stuck evaluation is a *value* (`Outcome`), never an
exception — the driver's only failure mode is the process exit code chosen by
the CLI in `Main.lean`.

`Main.lean` (the `morph` executable) is a thin IO shell over this module; all
logic is here so the tests can exercise the pipeline without touching IO.
-/

namespace Morph.Driver

open Morph.Core Morph.Syntax

/-- Render a computed value the way the CLI prints it. -/
def renderValue : Value → String
  | .int n => toString n
  | .bool b => toString b
  | .string s => s
  | .float f => toString f
  | .unit => "()"
  | .undef => "undef"
  | .none => "none"
  | .some v => s!"some ({renderValue v})"
  | .ok v => s!"ok ({renderValue v})"
  | .err v => s!"err ({renderValue v})"
  | .tuple_ vs => s!"({String.intercalate ", " (vs.map renderValue)})"
  | .array_ vs => s!"[{String.intercalate ", " (vs.map renderValue)}]"
  | .loc n => s!"loc {n}"
  | .pointer p => reprStr p
  | .closure f l => s!"<closure {f}@{l}>"

/-- What one pipeline run produced. Every outcome is a value; nothing throws. -/
inductive Outcome where
  | value : String → Outcome
  | parseFailed : String → Outcome
  | stuck : Outcome
  | typeError : String → Outcome
  | unsupported : String → Outcome
  deriving Repr, BEq

def isValue : Outcome → Bool | .value _ => true | _ => false
def isParseFailed : Outcome → Bool | .parseFailed _ => true | _ => false
def isStuck : Outcome → Bool | .stuck => true | _ => false
def isTypeError : Outcome → Bool | .typeError _ => true | _ => false
def isUnsupported : Outcome → Bool | .unsupported _ => true | _ => false

/-- Render parse errors as `line l, col c: message` lines. -/
def renderErrors (errs : List Morph.Frontend.ParseError) : String :=
  String.intercalate "\n"
    (errs.map fun e => s!"line {e.line}, col {e.col}: {e.message}")

/-- **The pipeline**: parse, then evaluate, then render.
Total by construction — both stages are proved-total components. -/
def runSource (src : String) : Outcome :=
  match Morph.Frontend.parse src with
  | .ok e =>
      match Executable.run e with
      | some (.lit v) => .value (renderValue v)
      | some e' => .value (reprStr e')
      | none => .stuck
  | .error errs => .parseFailed (renderErrors errs)

/-- Parse only; the AST in `repr` form. For `morph parse`. -/
def parseSource (src : String) : Outcome :=
  match Morph.Frontend.parse src with
  | .ok e => .value (reprStr e)
  | .error errs => .parseFailed (renderErrors errs)

/-- **The typecheck pipeline** (loop 82): parse, then synthesize a type.
A success reports the inferred type; a failure reports the checker's
message (`formatTypeError`). The dummy `.unitType` expectation never
surfaces: without an annotation, only the cannot-infer branch (which
ignores it) is reachable. For `morph check`. -/
def checkSource (src : String) : Outcome :=
  match Morph.Frontend.parse src with
  | .ok e =>
    match Morph.TypeChecker.synthType [] [] e with
    | some τ => .value (reprStr τ)
    | none => .typeError (Morph.TypeChecker.formatTypeError [] [] e .unitType)
  | .error errs => .parseFailed (renderErrors errs)

/-- **The statement pipeline** (loop 74): parse a statement sequence, run it.
The sequence's value is its last expression statement; `return` short-circuits.
Total by construction, like `runSource`. -/
def runProgram (src : String) : Outcome :=
  match Morph.Frontend.parseProgram src with
  | .ok prog =>
      match Morph.Interp.runProgram prog with
      | .value (.lit v) => .value (renderValue v)
      | .value e => .value (reprStr e)
      | .returned (.lit v) => .value (renderValue v)
      | .returned e => .value (reprStr e)
      | _ => .stuck
  | .error errs => .parseFailed (renderErrors errs)

/-- **The HIR statement pipeline** (loop 87): parse, lower to the HIR
fragment, run the HIR statement interpreter. Programs that leave the
fragment report `unsupported` rather than running. For `morph run --hir`. -/
def runProgramHIR (src : String) : Outcome :=
  match Morph.Frontend.parseProgram src with
  | .ok prog =>
      match Morph.Frontend.HIRLower.toHIRProgram prog with
      | some hprog =>
          match Morph.Frontend.HIRInterp.runHIRProgram hprog with
          | .value (.lit v) => .value (renderValue v)
          | .value e => .value (reprStr e)
          | .returned (.lit v) => .value (renderValue v)
          | .returned e => .value (reprStr e)
          | _ => .stuck
      | none => .unsupported
          "program leaves the HIR fragment (--hir runs first-order let/match/while programs only)"
  | .error errs => .parseFailed (renderErrors errs)

def usage : String :=
  "usage: morph <command> [argument]\n" ++
  "  eval <expr>   parse and evaluate an expression\n" ++
  "  parse <expr>  print the parsed AST\n" ++
  "  check <expr>  print the inferred type or the type error\n" ++
  "  run <file>    run the statement program in a file\n" ++
  "  run --hir <file>  run the file through the HIR lowering\n" ++
  "  fmt <file>    format the statement program in a file\n" ++
  "  doc <file>    render the file's /// docs as Markdown\n" ++
  "  version       print the Morph version\n"

/-- **The formatter** (loop 90): parse a statement program, print the
canonical `hum` rendering. Fails exactly when the program fails to parse,
with the same report `run` would print. -/
def formatProgram (src : String) : Outcome :=
  match Morph.Frontend.parseProgram src with
  | .ok prog => .value (Morph.Specs.MorphLanguage.renderCode prog .hum)
  | .error errs => .parseFailed (renderErrors errs)

/-- **The doc renderer** (loop 90): extract the file's `///` entries
(`Morph.Frontend.DocComment`) and render them as Markdown. Pure text
processing — it never fails, even on unparseable files. -/
def docSource (src : String) : Outcome :=
  .value (Morph.Frontend.DocComment.renderMarkdown
    (Morph.Frontend.DocComment.extract src))

/-- The text the CLI prints for an outcome (the exit code is `Main.lean`'s
decision: values exit 0, everything else exits 1). -/
def report (out : Outcome) : String :=
  match out with
  | .value s => s
  | .parseFailed s => s
  | .stuck => "stuck: evaluation got stuck or exhausted its fuel"
  | .typeError s => s
  | .unsupported s => s

end Morph.Driver

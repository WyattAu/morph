/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.HIRLower
import Morph.Frontend.Parser
import Morph.Driver

/-!
# HIR lowering tests (loop 82)

Executable counterpart of the lowering contract
(`Morph.Frontend.HIRLower`): supported shapes lower structurally,
rejected shapes lower to `none`, and real parser output lowers when it
stays inside the fragment (`1 + 2`) but not when it leaves it
(`for` loops).
-/

namespace Morph.Tests.HIRLower

open Morph.Frontend.HIRLower
open Morph.Syntax

/-- Top-level slots live in the `"ctx"` namespace (loop 84): a bare
`⟨n, "bv"⟩` would collide with the binder a `let` at depth `n`
introduces. -/
example : toHIR (.bvar 2) = some (.var ⟨2, "ctx"⟩) := by rfl

/-- Addition lowers structurally. -/
example : toHIR (.binop .add (.lit (.int 1)) (.lit (.int 2))) =
    some (.binop .add (.lit (.int 1)) (.lit (.int 2))) := by rfl

/-- A variable call lowers to call-by-`Id`. -/
example : toHIR (.app (.fvar "f") [.lit (.int 1)]) =
    some (.app ⟨0, "free:f"⟩ [.lit (.int 1)]) := by rfl

/-- `let` binds slot 0 under the `"bv"` name, matching body occurrences. -/
example : toHIR (.let_ (.lit (.int 1)) (.bvar 0)) =
    some (.let ⟨0, "bv"⟩ (.lit (.int 1)) (.var ⟨0, "bv"⟩)) := by rfl

/-- Tuples are rejected. -/
example : toHIR (.tuple_ [.lit (.int 1)]) = none := by rfl

/-- Ascriptions erase to their subject (loop 85). -/
example : toHIR (.typeAsc (.lit (.int 1)) .intType) =
    some (.lit (.int 1)) := by rfl

/-- Field projection erases to its receiver (loop 85). -/
example : toHIR (.field_ (.lit (.int 1)) "x") =
    some (.lit (.int 1)) := by rfl

/-- A variable pipeline lowers to application (loop 85). -/
example : toHIR (.pipe (.lit (.int 1)) (.fvar "f")) =
    some (.app ⟨0, "free:f"⟩ [.lit (.int 1)]) := by rfl

/-- A non-variable pipeline target is rejected (loop 85). -/
example : toHIR (.pipe (.lit (.int 1)) (.lit (.int 2))) = none := by rfl

/-- Expression `match_` over a literal pattern lowers structurally (loop 86). -/
example : toHIR (.match_ (.lit (.int 1)) [(.lit_ (.int 1), .lit (.int 7))]) =
    some (.match (.lit (.int 1)) [(.lit (.int 1), .lit (.int 7))]) := by rfl

/-- Expression `match_` over a variable pattern binds depth 0 (loop 86). -/
example : toHIR (.match_ (.lit (.int 1)) [(.var_ "x", .bvar 0)]) =
    some (.match (.lit (.int 1)) [(.var ⟨0, "bv"⟩, .var ⟨0, "bv"⟩)]) := by rfl

/-- `for` loops are rejected (anonymous, unreachable iterator). -/
example : toHIR (.forLoop (.lit (.int 0)) (.lit (.int 3)) [.lit (.int 42)]) =
    none := by rfl

/-! ## Rejection goldens (Sprint 5)

Every `none` arm of `toHIR`/`toHIRStmt`/`toHIRProgram` below is pinned, so
growing the fragment must update a golden deliberately. -/

/-- `??` is rejected (no HIR counterpart). -/
example : toHIR (.nullCoalesce (.lit (.int 1)) (.lit (.int 2))) = none := by
  rfl

/-- `some_` is rejected (option constructors stop at the fragment edge). -/
example : toHIR (.some_ (.lit (.int 1))) = none := by rfl

/-- `ok_` is rejected, like the other result/option constructors. -/
example : toHIR (.ok_ (.lit (.int 1))) = none := by rfl

/-- Applying a non-variable function is rejected (call-by-`Id` only). -/
example : toHIR (.app (.lit (.int 1)) [.lit (.int 2)]) = none := by rfl

/-- Array literals are rejected. -/
example : toHIR (.arrayLit [.lit (.int 1)]) = none := by rfl

/-- `some_` patterns are rejected. -/
example : toHIRPat (.some_ (.var_ "x")) = none := by rfl

/-- `matchStmt` with no arms lowers (empty match is unit). -/
example : toHIRStmt (.matchStmt (.lit (.int 1)) []) =
    some (.matchStmt (.lit (.int 1)) []) := by rfl

/-- A program with an `if` statement stays in the fragment (loop 112). -/
example : toHIRProgram ⟨[.ifStmt (.lit (.bool true)) [.nop] [.nop]]⟩ =
    some ⟨[.ifStmt (.lit (.bool true)) [.nop] [.nop]]⟩ := by rfl

/-- End-to-end: `1 + 2` parses and lowers. -/
example : (match Morph.Frontend.parse "1 + 2" with
  | .ok e => toHIR e
  | .error _ => none).isSome = true := by
  native_decide

/-- End-to-end: a `for` program parses but leaves the HIR fragment. -/
example : (match Morph.Frontend.parse "for 0 in 3 { 42 }" with
  | .ok e => toHIR e
  | .error _ => some (.lit (.int 0))).isSome = false := by
  native_decide

/-- End-to-end: a pipeline parses and lowers (loop 85). -/
example : (match Morph.Frontend.parse "1 |> f" with
  | .ok e => toHIR e
  | .error _ => none).isSome = true := by
  native_decide

/-! ## Statements and programs (loop 83) -/

/-- `break` lowers to itself. -/
example : toHIRStmt .break = some .break := by rfl

/-- Declarations join the `free:` namespace, matching expression-side uses. -/
example : toHIRStmt (.varDecl ⟨"y"⟩ .unitType (.lit (.int 5))) =
    some (.varDecl ⟨0, "free:y"⟩ .unitType (.lit (.int 5))) := by rfl

/-- `doWhile` is rejected (at-least-once has no HIR counterpart). -/
example : toHIRStmt (.doWhile (.lit (.bool true)) []) = none := by rfl

/-- `ifStmt` lowers 1:1 (loop 112: HIR grew the statement conditional). -/
example : toHIRStmt (.ifStmt (.lit (.bool true)) [] []) =
    some (.ifStmt (.lit (.bool true)) [] []) := by rfl

/-- `whileLoop` with a true guard lowers (the supported loop). -/
example : toHIRStmt (.whileLoop (.lit (.bool true)) [.nop]) =
    some (.whileLoop (.lit (.bool true)) [.nop]) := by rfl

/-- End-to-end: `let y = 5; y` parses and lowers as a program. -/
example : (match Morph.Frontend.parseProgram "let y = 5; y" with
  | .ok p => toHIRProgram p
  | .error _ => none).isSome = true := by
  native_decide

/-- End-to-end: a `match` statement parses but leaves the HIR fragment. -/
example : (match Morph.Frontend.parseProgram
    "let y = 0; match none { case none => { y = 1; } }" with
  | .ok p => toHIRProgram p
  | .error _ => some ⟨[]⟩).isSome = false := by
  native_decide

/-! ## The HIR statement pipeline (loop 87) -/

open Morph.Driver

/-- End-to-end: declarations and reads run through HIR. -/
example : runProgramHIR "let x = 5; x * x" == .value "25" := by native_decide

/-- End-to-end: assignment updates the innermost binding through HIR. -/
example : runProgramHIR "let x = 1; x = x + 10; x" == .value "11" := by
  native_decide

/-- End-to-end: a counting loop runs through HIR. -/
example : runProgramHIR
    "let a = 0; let i = 0; while (i < 5) { let a = a + i; let i = i + 1; }; a" ==
    .value "10" := by native_decide

/-- End-to-end: `return` short-circuits a HIR loop. -/
example : runProgramHIR "while (true) { return 7; }" == .value "7" := by
  native_decide

/-- End-to-end: `if` statements run through HIR (loop 112). -/
example : runProgramHIR "if (true) { 1; } else { 2; }" == .value "1" := by
  native_decide

/-- End-to-end: `match` statements with var patterns run through HIR. -/
example : runProgramHIR "let y = 0; match 1 { case x => { y = x; } } y" ==
    .value "1" := by native_decide

end Morph.Tests.HIRLower

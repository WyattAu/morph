/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.HIRLower
import Morph.Frontend.Parser

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

/-- Variables keep their slot index under the `"bv"` name. -/
example : toHIR (.bvar 2) = some (.var ⟨2, "bv"⟩) := by rfl

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

/-- `for` loops are rejected (anonymous, unreachable iterator). -/
example : toHIR (.forLoop (.lit (.int 0)) (.lit (.int 3)) [.lit (.int 42)]) =
    none := by rfl

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

/-! ## Statements and programs (loop 83) -/

/-- `break` lowers to itself. -/
example : toHIRStmt .break = some .break := by rfl

/-- Declarations keep the name at index 0. -/
example : toHIRStmt (.varDecl ⟨"y"⟩ .unitType (.lit (.int 5))) =
    some (.varDecl ⟨0, "y"⟩ .unitType (.lit (.int 5))) := by rfl

/-- `doWhile` is rejected (at-least-once has no HIR counterpart). -/
example : toHIRStmt (.doWhile (.lit (.bool true)) []) = none := by rfl

/-- `ifStmt` is rejected (HIR statements have no conditional). -/
example : toHIRStmt (.ifStmt (.lit (.bool true)) [] []) = none := by rfl

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

end Morph.Tests.HIRLower

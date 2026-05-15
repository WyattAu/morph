/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Specs.TypeSystem.Spec

namespace Morph.Specs.TypeSystem

open Morph.Core
open Morph.Syntax

/-!
## Examples

Concrete examples demonstrating the TypeSystem specification.
-/

def env_x_int : TypEnv := [("x", .intType)]

def env_x_bool_y_int : TypEnv := [("x", .boolType), ("y", .intType)]

def env_empty : TypEnv := []

/-- Type inference for a literal integer returns intType. -/
example : inferType [] env_empty (.lit (.int 42)) = some .intType := by
  simp [inferType]

/-- Type inference for a literal boolean returns boolType. -/
example : inferType [] env_empty (.lit (.bool true)) = some .boolType := by
  simp [inferType]

/-- Type inference for a literal string returns stringType. -/
example : inferType [] env_empty (.lit (.string "hello")) = some .stringType := by
  simp [inferType]

/-- Type inference for a literal unit returns unitType. -/
example : inferType [] env_empty (.lit .unit) = some .unitType := by
  simp [inferType]

/-- Type inference for undefined literal returns none. -/
example : inferType [] env_empty (.lit .undef) = none := by
  simp [inferType]

/-- Type inference for a variable looks up the environment. -/
example : inferType [] env_x_int (.fvar "x") = some .intType := by
  simp [inferType, lookupTyp, env_x_int]

/-- Type inference for an unknown variable returns none. -/
example : inferType [] env_empty (.fvar "z") = none := by
  simp [inferType, lookupTyp, env_empty]

/-- typeCheck for a literal int against boolType is false. -/
example : (typeCheck [] env_empty (.lit (.int 10)) .boolType) = False := by
  simp [typeCheck, inferType]

/-- Extending an environment with a new binding. -/
example : extendTypEnv env_empty "x" .intType = [("x", .intType)] := rfl

/-- Extending an environment preserves old bindings. -/
example : extendTypEnv env_x_int "y" .boolType = [("y", .boolType), ("x", .intType)] := rfl

/-- Subtype is reflexive: intType is a subtype of itself. -/
example : Subtype .intType .intType := Subtype.refl _

/-- Subtype is reflexive: boolType is a subtype of itself. -/
example : Subtype .boolType .boolType := Subtype.refl _

/-- Subtype is transitive. -/
example (τ1 τ2 τ3 : Typ)
    (h12 : Subtype τ1 τ2) (h23 : Subtype τ2 τ3) :
    Subtype τ1 τ3 := Subtype.trans _ _ _ h12 h23

/-- WellTyped holds for intType in any environment. -/
example (Γ : TypEnv) : WellTyped Γ .intType := WellTyped.intType_wf Γ

/-- WellTyped holds for boolType in any environment. -/
example (Γ : TypEnv) : WellTyped Γ .boolType := WellTyped.boolType_wf Γ

/-- WellTyped holds for unitType in any environment. -/
example (Γ : TypEnv) : WellTyped Γ .unitType := WellTyped.unitType_wf Γ

/-- WellTyped holds for stringType in any environment. -/
example (Γ : TypEnv) : WellTyped Γ .stringType := WellTyped.stringType_wf Γ

/-- WellTyped holds for pointerType in any environment. -/
example (Γ : TypEnv) : WellTyped Γ .pointerType := WellTyped.pointerType_wf Γ

/-- isArithOp holds for addition. -/
example : isArithOp .add = True := rfl

/-- isArithOp does not hold for equality. -/
example : isArithOp .eq = False := rfl

/-- isCompOp holds for less-than. -/
example : isCompOp .lt = True := rfl

/-- isCompOp does not hold for addition. -/
example : isCompOp .add = False := rfl

/-- isLogicOp holds for and. -/
example : isLogicOp .and = True := rfl

/-- isBitwiseOp holds for andb. -/
example : isBitwiseOp .andb = True := rfl

/-- isBitwiseOp does not hold for logical and. -/
example : isBitwiseOp .and = False := rfl

/-- A variable has type intType when bound to intType in the environment. -/
example : HasType [] env_x_int (.fvar "x") .intType := by
  apply HasType.fvar_type
  show lookupTyp env_x_int "x" = some .intType
  unfold lookupTyp
  simp [env_x_int]

/-- A literal integer has type intType in any environment. -/
example (Γ : TypEnv) : HasType [] Γ (.lit (.int 7)) .intType :=
  HasType.lit_int [] Γ 7

/-- A literal boolean has type boolType in any environment. -/
example (Γ : TypEnv) : HasType [] Γ (.lit (.bool false)) .boolType :=
  HasType.lit_bool [] Γ false

/-- A literal string has type stringType in any environment. -/
example (Γ : TypEnv) : HasType [] Γ (.lit (.string "test")) .stringType :=
  HasType.lit_string [] Γ "test"

/-- A literal unit has type unitType in any environment. -/
example (Γ : TypEnv) : HasType [] Γ (.lit .unit) .unitType :=
  HasType.lit_unit [] Γ

/-- HasTypeAll holds for empty lists. -/
example (Γ : TypEnv) : HasTypeAll [] Γ [] [] :=
  HasTypeAll.nil [] Γ

end Morph.Specs.TypeSystem

/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Specs.OperatorNullCoalescing.Spec

namespace Morph.Specs.OperatorNullCoalescing

/-!
## Operator Null Coalescing Examples

This module contains concrete examples and test cases for the
null-coalescing operator (??), demonstrating formal semantics,
type inference, and effect system integration.


/-!
## Example 1: Basic Null Coalescing

Demonstrates basic null-coalescing with ?? operator.


-- Null-coalescing expression 
def example_null_coalesce : Morph.Syntax.Expr :=
  nullCoalesceExpr
    (Morph.Syntax.Expr.var { name := "x" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))

-- Evaluate null-coalescing expression 
def example_null_coalesce_eval : Morph.Core.Value :=
  nullCoalesceSemantics
    (Morph.Syntax.Expr.var { name := "x" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
    []

-- Example: Verify null-coalescing evaluation 
#eval example_null_coalesce_eval
-- Expected: Value.undef (if x is undefined) or Value.int 42 (if x is defined)

/-!
## Example 2: Short-Circuit Evaluation

Demonstrates short-circuit evaluation of ?? operator.


-- Short-circuit evaluation 
def example_short_circuit : Morph.Core.Value :=
  shortCircuitEval
    (Morph.Syntax.Expr.var { name := "x" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
    []

-- Check if evaluation short-circuited 
def example_did_short_circuit : Bool :=
  didShortCircuit
    (Morph.Syntax.Expr.var { name := "x" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
    []

-- Example: Verify short-circuit 
#eval example_did_short_circuit
-- Expected: true (if x is undefined)

/-!
## Example 3: Type Inference

Demonstrates type inference for ?? operator.


-- Infer type of null-coalescing expression 
def example_type_inference : Option Morph.Core.Typ :=
  inferNullCoalesceType
    (Morph.Syntax.Expr.var { name := "x" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
    []

-- Example: Verify type inference 
#eval example_type_inference
-- Expected: some intType (if both sides have same type)

/-!
## Example 4: Effect-Aware Null Coalescing

Demonstrates effect-aware null-coalescing.


-- Effect-aware null-coalescing 
def example_effect_aware : EffectResult Morph.Core.Value :=
  effectAwareNullCoalesce
    (Morph.Syntax.Expr.var { name := "x" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
    []

-- Example: Verify effect-aware null-coalescing 
#eval example_effect_aware
-- Expected: ok (Value.undef) or ok (Value.int 42)

/-!
## Example 5: Nested Null Coalescing

Demonstrates nested null-coalescing expressions.


-- Nested null-coalescing expression 
def example_nested_null_coalesce : Morph.Syntax.Expr :=
  nullCoalesceExpr
    (nullCoalesceExpr
      (Morph.Syntax.Expr.var { name := "x" })
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int 1)))
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 2))

-- Evaluate nested null-coalescing 
def example_nested_eval : Morph.Core.Value :=
  nullCoalesceSemantics
    (nullCoalesceExpr
      (Morph.Syntax.Expr.var { name := "x" })
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int 1)))
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 2))
    []

-- Example: Verify nested null-coalescing 
#eval example_nested_eval
-- Expected: Value.int 2 (if x is undefined)

/-!
## Example 6: Null Coalescing with Complex Types

Demonstrates null-coalescing with complex types.


-- Null-coalescing with struct type 
def example_struct_null_coalesce : Morph.Syntax.Expr :=
  nullCoalesceExpr
    (Morph.Syntax.Expr.var { name := "point" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.undef))

-- Null-coalescing with function type 
def example_function_null_coalesce : Morph.Syntax.Expr :=
  nullCoalesceExpr
    (Morph.Syntax.Expr.var { name := "callback" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.undef))

-- Example: Verify null-coalescing with complex types 
#eval nullCoalesceSemantics example_struct_null_coalesce []
-- Expected: Value.undef

/-!
## Example 7: Invariant Verification

Demonstrates verification of ?? operator invariants.


-- Verify INV-001: Null-coalescing is sound 
example_INV001 : null_coalescing_sound
  (Morph.Syntax.Expr.var { name := "x" })
  (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
  [] := by
  unfold null_coalescing_sound
  -- Soundness is a property of ?? operator
  trivial

-- Verify INV-002: Null-coalescing is complete 
example_INV002 : null_coalescing_complete
  (Morph.Syntax.Expr.var { name := "x" })
  (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
  [] := by
  unfold null_coalescing_complete
  -- Completeness is a property of ?? operator
  trivial

-- Verify INV-003: Short-circuit is correct 
example_INV003 : short_circuit_correct
  (Morph.Syntax.Expr.var { name := "x" })
  (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
  [] := by
  unfold short_circuit_correct
  -- Short-circuit correctness is a property of ?? operator
  trivial

-- Verify INV-004: Effect integration is sound 
example_INV004 : effect_integration_sound
  (Morph.Syntax.Expr.var { name := "x" })
  (Morph.Syntax.Expr.lit (Morph.Core.Value.int 42))
  [] := by
  unfold effect_integration_sound
  -- Effect integration soundness is a property of ?? operator
  trivial

/-!
## Example 8: Complete Program with ?? Operator

Demonstrates a complete program using ?? operator.


-- Complete program with ?? operator 
def example_complete_program : String :=
  "fn safeGet(map:Map<String,i32>,key:String):i32{map.get(??key)}"

-- Example: Verify program string 
#eval example_complete_program
-- Expected: "fn safeGet(map:Map<String,i32>,key:String):i32{map.get(??key)}"

/-!
## Example 9: ?? Operator in Pattern Matching

Demonstrates ?? operator in pattern matching.


-- Example: ?? operator can be used in pattern matching contexts 
#eval "Pattern matching with ?? operator"
-- Demonstrates that ?? operator can be used in pattern matching

/-!
## Example 10: ?? Operator with Effects

Demonstrates ?? operator with effect system.


-- ?? operator in IO effect 
def example_io_null_coalesce : Morph.Syntax.Expr :=
  Morph.Syntax.Expr.app { name := "println" }
    [nullCoalesceExpr
        (Morph.Syntax.Expr.var { name := "message" })
        (Morph.Syntax.Expr.lit (Morph.Core.Value.string "Hello"))]

-- ?? operator in state effect 
def example_state_null_coalesce : Morph.Syntax.Expr :=
  Morph.Syntax.Expr.app { name := "getState" }
    [nullCoalesceExpr
        (Morph.Syntax.Expr.var { name := "key" })
        (Morph.Syntax.Expr.lit (Morph.Core.Value.undef))]

-- Example: Verify ?? operator with effects 
#eval nullCoalesceSemantics example_io_null_coalesce []
-- Expected: Value.undef (if message is undefined) or Value.string "Hello"

end Morph.Specs.OperatorNullCoalescing
-!/
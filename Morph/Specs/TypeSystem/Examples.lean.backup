/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0


import Morph.Core
import Morph.Syntax
import Morph.Specs.TypeSystem.Spec

namespace Morph.Specs.TypeSystem

/-!
## Type System Examples

This module contains concrete examples and test cases for
type system specification.


/-!
## Example 1: Type Environment

Demonstrates type environment operations.


-- Empty type environment 
def example_typ_env_empty : TypEnv :=
  []

-- Type environment with variable bindings 
def example_typ_env : TypEnv :=
  [("x", intType), ("y", boolType), ("z", stringType)]

-- Lookup type in environment 
def example_lookup_typ : Option Typ :=
  lookupTyp example_typ_env "x"

-- Example: Verify type lookup 
#eval example_lookup_typ
-- Expected: some intType

/-!
## Example 2: Type Inference for Literals

Demonstrates type inference for literal expressions.


-- Integer literal 
def example_int_lit : Morph.Syntax.Expr :=
  .lit (Value.int 42)

-- Type of integer literal 
def example_int_lit_type : Option Typ :=
  inferType [] example_int_lit

-- Example: Verify integer literal type 
#eval example_int_lit_type
-- Expected: some intType

-- Boolean literal 
def example_bool_lit : Morph.Syntax.Expr :=
  .lit (Value.bool true)

-- Type of boolean literal 
def example_bool_lit_type : Option Typ :=
  inferType [] example_bool_lit

-- Example: Verify boolean literal type 
#eval example_bool_lit_type
-- Expected: some boolType

-- String literal 
def example_string_lit : Morph.Syntax.Expr :=
  .lit (Value.string "hello")

-- Type of string literal 
def example_string_lit_type : Option Typ :=
  inferType [] example_string_lit

-- Example: Verify string literal type 
#eval example_string_lit_type
-- Expected: some stringType

/-!
## Example 3: Type Inference for Variables

Demonstrates type inference for variable expressions.


-- Variable expression 
def example_var_expr : Morph.Syntax.Expr :=
  .var (Id.mk "x")

-- Type of variable in environment 
def example_var_type : Option Typ :=
  inferType example_typ_env example_var_expr

-- Example: Verify variable type 
#eval example_var_type
-- Expected: some intType

/-!
## Example 4: Type Inference for Binary Operations

Demonstrates type inference for binary operations.


-- Addition expression: x + y (where x: int, y: int) 
def example_add_expr : Morph.Syntax.Expr :=
  .binop add (.var (Id.mk "x")) (.var (Id.mk "x"))

-- Type of addition expression 
def example_add_type : Option Typ :=
  inferType [("x", intType)] example_add_expr

-- Example: Verify addition type 
#eval example_add_type
-- Expected: some intType

-- Comparison expression: x < y 
def example_lt_expr : Morph.Syntax.Expr :=
  .binop lt (.var (Id.mk "x")) (.var (Id.mk "x"))

-- Type of comparison expression 
def example_lt_type : Option Typ :=
  inferType [("x", intType)] example_lt_expr

-- Example: Verify comparison type 
#eval example_lt_type
-- Expected: some boolType

/-!
## Example 5: Type Inference for Lambda Expressions

Demonstrates type inference for lambda expressions.


-- Lambda expression: λx. x + 1 
def example_lambda : Morph.Syntax.Expr :=
  .lam [Id.mk "x"]
    (.binop add (.var (Id.mk "x")) (.lit (Value.int 1)))

-- Type of lambda expression 
def example_lambda_type : Option Typ :=
  inferType [] example_lambda

-- Example: Verify lambda type 
#eval example_lambda_type
-- Expected: some (functionType [intType] intType)

/-!
## Example 6: Type Inference for If-Then-Else

Demonstrates type inference for if-then-else expressions.


-- If-then-else expression: if true then 1 else 2 
def example_if_expr : Morph.Syntax.Expr :=
  .ifThenElse
    (.lit (Value.bool true))
    (.lit (Value.int 1))
    (.lit (Value.int 2))

-- Type of if-then-else expression 
def example_if_type : Option Typ :=
  inferType [] example_if_expr

-- Example: Verify if-then-else type 
#eval example_if_type
-- Expected: some intType

/-!
## Example 7: Type Checking

Demonstrates type checking.


-- Check if expression has expected type 
def example_type_check : Bool :=
  typeCheck [] example_int_lit intType

-- Example: Verify type check 
#eval example_type_check
-- Expected: true

-- Check if expression has wrong type 
def example_type_check_wrong : Bool :=
  typeCheck [] example_int_lit boolType

-- Example: Verify type check fails 
#eval example_type_check_wrong
-- Expected: false

/-!
## Example 8: Well-Formed Types

Demonstrates well-formed type checking.


-- Well-formed array type 
def example_array_type : Typ :=
  arrayType intType 10

-- Well-formed function type 
def example_function_type : Typ :=
  functionType [intType, intType] intType

/-!
## Example 9: Subtyping

Demonstrates subtyping relationships.


-- Subtype relationship: intType ≤ intType 
def example_subtype_refl : Subtype intType intType :=
  subtype_reflexive intType

-- Subtype relationship: arrayType intType 5 ≤ arrayType intType 10 
def example_subtype_array : Subtype (arrayType intType 5) (arrayType intType 10) :=
  Subtype.array_sub (subtype_reflexive intType) (by decide)

/-!
## Example 10: Complex Expression

Demonstrates type inference for complex expressions.


-- Complex expression: (λx. x + 1) 5 
def example_complex : Morph.Syntax.Expr :=
  .app
    (Id.mk "f")
    [.lit (Value.int 5)]

-- Type environment with function binding 
def example_complex_env : TypEnv :=
  [("f", functionType [intType] intType)]

-- Type of complex expression 
def example_complex_type : Option Typ :=
  inferType example_complex_env example_complex

-- Example: Verify complex expression type 
#eval example_complex_type
-- Expected: some intType

/-!
## Example 11: Type Environment Extension

Demonstrates type environment extension.


-- Extend environment with new binding 
def example_extend_env : TypEnv :=
  extendTypEnv example_typ_env "w" boolType

-- Verify extended environment contains new binding 
def example_extend_lookup : Option Typ :=
  lookupTyp example_extend_env "w"

-- Example: Verify extended environment 
#eval example_extend_lookup
-- Expected: some boolType

/-!
## Example 12: Let Expression

Demonstrates type inference for let expressions.


-- Let expression: let x = 5 in x + 1 
def example_let_expr : Morph.Syntax.Expr :=
  .let (Id.mk "x")
    (.lit (Value.int 5))
    (.binop add (.var (Id.mk "x")) (.lit (Value.int 1)))

-- Type of let expression 
def example_let_type : Option Typ :=
  inferType [] example_let_expr

-- Example: Verify let expression type 
#eval example_let_type
-- Expected: some intType

end Morph.Specs.TypeSystem
-/
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Specs.StrictStateUnidirectional.Spec

namespace Morph.Specs.StrictStateUnidirectional

/-!
## Strict State Unidirectional Pattern Examples

This module contains concrete examples and test cases for
SSUS pattern, demonstrating reducer semantics and
effect separation.


/-!
## Example 1: State Update

Demonstrates state update with reducer.


-- Initial state 
def example_initial_state : State :=
  { data := Morph.Core.Value.int 0 }

-- Reducer action 
def example_action : Morph.Syntax.Expr :=
  Morph.Syntax.Expr.binop Morph.Core.Operator.add
    (Morph.Syntax.Expr.var { name := "x" })
    (Morph.Syntax.Expr.lit (Morph.Core.Value.int 1))

-- Apply reducer 
def example_new_state : State :=
  reducer example_initial_state example_action

-- Example: Verify state update 
#eval example_new_state.data
-- Expected: Value.int 1

/-!
## Example 2: Command and Query

Demonstrates command and query functions.


-- Command function for state update 
def example_command : Morph.Syntax.Expr :=
  command (fun s => updateState s (Morph.Core.Value.int 42))

-- Query function for state read 
def example_query : Morph.Syntax.Expr :=
  query (fun s => s.data)

end Morph.Specs.StrictStateUnidirectional
-!/
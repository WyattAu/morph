/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Specs.UnidirectionalDataFlow.Spec

namespace Morph.Specs.UnidirectionalDataFlow

/-!
## Unidirectional Data Flow Examples

This module contains concrete examples and test cases for
UDF (Unidirectional Data Flow) pattern.


/-!
## Example 1: Source and Sink

Demonstrates source and sink dualism.


-- Source expression 
def example_source : Morph.Syntax.Expr :=
  Morph.Syntax.Expr.lit (Morph.Core.Value.int 42)

-- Sink expression 
def example_sink : Morph.Syntax.Expr :=
  Morph.Syntax.Expr.app { name := "println" }
    [example_source]

/-!
## Example 2: Polarity Types

Demonstrates polarity types for sources and sinks.


-- Source type (polarity <) 
def example_source_type : Morph.Core.Typ :=
  Morph.Core.Typ.intType

-- Sink type (polarity >) 
def example_sink_type : Morph.Core.Typ :=
  Morph.Core.Typ.functionType [example_source_type] Morph.Core.Typ.unitType

/-!
## Example 3: Backpressure

Demonstrates backpressure in data flow.


-- Backpressure predicate (abstract) 
def backpressure : Prop :=
  -- Abstract backpressure
  True

end Morph.Specs.UnidirectionalDataFlow
-!/
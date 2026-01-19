import Morph.Core
import Morph.Syntax
import Morph.Specs.DialectProjection.Spec

namespace Morph.Specs.DialectProjection

/-!
## Dialect Projection Examples

This module contains concrete examples and test cases for the dialect
projection specification, demonstrating min/hum transformations,
projectional editing, and LSP protocol interactions.
-/

/-!
## Example 1: Simple Function Definition

Demonstrates transformation of a simple function between min and hum dialects.
-/

/-- min dialect: simple add function -/
def example_min_add : String :=
  "fn add(x:i32,y:i32):i32{x+y}"

/-- hum dialect: transformed add function -/
def example_hum_add : String :=
  transformMinToHum example_min_add

/-- Example: Verify min to hum transformation -/
#eval example_hum_add
-- Expected: "function add(x: Int32, y: Int32): Int32 {x + y}"

/-- Example: Verify round-trip transformation -/
#eval transformHumToMin example_hum_add
-- Expected: "fn add(x:i32,y:i32):i32{x+y}"

/-!
## Example 2: Factorial Function

Demonstrates transformation of a recursive function with control flow.
-/

/-- min dialect: factorial function -/
def example_min_factorial : String :=
  "fn factorial(n:i32):i32{if n<=1{1}else{n*factorial(n-1)}}"

/-- hum dialect: transformed factorial function -/
def example_hum_factorial : String :=
  transformMinToHum example_min_factorial

/-- Example: Verify factorial transformation -/
#eval example_hum_factorial
-- Expected: "function factorial(n: Int32): Int32 {if (n <= 1) {1} else {n * factorial(n - 1)}}"

/-!
## Example 3: Pattern Matching

Demonstrates transformation of pattern matching expressions.
-/

/-- min dialect: pattern matching -/
def example_min_match : String :=
  "fn maybeAdd(opt:Option<i32>):i32{fix opt{Some(v)=>v+1,None=>0}}"

/-- hum dialect: transformed pattern matching -/
def example_hum_match : String :=
  transformMinToHum example_min_match

/-- Example: Verify pattern matching transformation -/
#eval example_hum_match
-- Expected: "function maybeAdd(opt: Option<Int32>): Int32 {match (opt) {Some(v) => v + 1, None => 0}}"

/-!
## Example 4: Variable Declaration

Demonstrates transformation of variable declarations with walrus operator.
-/

/-- min dialect: variable declaration -/
def example_min_let : String :=
  "x:=10"

/-- hum dialect: transformed variable declaration -/
def example_hum_let : String :=
  transformMinToHum example_min_let

/-- Example: Verify variable declaration transformation -/
#eval example_hum_let
-- Expected: "let x = 10;"

/-!
## Example 5: Complete Program

Demonstrates transformation of a complete program with multiple functions.
-/

/-- min dialect: complete program -/
def example_min_program : String :=
  "fn factorial(n:i32):i32{if n<=1{1}else{n*factorial(n-1)}}fn main():Effect<(),IO>{let result:=factorial(5);println(result)}"

/-- hum dialect: transformed program -/
def example_hum_program : String :=
  transformMinToHum example_min_program

/-- Example: Verify program transformation -/
#eval example_hum_program
-- Expected: "function factorial(n: Int32): Int32 {if (n <= 1) {1} else {n * factorial(n - 1)}}function main(): Effect<(), IO> {let result = factorial(5); println(result);}"

/-!
## Example 6: Empty Function

Demonstrates transformation of an empty function.
-/

/-- min dialect: empty function -/
def example_min_empty : String :=
  "fn empty():void{}"

/-- hum dialect: transformed empty function -/
def example_hum_empty : String :=
  transformMinToHum example_min_empty

/-- Example: Verify empty function transformation -/
#eval example_hum_empty
-- Expected: "function empty(): void {}"

/-!
## Example 7: Nested Functions

Demonstrates transformation of nested function definitions.
-/

/-- min dialect: nested functions -/
def example_min_nested : String :=
  "fn outer():i32{fn inner(x:i32):i32{x*2}inner(5)}"

/-- hum dialect: transformed nested functions -/
def example_hum_nested : String :=
  transformMinToHum example_min_nested

/-- Example: Verify nested function transformation -/
#eval example_hum_nested
-- Expected: "function outer(): Int32 {function inner(x: Int32): Int32 {x * 2}inner(5)}"

/-!
## Example 8: Generic Function

Demonstrates transformation of a generic function.
-/

/-- min dialect: generic function -/
def example_min_generic : String :=
  "fn id<T>(x:T):T{x}"

/-- hum dialect: transformed generic function -/
def example_hum_generic : String :=
  transformMinToHum example_min_generic

/-- Example: Verify generic function transformation -/
#eval example_hum_generic
-- Expected: "function id<T>(x: T): T {x}"

/-!
## Example 9: Projectional Editing

Demonstrates projectional editing workflow.
-/

/-- Initial min dialect code -/
def example_edit_initial_min : String :=
  "fn add(x:i32,y:i32):i32{x+y}"

/-- Initial hum projection -/
def example_edit_initial_hum : String :=
  transformMinToHum example_edit_initial_min

/-- Edit operation: add +1 to result -/
def example_edit_operation : Edit :=
  {
    location := { nodeId := 0, offset := 0 },
    operation := EditOp.replace "x+y+1",
    content := ""
  }

/-- Updated min dialect after edit -/
def example_edit_updated_min : String :=
  "fn add(x:i32,y:i32):i32{x+y+1}"

/-- Updated hum projection after edit -/
def example_edit_updated_hum : String :=
  transformMinToHum example_edit_updated_min

/-- Example: Verify projectional editing workflow -/
#eval example_edit_initial_hum
-- Expected: "function add(x: Int32, y: Int32): Int32 {x + y}"

#eval example_edit_updated_hum
-- Expected: "function add(x: Int32, y: Int32): Int32 {x + y + 1}"

/-!
## Example 10: LSP Protocol Interaction

Demonstrates LSP protocol request/response flow.
-/

/-- LSP get_projection request -/
def example_lsp_get_projection : LspRequest :=
  LspRequest.getProjection "file:///add.min" Dialect.hum

/-- LSP get_projection response -/
def example_lsp_projection_response : LspResponse :=
  LspResponse.projection "file:///add.min" Dialect.hum
    "function add(x: Int32, y: Int32): Int32 {x + y}" 42

/-- LSP apply_edit request -/
def example_lsp_apply_edit : LspRequest :=
  LspRequest.applyEdit "file:///add.min" {
      location := { nodeId := 0, offset := 0 },
      operation := EditOp.replace "x+y+1",
      content := ""
    }

/-- LSP apply_edit response -/
def example_lsp_edit_response : LspResponse :=
  LspResponse.editResult true [
      (Dialect.min, "fn add(x:i32,y:i32):i32{x+y+1}"),
      (Dialect.hum, "function add(x: Int32, y: Int32): Int32 {x + y + 1}")
    ]

/-- LSP projection_changed notification -/
def example_lsp_projection_changed : LspNotification :=
  LspNotification.projectionChanged "file:///add.min" Dialect.hum
    "function add(x: Int32, y: Int32): Int32 {x + y + 1}" 43

/-!
## Example 11: Keyword Expansion Table

Demonstrates all keyword transformations.
-/

/-- All min keywords and their hum equivalents -/
def example_keywords : List (String × String) :=
  [
    ("fn", "function"),
    ("ret", "return"),
    ("use", "import"),
    ("act", "actor"),
    ("fix", "match")
  ]

/-- Example: Verify keyword expansion -/
#eval example_keywords.map fun (minKw, humKw) =>
  (minKw, expandKeywords minKw, humKw)
-- Expected: All pairs should match after expansion

/-!
## Example 12: Type Expansion Table

Demonstrates all type transformations.
-/

/-- All min types and their hum equivalents -/
def example_types : List (String × String) :=
  [
    ("i8", "Int8"),
    ("i16", "Int16"),
    ("i32", "Int32"),
    ("i64", "Int64"),
    ("f32", "Float32"),
    ("f64", "Float64"),
    ("str", "String"),
    ("bool", "Boolean")
  ]

/-- Example: Verify type expansion -/
#eval example_types.map fun (minType, humType) =>
  (minType, expandKeywords minType, humType)
-- Expected: All pairs should match after expansion

/-!
## Example 13: Edge Cases

Demonstrates handling of edge cases.
-/

/-- Edge case: Empty string -/
def example_edge_empty : String := ""
#eval transformMinToHum example_edge_empty
-- Expected: ""

/-- Edge case: Single character -/
def example_edge_single : String := "x"
#eval transformMinToHum example_edge_single
-- Expected: "x"

/-- Edge case: Only keywords -/
def example_edge_keywords : String := "fn ret use act fix"
#eval transformMinToHum example_edge_keywords
-- Expected: "function return import actor match"

/-!
## Example 14: Complex Expression

Demonstrates transformation of complex nested expressions.
-/

/-- min dialect: complex expression -/
def example_min_complex : String :=
  "fn complex():i32{let x:=10;let y:=20;if x<y{x+y}else{x-y}}"

/-- hum dialect: transformed complex expression -/
def example_hum_complex : String :=
  transformMinToHum example_min_complex

/-- Example: Verify complex expression transformation -/
#eval example_hum_complex
-- Expected: "function complex(): Int32 {let x = 10; let y = 20; if (x < y) {x + y} else {x - y}}"

/-!
## Example 15: Round-Trip Verification

Demonstrates round-trip property for various code samples.
-/

/-- Test round-trip property for a sample -/
def example_round_trip_test (code : String) : Bool :=
  transformHumToMin (transformMinToHum code) = code

/-- Example: Test round-trip for add function -/
#eval example_round_trip_test example_min_add
-- Expected: true

/-- Example: Test round-trip for factorial function -/
#eval example_round_trip_test example_min_factorial
-- Expected: true

/-- Example: Test round-trip for pattern matching -/
#eval example_round_trip_test example_min_match
-- Expected: true

/-!
## Example 16: Projection Synchronization

Demonstrates projection synchronization after edits.
-/

/-- Initial projections -/
def example_sync_projections : Projections :=
  [
    {
      dialect := Dialect.min,
      ast := Morph.Syntax.Program.empty,
      renderer := fun _ => example_edit_initial_min,
      parser := fun _ => some Morph.Syntax.Program.empty
    },
    {
      dialect := Dialect.hum,
      ast := Morph.Syntax.Program.empty,
      renderer := fun _ => example_edit_initial_hum,
      parser := fun _ => some Morph.Syntax.Program.empty
    }
  ]

/-- Updated projections after edit -/
def example_sync_updated : Projections :=
  synchronizeProjections example_sync_projections Morph.Syntax.Program.empty

/-- Example: Verify projection synchronization -/
#eval example_sync_projections.length
-- Expected: 2

#eval example_sync_updated.length
-- Expected: 2

/-!
## Example 17: LSP State Machine

Demonstrates LSP state transitions.
-/

/-- Initial state: idle -/
def example_state_initial : LspState := LspState.idle

/-- State after get_projection request -/
def example_state_rendering : LspState :=
  lspStateTransition example_state_initial example_lsp_get_projection
-- Expected: LspState.rendering

/-- State after rendering completes -/
def example_state_idle_again : LspState :=
  lspStateTransition example_state_rendering example_lsp_get_projection
-- Expected: LspState.idle

/-- State after apply_edit request -/
def example_state_editing : LspState :=
  lspStateTransition example_state_idle_again example_lsp_apply_edit
-- Expected: LspState.editing

/-- State after edit applied -/
def example_state_synchronizing : LspState :=
  lspStateTransition example_state_editing example_lsp_apply_edit
-- Expected: LspState.synchronizing

/-- State after synchronization completes -/
def example_state_final : LspState :=
  lspStateTransition example_state_synchronizing example_lsp_apply_edit
-- Expected: LspState.idle

/-!
## Example 18: Isomorphism Verification

Demonstrates isomorphism between min and hum dialects.
-/

/-- Verify isomorphism: min and hum are isomorphic -/
example : isIsomorphic Dialect.min Dialect.hum := by
  exact min_hum_isomorphic

/-- Example: Check isomorphism property -/
#eval (min_hum_isomorphic : Prop)
-- This is a proof that min and hum are isomorphic

/-!
## Example 19: Semantic Equivalence

Demonstrates semantic equivalence between min and hum representations.
-/

/-- Example: Verify semantic equivalence -/
example_semantic_eq : semanticsPreserved example_min_add example_hum_add := by
  unfold semanticsPreserved
  trivial

/-!
## Example 20: Invariant Verification

Demonstrates verification of dialect system invariants.
-/

/-- Verify INV-001: All persisted code is in min dialect -/
example_INV001 : ∀ (file : String), file ∈ PersistedCode →
  ∃ (d : Dialect), d = Dialect.min := by
  exact INV001_canonical_representation

/-- Verify INV-002: All dialects of same AST are semantically equivalent -/
example_INV002 (projections : Projections)
  (h_sync : projectionSyncInvariant projections)
  (p1 p2 : Projection)
  (h_p1 : p1 ∈ projections)
  (h_p2 : p2 ∈ projections) :
  semanticsPreserved (p1.renderer p1.ast) (p2.renderer p2.ast) := by
  exact INV002_semantic_equivalence projections h_sync p1 p2 h_p1 h_p2

end Morph.Specs.DialectProjection

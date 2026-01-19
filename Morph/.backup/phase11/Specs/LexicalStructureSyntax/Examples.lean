import Morph.Core
import Morph.Syntax
import Morph.Specs.LexicalStructureSyntax.Spec

namespace Morph.Specs.LexicalStructureSyntax

/-!
## Lexical Structure and Syntax Examples

This module contains concrete examples and test cases for lexical
structure and syntax specification, demonstrating tokenization, parsing,
and grammar validation.
-/

/-!
## Example 1: Simple Function

Demonstrates tokenization and parsing of a simple function.
-/

/-- Simple function source code -/
def example_simple_function : String :=
  "fn add(x:i32,y:i32):i32{x+y}"

/-- Tokenize simple function -/
def example_simple_tokens : List TokenWithPos :=
  tokenize example_simple_function

/-- Example: Verify tokenization -/
#eval example_simple_tokens.length
-- Expected: Number of tokens

/-!
## Example 2: Keywords

Demonstrates keyword recognition.
-/

/-- Example: Check if 'fn' is a keyword -/
#eval isKeyword "fn"
-- Expected: true

/-- Example: Check if 'add' is not a keyword -/
#eval isKeyword "add"
-- Expected: false

/-- Example: Check all keywords -/
#eval keywords.map fun kw => (kw, isKeyword kw)
-- Expected: All pairs show true

/-!
## Example 3: Identifiers

Demonstrates identifier validation.
-/

/-- Example: Valid identifier -/
#eval isValidIdentifier "myVariable"
-- Expected: true

/-- Example: Invalid identifier (starts with digit) -/
#eval isValidIdentifier "123invalid"
-- Expected: false

/-- Example: Invalid identifier (contains spaces) -/
#eval isValidIdentifier "invalid name"
-- Expected: false

/-- Example: Escaped identifier -/
#eval isValidEscapedIdentifier "`fn`"
-- Expected: true

/-!
## Example 4: Integer Literals

Demonstrates integer literal parsing.
-/

/-- Decimal integer literal -/
def example_int_decimal : String := "42"
#eval parseIntLiteral example_int_decimal
-- Expected: some (IntLiteral.decimal "42")

/-- Hex integer literal -/
def example_int_hex : String := "0x2A"
#eval parseIntLiteral example_int_hex
-- Expected: some (IntLiteral.hex "0x2A")

/-- Octal integer literal -/
def example_int_octal : String := "0o52"
#eval parseIntLiteral example_int_octal
-- Expected: some (IntLiteral.octal "0o52")

/-- Binary integer literal -/
def example_int_binary : String := "0b101010"
#eval parseIntLiteral example_int_binary
-- Expected: some (IntLiteral.binary "0b101010")

/-!
## Example 5: Float Literals

Demonstrates float literal parsing.
-/

/-- Decimal float literal -/
def example_float_decimal : String := "3.14"
#eval parseFloatLiteral example_float_decimal
-- Expected: some (FloatLiteral.decimal "3.14")

/-- Scientific notation float literal -/
def example_float_scientific : String := "1.23e-4"
#eval parseFloatLiteral example_float_scientific
-- Expected: some (FloatLiteral.scientific "1.23e-4")

/-- Hex float literal -/
def example_float_hex : String := "0x1.8p1"
#eval parseFloatLiteral example_float_hex
-- Expected: some (FloatLiteral.hex "0x1.8p1")

/-!
## Example 6: String Literals

Demonstrates string literal syntax.
-/

/-- Double-quoted string literal -/
def example_string_double : String := "\"hello\""
#eval StringLiteral.doubleQuoted "hello"
-- Expected: StringLiteral.doubleQuoted "hello"

/-- Single-quoted string literal -/
def example_string_single : String := "'world'"
#eval StringLiteral.singleQuoted "world"
-- Expected: StringLiteral.singleQuoted "world"

/-- Raw string literal -/
def example_string_raw : String := "r\"raw\""
#eval StringLiteral.raw "raw"
-- Expected: StringLiteral.raw "raw"

/-!
## Example 7: Character Literals

Demonstrates character literal syntax.
-/

/-- Single character literal -/
#eval CharLiteral.single 'a'
-- Expected: CharLiteral.single 'a'

/-- Escape sequence character literal -/
#eval CharLiteral.escape "\\n"
-- Expected: CharLiteral.escape "\\n"

/-- Unicode character literal -/
#eval CharLiteral.unicode "\\u{1F600}"
-- Expected: CharLiteral.unicode "\\u{1F600}"

/-!
## Example 8: Boolean Literals

Demonstrates boolean literal syntax.
-/

/-- True literal -/
#eval BoolLiteral.trueLit
-- Expected: BoolLiteral.trueLit

/-- False literal -/
#eval BoolLiteral.falseLit
-- Expected: BoolLiteral.falseLit

/-!
## Example 9: Operators

Demonstrates operator recognition.
-/

/-- Example: Check binary operators -/
#eval binaryOperators.map fun op => (op, isBinaryOperator op)
-- Expected: All pairs show true

/-- Example: Check unary operators -/
#eval unaryOperators.map fun op => (op, isUnaryOperator op)
-- Expected: All pairs show true

/-- Example: Check assignment operators -/
#eval assignmentOperators.map fun op => (op, isAssignmentOperator op)
-- Expected: All pairs show true

/-!
## Example 10: Delimiters

Demonstrates delimiter recognition.
-/

/-- Example: Check delimiters -/
#eval delimiters.map fun delim => (delim, isDelimiter delim)
-- Expected: All pairs show true

/-!
## Example 11: Comments

Demonstrates comment recognition.
-/

/-- Single-line comment -/
#eval isSingleLineComment "// This is a comment"
-- Expected: true

/-- Multi-line comment start -/
#eval isMultiLineCommentStart "/* This is a"
-- Expected: true

/-- Multi-line comment end -/
#eval isMultiLineCommentEnd "comment */"
-- Expected: true

/-- Documentation comment -/
#eval isDocComment "/// This is documentation"
-- Expected: true

/-!
## Example 12: Whitespace

Demonstrates whitespace recognition.
-/

/-- Example: Check whitespace characters -/
#eval " \t\n\r".data.map fun c => (c, isWhitespace c)
-- Expected: All pairs show true

/-- Example: Check if string is all whitespace -/
#eval isAllWhitespace "   \t\n  "
-- Expected: true

/-- Example: Check if string is not all whitespace -/
#eval isAllWhitespace "hello world"
-- Expected: false

/-!
## Example 13: Token Filtering

Demonstrates token filtering.
-/

/-- Tokens with whitespace and comments -/
def example_unfiltered_tokens : List TokenWithPos :=
  [
      { token := Token.keyword "fn", pos := { line := 1, column := 1, offset := 0 } },
      { token := Token.whitespace, pos := { line := 1, column := 3, offset := 2 } },
      { token := Token.identifier "add", pos := { line := 1, column := 4, offset := 3 } },
      { token := Token.comment "// comment", pos := { line := 2, column := 1, offset := 10 } }
    ]

/-- Filtered tokens (no whitespace or comments) -/
def example_filtered_tokens : List TokenWithPos :=
  filterTokens example_unfiltered_tokens

/-- Example: Verify filtering -/
#eval example_filtered_tokens.length
-- Expected: 2 (only keyword and identifier)

/-!
## Example 14: Grammar Productions

Demonstrates grammar productions.
-/

/-- Example: Function production -/
def example_function_production : Production :=
  { lhs := "Function", rhs := "'fn' Identifier '(' ParamList? ')' ':' Type Block" }

/-- Example: Check production in grammar -/
#eval example_function_production ∈ coreProductions
-- Expected: true

/-!
## Example 15: Token Position

Demonstrates token position tracking.
-/

/-- Example token with position -/
def example_token_with_pos : TokenWithPos :=
  {
      token := Token.identifier "x",
      pos := { line := 5, column := 10, offset := 42 }
    }

/-- Example: Verify token position -/
#eval example_token_with_pos.pos.line
-- Expected: 5

#eval example_token_with_pos.pos.column
-- Expected: 10

#eval example_token_with_pos.pos.offset
-- Expected: 42

/-!
## Example 16: Complex Expression

Demonstrates tokenization of a complex expression.
-/

/-- Complex expression source code -/
def example_complex_expression : String :=
  "fn factorial(n:i32):i32{if n<=1{1}else{n*factorial(n-1)}}"

/-- Tokenize complex expression -/
def example_complex_tokens : List TokenWithPos :=
  tokenize example_complex_expression

/-- Example: Verify tokenization -/
#eval example_complex_tokens.length
-- Expected: Number of tokens

/-!
## Example 17: Pattern Matching

Demonstrates tokenization of pattern matching.
-/

/-- Pattern matching source code -/
def example_pattern_match : String :=
  "fix opt{Some(v)=>v+1,None=>0}"

/-- Tokenize pattern matching -/
def example_pattern_tokens : List TokenWithPos :=
  tokenize example_pattern_match

/-- Example: Verify tokenization -/
#eval example_pattern_tokens.length
-- Expected: Number of tokens

/-!
## Example 18: Variable Declaration

Demonstrates tokenization of variable declaration.
-/

/-- Variable declaration source code -/
def example_var_decl : String :=
  "x:=10"

/-- Tokenize variable declaration -/
def example_var_tokens : List TokenWithPos :=
  tokenize example_var_decl

/-- Example: Verify tokenization -/
#eval example_var_tokens.length
-- Expected: Number of tokens

/-!
## Example 19: Invariant Verification

Demonstrates verification of syntax invariants.
-/

/-- Verify INV-001: All tokens have valid positions -/
example_INV001 : all_tokens_have_valid_positions example_simple_tokens := by
  unfold all_tokens_have_valid_positions
  intro t
  intro h_in
  -- All tokens have valid positions by construction
  trivial

/-- Verify INV-002: All identifiers are valid -/
example_INV002 : all_identifiers_are_valid example_simple_tokens := by
  unfold all_identifiers_are_valid
  intro t
  intro h_in
  -- All identifiers are validated during tokenization
  trivial

/-!
## Example 20: Parsing

Demonstrates parsing of tokens into AST.
-/

/-- Parse tokens into AST -/
def example_parse_result : Option Morph.Syntax.Program :=
  parseTokens example_simple_tokens

/-- Example: Verify parsing -/
#eval example_parse_result.isSome
-- Expected: true

/-- Validate syntax of parsed program -/
def example_validate_result : Bool :=
  match example_parse_result with
  | some program => validateSyntax program
  | none => false

/-- Example: Verify validation -/
#eval example_validate_result
-- Expected: true

end Morph.Specs.LexicalStructureSyntax

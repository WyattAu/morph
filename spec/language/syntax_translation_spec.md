# Syntax Translation Specification

* File:* `language\syntax_translation_spec.md`
* Version:* 1.0.0
* Context:* Layer 2 (Compiler)
* Formalism:* EBNF, Category Theory, Type Theory
* Status:* Active
* Last Modified:* 2026-01-02
* Author:* Language Design Team
* Reviewers:* Architecture Team, Tooling Team

---

## 1. Introduction

### 1.1 Purpose

This specification defines formal syntax translation rules between the `min` and `hum` dialects of the Morph programming language. It provides bidirectional transformation functions, correctness properties, and algorithms for converting between these dialects while preserving semantic equivalence.

### 1.2 Scope

This specification covers:
- Formal grammar definitions for `min` dialect
- Formal grammar definitions for `hum` dialect
- Bidirectional translation rules (min ↔ hum)
- Translation correctness properties and invariants
- Translation algorithms and complexity analysis
- Examples of translations for all language constructs
- Theorems proving translation correctness

This specification does NOT cover:
- AST node type definitions (see [`ast_graph_spec.md`](ast_graph_spec.md))
- LSP protocol implementation (see [`dialect_projection_spec.md`](dialect_projection_spec.md))
- Lexical analysis and tokenization (see [`lexical_strcutre_syntax_spec.md`](lexical_strcutre_syntax_spec.md))

### 1.3 Definitions, Acronyms, and Abbreviations

| Term | Definition |
|------|------------|
| **min dialect** | Agent-optimized syntax with minimal verbosity, high information density |
| **hum dialect** | Human-optimized syntax with explicit verbosity, improved readability |
| **Translation** | Bidirectional transformation between dialects preserving semantics |
| **Isomorphism** | Bidirectional mapping preserving structure and semantics |
| **Round-trip** | Translation from dialect A to B and back to A yielding equivalent code |
| **AST** | Abstract Syntax Tree - hierarchical representation of program structure |

### 1.4 References

- [`dialect_projection_spec.md`](dialect_projection_spec.md) - Dialect system and isomorphism
- [`lexical_strcutre_syntax_spec.md`](lexical_strcutre_syntax_spec.md) - Lexical structure and syntax
- [`ast_graph_spec.md`](ast_graph_spec.md) - AST graph structure
- SPEC_GAPS_AND_BASIS.md - Gap analysis (Section 5.5)
- SPEC_FIX_PROPOSAL.md - Fix proposal (Section 3.5)

---

## 2. Formal Definitions

### 2.1 Dialect Syntax Spaces

#### 2.1.1 min Dialect Syntax Space

Let $\mathcal{L}_{\text{min}}$ be the set of all valid `min` dialect programs.

**Formal Definition:*

$$
\mathcal{L}_{\text{min}} = \{ \text{code} \mid \text{code} \text{ is valid min syntax} \}
$$

**Characteristics:*
- Minimal whitespace (only where necessary for token separation)
- Abbreviated keywords (e.g., `fn` instead of `function`)
- Compact type annotations (e.g., `i32` instead of `Int32`)
- Implicit returns (last expression in block)
- Concise control flow syntax

#### 2.1.2 hum Dialect Syntax Space

Let $\mathcal{L}_{\text{hum}}$ be the set of all valid `hum` dialect programs.

**Formal Definition:*

$$
\mathcal{L}_{\text{hum}} = \{ \text{code} \mid \text{code} \text{ is valid hum syntax} \}
$$

**Characteristics:*
- Explicit whitespace for readability
- Full keywords (e.g., `function` instead of `fn`)
- Verbose type annotations (e.g., `Int32` instead of `i32`)
- Explicit returns (return statements)
- Parenthesized conditions and expressions

### 2.2 Translation Functions

#### 2.2.1 Forward Translation (min → hum)

$$
\mathcal{T}_{\text{min}\to\text{hum}}: \mathcal{L}_{\text{min}} \to \mathcal{L}_{\text{hum}}
$$

**Definition:*

$$
\forall \text{code}_{\text{min}} \in \mathcal{L}_{\text{min}}, \mathcal{T}_{\text{min}\to\text{hum}}(\text{code}_{\text{min}}) = \text{code}_{\text{hum}} \in \mathcal{L}_{\text{hum}}
$$

#### 2.2.2 Reverse Translation (hum → min)

$$
\mathcal{T}_{\text{hum}\to\text{min}}: \mathcal{L}_{\text{hum}} \to \mathcal{L}_{\text{min}}
$$

**Definition:*

$$
\forall \text{code}_{\text{hum}} \in \mathcal{L}_{\text{hum}}, \mathcal{T}_{\text{hum}\to\text{min}}(\text{code}_{\text{hum}}) = \text{code}_{\text{min}} \in \mathcal{L}_{\text{min}}
$$

### 2.3 Semantic Equivalence

Two programs are semantically equivalent if they produce identical results for all inputs.

**Formal Definition:*

$$
\text{code}_1 \equiv \text{code}_2 \iff \forall \text{input}, \text{Semantics}(\text{code}_1, \text{input}) = \text{Semantics}(\text{code}_2, \text{input})
$$

---

## 3. Formal Grammars

### 3.1 min Dialect Grammar

#### 3.1.1 Compilation Unit

```ebnf
CompilationUnit ::= { UseDecl } { TopLevelDecl }
UseDecl         ::= 'use' Identifier [ 'as' Identifier ] ';'
TopLevelDecl    ::= FuncDecl | TypeDecl | ActDecl | ConstDecl
```

#### 3.1.2 Declarations

```ebnf
/* Function Declaration */
FuncDecl    ::= 'fn' Identifier [Generics] Params [ '->' Type ] Block

/* Type Declaration */
TypeDecl    ::= 'type' Identifier [Generics] '=' TypeBody ';'
TypeBody    ::= '{' FieldList '}'                     (* Product/Struct *)
              | Variant { '|' Variant }               (* Sum/Enum *)

/* Constant Declaration */
ConstDecl   ::= 'const' Identifier '=' ( Expr | '??' ) ';'

/* Variable Declaration */
VarDecl     ::= Identifier ':=' Expr ';'              (* Inferred *)
              | Identifier ':' Type '=' Expr ';'      (* Explicit *)
```

#### 3.1.3 Parameters and Generics

```ebnf
Params      ::= '(' [ ParamList ] ')'
ParamList   ::= Param { ',' Param }
Param       ::= Identifier ':' Type [ '=' Expr ]

Generics    ::= '<' GenericList '>'
GenericList ::= Generic { ',' Generic }
Generic     ::= Identifier [ ':' TypeConstraint ]
```

#### 3.1.4 Types

```ebnf
Type        ::= PrimitiveType
              | Identifier [ Generics ]
              | Type '?'                          (* Optional *)
              | '^' Type                          (* Isolated *)
              | '#' Type                          (* Value *)
              | '&' Type                          (* Reference *)
              | '(' TypeList ')'                   (* Tuple *)

PrimitiveType ::= 'i8' | 'i16' | 'i32' | 'i64'
              | 'f32' | 'f64'
              | 'str' | 'bool' | 'void'

TypeList    ::= Type { ',' Type }
```

#### 3.1.5 Expressions

```ebnf
Expr        ::= Literal
              | Identifier
              | Expr '(' [ ArgList ] ')'           (* Function call *)
              | Expr '.' Identifier                (* Field access *)
              | Expr '[' Expr ']'                 (* Index *)
              | Expr '?'                          (* Null propagation *)
              | Expr '??' Expr                    (* Null coalescing *)
              | Expr '|' '>' Expr                 (* Pipe *)
              | Expr BinaryOp Expr
              | UnaryOp Expr
              | '(' Expr ')'

ArgList     ::= Expr { ',' Expr }

BinaryOp    ::= '+' | '-' | '*' | '/' | '%'
              | '==' | '!=' | '<' | '>' | '<=' | '>='
              | '&&' | '||' | 'in' | 'is' | 'as'

UnaryOp     ::= '!' | '-' | '^'
```

#### 3.1.6 Statements

```ebnf
Statement   ::= VarDecl
              | 'ret' [Expr] ';'
              | 'fix' Expr '{' { MatchArm } '}'       (* Pattern match *)
              | 'if' Expr Block [ 'else' Block ]
              | 'loop' Block
              | 'defer' Block
              | Expr ';'

MatchArm    ::= Pattern '=>' Expr [ ',' ]
Pattern     ::= Literal
              | Identifier
              | Identifier '(' [ PatternList ] ')'
              | '{' FieldPatternList '}'
```

#### 3.1.7 Blocks

```ebnf
Block       ::= '{' { Statement } '}'
```

#### 3.1.8 Literals

```ebnf
Literal     ::= Integer | Float | String | FencedString | 'true' | 'false' | 'null'

Integer     ::= [ '-' ] Digit { Digit }
Float       ::= [ '-' ] Digit { Digit } '.' Digit { Digit } [ 'e' [ '-' ] Digit { Digit } ]
String      ::= '"' { Char } '"'
FencedString ::= Backticks [ Tag ] Newline AnyChar* Newline Backticks
Backticks   ::= '```' { '`' }
```

### 3.2 hum Dialect Grammar

#### 3.2.1 Compilation Unit

```ebnf
CompilationUnit ::= { UseDecl } { TopLevelDecl }
UseDecl         ::= 'import' Identifier [ 'as' Identifier ] ';'
TopLevelDecl    ::= FuncDecl | TypeDecl | ActDecl | ConstDecl
```

#### 3.2.2 Declarations

```ebnf
/* Function Declaration */
FuncDecl    ::= 'function' Identifier [Generics] Params [ ':' Type ] Block

/* Type Declaration */
TypeDecl    ::= 'type' Identifier [Generics] '=' TypeBody ';'
TypeBody    ::= '{' FieldList '}'                     (* Product/Struct *)
              | Variant { '|' Variant }               (* Sum/Enum *)

/* Constant Declaration */
ConstDecl   ::= 'const' Identifier '=' ( Expr | '??' ) ';'

/* Variable Declaration */
VarDecl     ::= 'let' Identifier [ ':' Type ] '=' Expr ';'
```

#### 3.2.3 Parameters and Generics

```ebnf
Params      ::= '(' [ ParamList ] ')'
ParamList   ::= Param { ',' Param }
Param       ::= Identifier ':' Type [ '=' Expr ]

Generics    ::= '<' GenericList '>'
GenericList ::= Generic { ',' Generic }
Generic     ::= Identifier [ ':' TypeConstraint ]
```

#### 3.2.4 Types

```ebnf
Type        ::= PrimitiveType
              | Identifier [ Generics ]
              | Type '?'                          (* Optional *)
              | '^' Type                          (* Isolated *)
              | '#' Type                          (* Value *)
              | '&' Type                          (* Reference *)
              | '(' TypeList ')'                   (* Tuple *)

PrimitiveType ::= 'Int8' | 'Int16' | 'Int32' | 'Int64'
              | 'Float32' | 'Float64'
              | 'String' | 'Boolean' | 'Void'

TypeList    ::= Type { ',' Type }
```

#### 3.2.5 Expressions

```ebnf
Expr        ::= Literal
              | Identifier
              | Expr '(' [ ArgList ] ')'           (* Function call *)
              | Expr '.' Identifier                (* Field access *)
              | Expr '[' Expr ']'                 (* Index *)
              | Expr '?'                          (* Null propagation *)
              | Expr '??' Expr                    (* Null coalescing *)
              | Expr '|' '>' Expr                 (* Pipe *)
              | Expr BinaryOp Expr
              | UnaryOp Expr
              | '(' Expr ')'

ArgList     ::= Expr { ',' Expr }

BinaryOp    ::= '+' | '-' | '*' | '/' | '%'
              | '==' | '!=' | '<' | '>' | '<=' | '>='
              | '&&' | '||' | 'in' | 'is' | 'as'

UnaryOp     ::= '!' | '-' | '^'
```

#### 3.2.6 Statements

```ebnf
Statement   ::= VarDecl
              | 'return' [Expr] ';'
              | 'match' '(' Expr ')' '{' { MatchArm } '}'
              | 'if' '(' Expr ')' Block [ 'else' Block ]
              | 'loop' Block
              | 'defer' Block
              | Expr ';'

MatchArm    ::= 'case' Pattern '=>' Expr [ ',' ]
Pattern     ::= Literal
              | Identifier
              | Identifier '(' [ PatternList ] ')'
              | '{' FieldPatternList '}'
```

#### 3.2.7 Blocks

```ebnf
Block       ::= '{' { Statement } '}'
```

#### 3.2.8 Literals

```ebnf
Literal     ::= Integer | Float | String | FencedString | 'true' | 'false' | 'null'

Integer     ::= [ '-' ] Digit { Digit }
Float       ::= [ '-' ] Digit { Digit } '.' Digit { Digit } [ 'e' [ '-' ] Digit { Digit } ]
String      ::= '"' { Char } '"'
FencedString ::= Backticks [ Tag ] Newline AnyChar* Newline Backticks
Backticks   ::= '```' { '`' }
```

---

## 4. Translation Rules

### 4.1 Keyword Translation Table

| min Keyword | hum Keyword | Translation Rule |
|-------------|--------------|------------------|
| `fn` | `function` | Replace `fn` with `function` |
| `ret` | `return` | Replace `ret` with `return` |
| `use` | `import` | Replace `use` with `import` |
| `act` | `actor` | Replace `act` with `actor` |
| `fix` | `match` | Replace `fix` with `match` |
| `const` | `const` | No change |
| `type` | `type` | No change |
| `if` | `if` | No change (but add parentheses) |
| `else` | `else` | No change |
| `loop` | `loop` | No change |
| `defer` | `defer` | No change |
| `in` | `in` | No change |
| `is` | `is` | No change |
| `as` | `as` | No change |

### 4.2 Type Translation Table

| min Type | hum Type | Translation Rule |
|----------|-----------|------------------|
| `i8` | `Int8` | Replace `i8` with `Int8` |
| `i16` | `Int16` | Replace `i16` with `Int16` |
| `i32` | `Int32` | Replace `i32` with `Int32` |
| `i64` | `Int64` | Replace `i64` with `Int64` |
| `f32` | `Float32` | Replace `f32` with `Float32` |
| `f64` | `Float64` | Replace `f64` with `Float64` |
| `str` | `String` | Replace `str` with `String` |
| `bool` | `Boolean` | Replace `bool` with `Boolean` |
| `void` | `Void` | Replace `void` with `Void` |

### 4.3 Operator Translation Table

| min Operator | hum Operator | Translation Rule |
|--------------|---------------|------------------|
| `:=` | `let ... =` | Replace `x := expr` with `let x = expr;` |
| `->` | `:` | Replace `->` with `:` in function signatures |
| `|>` | `|>` | No change |
| `??` | `??` | No change |
| `?` | `?` | No change |
| `^` | `^` | No change |
| `#` | `#` | No change |
| `&` | `&` | No change |

### 4.4 Expression Translation Rules

#### 4.4.1 Function Call

**min:*
```morph
fn_name(arg1, arg2)
```

**hum:*
```morph
fn_name(arg1, arg2)
```

**Translation Rule:* No change in syntax, only type annotations differ.

#### 4.4.2 Binary Operation

**min:*
```morph
x+y
```

**hum:*
```morph
x + y
```

**Translation Rule:* Add spaces around binary operators.

#### 4.4.3 Unary Operation

**min:*
```morph
-x
```

**hum:*
```morph
-x
```

**Translation Rule:* No change.

#### 4.4.4 Parenthesized Expression

**min:*
```morph
(x+y)
```

**hum:*
```morph
(x + y)
```

**Translation Rule:* Add spaces around operators inside parentheses.

### 4.5 Statement Translation Rules

#### 4.5.1 Variable Declaration

**min:*
```morph
x:=10
```

**hum:*
```morph
let x = 10;
```

**Translation Rule:*
1. Replace `:=` with `=`
2. Add `let` keyword before identifier
3. Add semicolon at end

**min:*
```morph
x:i32=10
```

**hum:*
```morph
let x: Int32 = 10;
```

**Translation Rule:*
1. Replace `:` with `: ` (add space)
2. Replace type name with hum equivalent
3. Replace `=` with ` =`
4. Add `let` keyword before identifier
5. Add semicolon at end

#### 4.5.2 Return Statement

**min:*
```morph
ret x
```

**hum:*
```morph
return x;
```

**Translation Rule:*
1. Replace `ret` with `return`
2. Add semicolon at end

**min:*
```morph
ret
```

**hum:*
```morph
return;
```

**Translation Rule:*
1. Replace `ret` with `return`
2. Add semicolon at end

#### 4.5.3 If Statement

**min:*
```morph
if cond{a}else{b}
```

**hum:*
```morph
if (cond) {
  a;
} else {
  b;
}
```

**Translation Rule:*
1. Add parentheses around condition
2. Add newline and indentation after opening brace
3. Add semicolon after each statement in block
4. Add newline before closing brace

**min:*
```morph
if cond{a}
```

**hum:*
```morph
if (cond) {
  a;
}
```

**Translation Rule:*
1. Add parentheses around condition
2. Add newline and indentation after opening brace
3. Add semicolon after each statement in block
4. Add newline before closing brace

#### 4.5.4 Match Statement

**min:*
```morph
fix x{
  Some(v)=>v,
  None=>0
}
```

**hum:*
```morph
match (x) {
  case Some(v) => v,
  case None => 0
}
```

**Translation Rule:*
1. Replace `fix` with `match`
2. Add parentheses around expression
3. Replace `pattern =>` with `case pattern =>`
4. Add newline and indentation after opening brace
5. Add semicolon after each arm expression
6. Add newline before closing brace

#### 4.5.5 Loop Statement

**min:*
```morph
loop{body}
```

**hum:*
```morph
loop {
  body;
}
```

**Translation Rule:*
1. Add newline and indentation after opening brace
2. Add semicolon after each statement in block
3. Add newline before closing brace

### 4.6 Function Definition Translation Rules

#### 4.6.1 Simple Function

**min:*
```morph
fn add(x:i32,y:i32):i32{x+y}
```

**hum:*
```morph
function add(x: Int32, y: Int32): Int32 {
  return x + y;
}
```

**Translation Rule:*
1. Replace `fn` with `function`
2. Add spaces around colons in parameter list
3. Replace `->` with `:`
4. Expand type names
5. Add newline and indentation after opening brace
6. Wrap body expression in `return`
7. Add semicolon after return
8. Add newline before closing brace

#### 4.6.2 Generic Function

**min:*
```morph
fn id<T>(x:T):T{x}
```

**hum:*
```morph
function id<T>(x: T): T {
  return x;
}
```

**Translation Rule:*
1. Replace `fn` with `function`
2. Add spaces around colons in parameter list
3. Replace `->` with `:`
4. Add newline and indentation after opening brace
5. Wrap body expression in `return`
6. Add semicolon after return
7. Add newline before closing brace

#### 4.6.3 Function with Multiple Statements

**min:*
```morph
fn process(x:i32):i32{
  y:=x*2;
  ret y
}
```

**hum:*
```morph
function process(x: Int32): Int32 {
  let y = x * 2;
  return y;
}
```

**Translation Rule:*
1. Replace `fn` with `function`
2. Add spaces around colons in parameter list
3. Replace `->` with `:`
4. Expand type names
5. Add newline and indentation after opening brace
6. Translate each statement in body
7. Add newline before closing brace

### 4.7 Type Definition Translation Rules

#### 4.7.1 Struct Definition

**min:*
```morph
type Point={x:i32,y:i32}
```

**hum:*
```morph
type Point = {
  x: Int32,
  y: Int32
};
```

**Translation Rule:*
1. Add space around `=`
2. Add newline and indentation after opening brace
3. Add spaces around colons in field list
4. Expand type names
5. Add commas between fields
6. Add semicolon after closing brace

#### 4.7.2 Enum Definition

**min:*
```morph
type Option<T>=Some(T)|None
```

**hum:*
```morph
type Option<T> = Some(T) | None;
```

**Translation Rule:*
1. Add space around `=`
2. Add spaces around `|`

### 4.8 Pattern Translation Rules

#### 4.8.1 Literal Pattern

**min:*
```morph
Some(42)
```

**hum:*
```morph
Some(42)
```

**Translation Rule:* No change.

#### 4.8.2 Variable Pattern

**min:*
```morph
Some(v)
```

**hum:*
```morph
Some(v)
```

**Translation Rule:* No change.

#### 4.8.3 Struct Pattern

**min:*
```morph
Point{x,y}
```

**hum:*
```morph
Point { x, y }
```

**Translation Rule:* Add spaces around braces.

### 4.9 Comment Translation Rules

#### 4.9.1 Single-Line Comment

**min:*
```morph
// This is a comment
```

**hum:*
```morph
// This is a comment
```

**Translation Rule:* No change.

#### 4.9.2 Multi-Line Comment

**min:*
```morph
/* This is a
   multi-line comment */
```

**hum:*
```morph
/* This is a
   multi-line comment */
```

**Translation Rule:* No change.

### 4.10 Whitespace Translation Rules

#### 4.10.1 min to hum Whitespace

**Translation Rule:*
1. Add newline after each semicolon
2. Add newline after opening brace `{`
3. Add newline before closing brace `}`
4. Add 2 spaces of indentation for each nesting level
5. Add spaces around binary operators
6. Add spaces after commas in lists

#### 4.10.2 hum to min Whitespace

**Translation Rule:*
1. Remove all newlines (except where required for token separation)
2. Remove all indentation
3. Remove spaces around binary operators
4. Remove spaces after commas in lists
5. Keep single space where necessary for token separation

---

## 5. Requirements

### 5.1 Functional Requirements

#### 5.1.1 Translation Completeness Requirements

**SYN-REQ-001:* THE system SHALL provide bidirectional translation between min and hum dialects for all language constructs.

* **Priority:* Critical
* **Verification Method:* Test
* **Rationale:* Ensures complete coverage of language features
* **Dependencies:* None
* **Traceability:* Section 4 (Translation Rules)

**SYN-REQ-002:* THE system SHALL translate all keywords from min to hum and vice versa.

* **Priority:* Critical
* **Verification Method:* Test
* **Rationale:* Keywords are fundamental to syntax
* **Dependencies:* SYN-REQ-001
* **Traceability:* Section 4.1 (Keyword Translation Table)

**SYN-REQ-003:* THE system SHALL translate all primitive types from min to hum and vice versa.

* **Priority:* Critical
* **Verification Method:* Test
* **Rationale:* Types are fundamental to type system
* **Dependencies:* SYN-REQ-001
* **Traceability:* Section 4.2 (Type Translation Table)

**SYN-REQ-004:* THE system SHALL translate all operators from min to hum and vice versa.

* **Priority:* Critical
* **Verification Method:* Test
* **Rationale:* Operators are fundamental to expressions
* **Dependencies:* SYN-REQ-001
* **Traceability:* Section 4.3 (Operator Translation Table)

#### 5.1.2 Translation Correctness Requirements

**SYN-REQ-005:* THE system SHALL preserve semantic equivalence during translation.

* **Priority:* Critical
* **Verification Method:* Analysis
* **Rationale:* Ensures translated code has identical behavior
* **Dependencies:* SYN-REQ-001
* **Traceability:* Section 5 (Correctness Properties)

**SYN-REQ-006:* THE system SHALL satisfy the round-trip property for all valid code.

* **Priority:* Critical
* **Verification Method:* Test
* **Rationale:* Ensures translation is reversible
* **Dependencies:* SYN-REQ-005
* **Traceability:* Section 5.2 (Round-Trip Property)

**SYN-REQ-007:* THE system SHALL preserve type information during translation.

* **Priority:* Critical
* **Verification Method:* Test
* **Rationale:* Type safety must be maintained
* **Dependencies:* SYN-REQ-005
* **Traceability:* Section 4.2 (Type Translation Table)

#### 5.1.3 Translation Algorithm Requirements

**SYN-REQ-008:* THE system SHALL provide a min-to-hum translation algorithm with O(n) time complexity.

* **Priority:* High
* **Verification Method:* Analysis
* **Metric:* Translation time < 100ms for 10,000 tokens
* **Rationale:* Ensures responsive translation
* **Dependencies:* SYN-REQ-001
* **Traceability:* Section 6 (Translation Algorithms)

**SYN-REQ-009:* THE system SHALL provide a hum-to-min translation algorithm with O(n) time complexity.

* **Priority:* High
* **Verification Method:* Analysis
* **Metric:* Translation time < 100ms for 10,000 tokens
* **Rationale:* Ensures responsive translation
* **Dependencies:* SYN-REQ-001
* **Traceability:* Section 6 (Translation Algorithms)

**SYN-REQ-010:* THE system SHALL handle nested constructs correctly during translation.

* **Priority:* High
* **Verification Method:* Test
* **Rationale:* Nested constructs are common in real code
* **Dependencies:* SYN-REQ-001
* **Traceability:* Section 4 (Translation Rules)

### 5.2 Non-Functional Requirements

#### 5.2.1 Performance Requirements

**SYN-NFR-001:* THE system SHALL translate min to hum in O(n) time complexity, where n is the number of tokens.

* **Priority:* High
* **Verification Method:* Analysis
* **Metric:* Translation time < 100ms for 10,000 tokens
* **Rationale:* Ensures responsive IDE experience

**SYN-NFR-002:* THE system SHALL translate hum to min in O(n) time complexity, where n is the number of tokens.

* **Priority:* High
* **Verification Method:* Analysis
* **Metric:* Translation time < 100ms for 10,000 tokens
* **Rationale:* Ensures responsive IDE experience

**SYN-NFR-003:* THE system SHALL use O(1) space complexity for translation.

* **Priority:* Medium
* **Verification Method:* Analysis
* **Metric:* Memory usage < 10MB for 10,000 tokens
* **Rationale:* Ensures efficient memory usage

#### 5.2.2 Reliability Requirements

**SYN-NFR-004:* THE system SHALL guarantee 100% semantic equivalence for all translations.

* **Priority:* Critical
* **Verification Method:* Test
* **Metric:* 0 semantic equivalence failures
* **Rationale:* Prevents bugs from translation errors

**SYN-NFR-005:* THE system SHALL never lose information during translation.

* **Priority:* Critical
* **Verification Method:* Test
* **Metric:* 0 information loss events
* **Rationale:* Ensures round-trip property

#### 5.2.3 Maintainability Requirements

**SYN-NFR-006:* THE system SHALL allow addition of new language constructs without modifying existing translation rules.

* **Priority:* Medium
* **Verification Method:* Analysis
* **Rationale:* Enables extensibility
* **Traceability:* Section 4 (Translation Rules)

---

## 6. Translation Algorithms

### 6.1 min to hum Translation Algorithm

#### 6.1.1 Algorithm Overview

The min-to-hum translation algorithm transforms min dialect code to hum dialect code by applying a series of syntactic transformations while preserving semantic structure.

#### 6.1.2 Algorithm Definition

**Algorithm:* `translate_min_to_hum`

**Input:* `code_min: String` (valid min dialect code)

**Output:* `code_hum: String` (equivalent hum dialect code)

**Mathematical Definition:*

$$
\text{translate\_min\_to\_hum}(\text{code}_{\text{min}}) = \text{apply\_transformations}(\text{parse}(\text{code}_{\text{min}}), \mathcal{T}_{\text{min}\to\text{hum}})
$$

**Pseudocode:*

```
function translate_min_to_hum(code_min: String): String {
    // Parse min code to AST
    ast = parse_min(code_min);
    
    // Apply transformations
    ast_hum = transform_ast(ast, min_to_hum_rules);
    
    // Render AST to hum code
    code_hum = render_hum(ast_hum);
    
    return code_hum;
}

function transform_ast(node: AST, rules: TransformationRules): AST {
    match node.type {
        case Function:
            return transform_function(node, rules);
        case If:
            return transform_if(node, rules);
        case Match:
            return transform_match(node, rules);
        case Let:
            return transform_let(node, rules);
        case Return:
            return transform_return(node, rules);
        case BinaryOp:
            return transform_binary_op(node, rules);
        case Call:
            return transform_call(node, rules);
        default:
            return node;
    }
}

function transform_function(node: AST, rules: TransformationRules): AST {
    // Replace 'fn' with 'function'
    node.keyword = 'function';
    
    // Add spaces around colons in parameters
    for param in node.parameters {
        param.type_annotation = add_spaces(param.type_annotation);
    }
    
    // Replace '->' with ':'
    node.return_type_annotation = node.return_type_annotation.replace('->', ':');
    
    // Expand type names
    node.return_type = expand_type(node.return_type);
    for param in node.parameters {
        param.type = expand_type(param.type);
    }
    
    // Add explicit return if implicit
    if is_implicit_return(node.body) {
        node.body = wrap_in_return(node.body);
    }
    
    return node;
}

function transform_if(node: AST, rules: TransformationRules): AST {
    // Add parentheses around condition
    node.condition = wrap_in_parentheses(node.condition);
    
    // Add semicolons to statements
    node.then_branch = add_semicolons(node.then_branch);
    if node.else_branch exists {
        node.else_branch = add_semicolons(node.else_branch);
    }
    
    return node;
}

function transform_match(node: AST, rules: TransformationRules): AST {
    // Replace 'fix' with 'match'
    node.keyword = 'match';
    
    // Add parentheses around expression
    node.expression = wrap_in_parentheses(node.expression);
    
    // Add 'case' to each arm
    for arm in node.arms {
        arm.pattern = add_case_keyword(arm.pattern);
        arm.expression = add_semicolon(arm.expression);
    }
    
    return node;
}

function transform_let(node: AST, rules: TransformationRules): AST {
    // Replace ':=' with '='
    node.operator = '=';
    
    // Add 'let' keyword
    node.keyword = 'let';
    
    // Add semicolon
    node.semicolon = true;
    
    // Expand type if explicit
    if node.type_annotation exists {
        node.type = expand_type(node.type);
    }
    
    return node;
}

function transform_return(node: AST, rules: TransformationRules): AST {
    // Replace 'ret' with 'return'
    node.keyword = 'return';
    
    // Add semicolon
    node.semicolon = true;
    
    return node;
}

function transform_binary_op(node: AST, rules: TransformationRules): AST {
    // Add spaces around operator
    node.operator = ' ' + node.operator + ' ';
    
    return node;
}

function expand_type(type: Type): Type {
    match type.name {
        case 'i8': return Type('Int8');
        case 'i16': return Type('Int16');
        case 'i32': return Type('Int32');
        case 'i64': return Type('Int64');
        case 'f32': return Type('Float32');
        case 'f64': return Type('Float64');
        case 'str': return Type('String');
        case 'bool': return Type('Boolean');
        case 'void': return Type('Void');
        default: return type;
    }
}
```

**Complexity:*
- **Time:* $O(n)$ where $n$ is the number of AST nodes
- **Space:* $O(n)$ for storing transformed AST

### 6.2 hum to min Translation Algorithm

#### 6.2.1 Algorithm Overview

The hum-to-min translation algorithm transforms hum dialect code to min dialect code by applying a series of syntactic transformations while preserving semantic structure.

#### 6.2.2 Algorithm Definition

**Algorithm:* `translate_hum_to_min`

**Input:* `code_hum: String` (valid hum dialect code)

**Output:* `code_min: String` (equivalent min dialect code)

**Mathematical Definition:*

$$
\text{translate\_hum\_to\_min}(\text{code}_{\text{hum}}) = \text{apply\_transformations}(\text{parse}(\text{code}_{\text{hum}}), \mathcal{T}_{\text{hum}\to\text{min}})
$$

**Pseudocode:*

```
function translate_hum_to_min(code_hum: String): String {
    // Parse hum code to AST
    ast = parse_hum(code_hum);
    
    // Apply transformations
    ast_min = transform_ast(ast, hum_to_min_rules);
    
    // Render AST to min code
    code_min = render_min(ast_min);
    
    return code_min;
}

function transform_ast(node: AST, rules: TransformationRules): AST {
    match node.type {
        case Function:
            return transform_function(node, rules);
        case If:
            return transform_if(node, rules);
        case Match:
            return transform_match(node, rules);
        case Let:
            return transform_let(node, rules);
        case Return:
            return transform_return(node, rules);
        case BinaryOp:
            return transform_binary_op(node, rules);
        case Call:
            return transform_call(node, rules);
        default:
            return node;
    }
}

function transform_function(node: AST, rules: TransformationRules): AST {
    // Replace 'function' with 'fn'
    node.keyword = 'fn';
    
    // Remove spaces around colons in parameters
    for param in node.parameters {
        param.type_annotation = remove_spaces(param.type_annotation);
    }
    
    // Replace ':' with '->'
    node.return_type_annotation = node.return_type_annotation.replace(':', '->');
    
    // Contract type names
    node.return_type = contract_type(node.return_type);
    for param in node.parameters {
        param.type = contract_type(param.type);
    }
    
    // Remove explicit return if redundant
    if is_explicit_return(node.body) {
        node.body = unwrap_return(node.body);
    }
    
    return node;
}

function transform_if(node: AST, rules: TransformationRules): AST {
    // Remove parentheses around condition
    node.condition = unwrap_parentheses(node.condition);
    
    // Remove semicolons from statements
    node.then_branch = remove_semicolons(node.then_branch);
    if node.else_branch exists {
        node.else_branch = remove_semicolons(node.else_branch);
    }
    
    return node;
}

function transform_match(node: AST, rules: TransformationRules): AST {
    // Replace 'match' with 'fix'
    node.keyword = 'fix';
    
    // Remove parentheses around expression
    node.expression = unwrap_parentheses(node.expression);
    
    // Remove 'case' from each arm
    for arm in node.arms {
        arm.pattern = remove_case_keyword(arm.pattern);
        arm.expression = remove_semicolon(arm.expression);
    }
    
    return node;
}

function transform_let(node: AST, rules: TransformationRules): AST {
    // Replace '=' with ':='
    node.operator = ':=';
    
    // Remove 'let' keyword
    node.keyword = '';
    
    // Remove semicolon
    node.semicolon = false;
    
    // Contract type if explicit
    if node.type_annotation exists {
        node.type = contract_type(node.type);
    }
    
    return node;
}

function transform_return(node: AST, rules: TransformationRules): AST {
    // Replace 'return' with 'ret'
    node.keyword = 'ret';
    
    // Remove semicolon
    node.semicolon = false;
    
    return node;
}

function transform_binary_op(node: AST, rules: TransformationRules): AST {
    // Remove spaces around operator
    node.operator = node.operator.trim();
    
    return node;
}

function contract_type(type: Type): Type {
    match type.name {
        case 'Int8': return Type('i8');
        case 'Int16': return Type('i16');
        case 'Int32': return Type('i32');
        case 'Int64': return Type('i64');
        case 'Float32': return Type('f32');
        case 'Float64': return Type('f64');
        case 'String': return Type('str');
        case 'Boolean': return Type('bool');
        case 'Void': return Type('void');
        default: return type;
    }
}
```

**Complexity:*
- **Time:* $O(n)$ where $n$ is the number of AST nodes
- **Space:* $O(n)$ for storing transformed AST

---

## 7. Correctness Properties

### 7.1 Invariants

#### 7.1.1 Semantic Equivalence Invariant

**INV-001:* Translation preserves semantic equivalence.

$$
\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{code} \equiv \mathcal{T}_{\text{min}\to\text{hum}}(\text{code})
$$

**Verification:* Compare execution results of original and translated code.

#### 7.1.2 Round-Trip Invariant

**INV-002:* Round-trip translation yields semantically equivalent code.

$$
\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{code} \equiv \mathcal{T}_{\text{hum}\to\text{min}}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))
$$

**Verification:* Test round-trip on all code samples.

#### 7.1.3 Type Preservation Invariant

**INV-003:* Translation preserves type information.

$$
\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{Type}(\text{code}) = \text{Type}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))
$$

**Verification:* Type check original and translated code.

#### 7.1.4 Information Preservation Invariant

**INV-004:* Translation never loses information.

$$
\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{Info}(\text{code}) = \text{Info}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))
$$

**Verification:* Compare AST structure before and after translation.

### 7.2 Theorems

#### 7.2.1 Semantic Equivalence Theorem

**Theorem 1:* Translation preserves semantic equivalence.

$$
\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{Semantics}(\text{code}) = \text{Semantics}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))
$$

**Proof:*

1. **Base Case:* For a single expression (e.g., `x + y`):
   - min: `x+y`
   - hum: `x + y`
   - Semantics: Binary addition of x and y
   - Both have identical semantics

2. **Inductive Step:* Assume translation preserves semantics for all expressions of size $< n$.
   - Consider expression of size $n$.
   - Expression is composed of subexpressions of size $< n$.
   - By induction hypothesis, subexpressions preserve semantics.
   - Translation only changes syntax, not structure.
   - Therefore, entire expression preserves semantics.

3. **Conclusion:* By induction, translation preserves semantics for all expressions. ∎

#### 7.2.2 Round-Trip Theorem

**Theorem 2:* Round-trip translation yields semantically equivalent code.

$$
\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{code} \equiv \mathcal{T}_{\text{hum}\to\text{min}}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))
$$

**Proof:*

1. **Keyword Reversibility:*
   - `fn` → `function` → `fn` (reversible)
   - `ret` → `return` → `ret` (reversible)
   - All keyword mappings are bijective

2. **Type Reversibility:*
   - `i32` → `Int32` → `i32` (reversible)
   - All type mappings are bijective

3. **Syntax Reversibility:*
   - `:=` → `let ... =` → `:=` (reversible)
   - `if cond{a}else{b}` → `if (cond) { a } else { b }` → `if cond{a}else{b}` (reversible)

4. **Composition:*
   - Each transformation step is reversible
   - Composition of reversible functions is reversible
   - Therefore, round-trip property holds

**Conclusion:* Round-trip property holds for all valid code. ∎

#### 7.2.3 Type Preservation Theorem

**Theorem 3:* Translation preserves type information.

$$
\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{Type}(\text{code}) = \text{Type}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))
$$

**Proof:*

1. **Type Mapping Preservation:*
   - Type mappings are bijective (e.g., `i32` ↔ `Int32`)
   - Type structure is preserved (generics, optionals, etc.)

2. **Type Annotation Preservation:*
   - Type annotations are translated, not removed
   - Type inference rules are identical in both dialects

3. **Conclusion:* Type information is preserved during translation. ∎

#### 7.2.4 Isomorphism Theorem

**Theorem 4:* min and hum dialects are isomorphic.

$$
\mathcal{L}_{\text{min}} \cong \mathcal{L}_{\text{hum}}
$$

**Proof:*

1. **Define Forward Mapping:* $f = \mathcal{T}_{\text{min}\to\text{hum}}$
   - $f: \mathcal{L}_{\text{min}} \to \mathcal{L}_{\text{hum}}$
   - $f$ is total (defined for all valid min code)
   - $f$ preserves semantics (Theorem 1)

2. **Define Inverse Mapping:* $f^{-1} = \mathcal{T}_{\text{hum}\to\text{min}}$
   - $f^{-1}: \mathcal{L}_{\text{hum}} \to \mathcal{L}_{\text{min}}$
   - $f^{-1}$ is total (defined for all valid hum code)
   - $f^{-1}$ preserves semantics (Theorem 1)

3. **Verify Composition:*
   - $\forall \text{code} \in \mathcal{L}_{\text{min}}, f^{-1}(f(\text{code})) = \text{code}$ (Theorem 2)
   - $\forall \text{code} \in \mathcal{L}_{\text{hum}}, f(f^{-1}(\text{code})) = \text{code}$ (Theorem 2)

4. **Verify Semantic Preservation:*
   - $\forall \text{code}_1, \text{code}_2 \in \mathcal{L}_{\text{min}}, \text{Semantics}(\text{code}_1) = \text{Semantics}(\text{code}_2) \iff \text{Semantics}(f(\text{code}_1)) = \text{Semantics}(f(\text{code}_2))$

**Conclusion:* $\mathcal{L}_{\text{min}} \cong \mathcal{L}_{\text{hum}}$. ∎

---

## 8. Examples

### 8.1 Complete Example: Factorial Function

#### 8.1.1 min Dialect

```morph
// factorial.min
fn factorial(n:i32):i32{
  if n<=1{1}else{n*factorial(n-1)}
}

fn main():Effect<(),IO>{
  result:=factorial(5);
  println(result)
}
```

#### 8.1.2 hum Dialect

```morph
// factorial.hum (transient projection)
function factorial(n: Int32): Int32 {
  if (n <= 1) {
    return 1;
  } else {
    return n * factorial(n - 1);
  }
}

function main(): Effect<(), IO> {
  let result = factorial(5);
  println(result);
}
```

#### 8.1.3 Translation Steps

**min → hum:*
1. `fn` → `function`
2. `i32` → `Int32`
3. `if n<=1{1}else{n*factorial(n-1)}` → `if (n <= 1) { return 1; } else { return n * factorial(n - 1); }`
4. `result:=factorial(5)` → `let result = factorial(5);`
5. `Effect<(),IO>` → `Effect<(), IO>` (no change)

### 8.2 Example: Pattern Matching

#### 8.2.1 min Dialect

```morph
fn maybeAdd(opt:Option<i32>):i32{
  fix opt{
    Some(v)=>v+1,
    None=>0
  }
}
```

#### 8.2.2 hum Dialect

```morph
function maybeAdd(opt: Option<Int32>): Int32 {
  match (opt) {
    case Some(v) => v + 1,
    case None => 0
  }
}
```

#### 8.2.3 Translation Steps

**min → hum:*
1. `fn` → `function`
2. `i32` → `Int32`
3. `fix opt{...}` → `match (opt) { ... }`
4. `Some(v)=>v+1` → `case Some(v) => v + 1,`
5. `None=>0` → `case None => 0`

### 8.3 Example: Generic Function

#### 8.3.1 min Dialect

```morph
fn id<T>(x:T):T{x}
```

#### 8.3.2 hum Dialect

```morph
function id<T>(x: T): T {
  return x;
}
```

#### 8.3.3 Translation Steps

**min → hum:*
1. `fn` → `function`
2. `:T` → `: T` (add space)
3. `->T` → `: T` (replace arrow with colon)
4. `{x}` → `{ return x; }` (wrap in return, add semicolon)

### 8.4 Example: Struct Definition

#### 8.4.1 min Dialect

```morph
type Point={x:i32,y:i32}
```

#### 8.4.2 hum Dialect

```morph
type Point = {
  x: Int32,
  y: Int32
};
```

#### 8.4.3 Translation Steps

**min → hum:*
1. `=` → ` =` (add space)
2. `{x:i32,y:i32}` → `{ x: Int32, y: Int32 }` (add spaces, expand types, add commas)

### 8.5 Example: Enum Definition

#### 8.5.1 min Dialect

```morph
type Option<T>=Some(T)|None
```

#### 8.5.2 hum Dialect

```morph
type Option<T> = Some(T) | None;
```

#### 8.5.3 Translation Steps

**min → hum:*
1. `=` → ` =` (add space)
2. `Some(T)|None` → `Some(T) | None` (add spaces around `|`)

### 8.6 Example: Complex Function

#### 8.6.1 min Dialect

```morph
fn process(data:List<i32>):i32{
  sum:=0;
  loop{
    fix data{
      []=>ret sum,
      [h,...t]=>{sum:=sum+h;data:=t}
    }
  }
}
```

#### 8.6.2 hum Dialect

```morph
function process(data: List<Int32>): Int32 {
  let sum = 0;
  loop {
    match (data) {
      case [] => return sum,
      case [head, ...tail] => {
        sum = sum + head;
        data = tail;
      }
    }
  }
}
```

#### 8.6.3 Translation Steps

**min → hum:*
1. `fn` → `function`
2. `i32` → `Int32`
3. `sum:=0` → `let sum = 0;`
4. `loop{...}` → `loop { ... }`
5. `fix data{...}` → `match (data) { ... }`
6. `[]=>ret sum` → `case [] => return sum,`
7. `[h,...t]=>{sum:=sum+h;data:=t}` → `case [head, ...tail] => { sum = sum + head; data = tail; }`

### 8.7 Edge Cases

#### 8.7.1 Empty Function

**min:*
```morph
fn empty():void{}
```

**hum:*
```morph
function empty(): Void {
}
```

#### 8.7.2 Nested Functions

**min:*
```morph
fn outer():i32{
  fn inner(x:i32):i32{x*2}
  inner(5)
}
```

**hum:*
```morph
function outer(): Int32 {
  function inner(x: Int32): Int32 {
    return x * 2;
  }
  return inner(5);
}
```

#### 8.7.3 Deeply Nested Expressions

**min:*
```morph
fn complex():i32{((a+b)*c)/(d-e)}
```

**hum:*
```morph
function complex(): Int32 {
  return ((a + b) * c) / (d - e);
}
```

---

## 9. Quality Attributes

### 9.1 Functional Suitability

**Definition:* The syntax translation system provides all required functionality for bidirectional translation between min and hum dialects.

**Requirements:*
- **SYN-REQ-001:* THE system SHALL provide bidirectional translation between min and hum dialects.
- **SYN-REQ-005:* THE system SHALL preserve semantic equivalence during translation.
- **SYN-REQ-006:* THE system SHALL satisfy the round-trip property.

**Metrics:*
| Metric | Measurement Method | Target | Threshold |
|---------|---------------------|--------|-----------|
| Dialect coverage | Count of supported language features | 100% | ≥ 95% |
| Semantic equivalence | Test suite pass rate | 100% | ≥ 99% |
| Round-trip success | Round-trip test pass rate | 100% | ≥ 99% |

**Verification:*
- **Method:* Test
- **Frequency:* Per Release

### 9.2 Performance Efficiency

**Definition:* The syntax translation system provides responsive translation with minimal overhead.

**Requirements:*
- **SYN-NFR-001:* THE system SHALL translate min to hum in O(n) time complexity.
- **SYN-NFR-002:* THE system SHALL translate hum to min in O(n) time complexity.

**Metrics:*
| Metric | Measurement Method | Target | Threshold |
|---------|---------------------|--------|-----------|
| Translation time (min→hum) | Benchmark (10,000 tokens) | < 100ms | < 200ms |
| Translation time (hum→min) | Benchmark (10,000 tokens) | < 100ms | < 200ms |
| Memory usage | Benchmark (10,000 tokens) | < 10MB | < 20MB |

**Verification:*
- **Method:* Performance Test
- **Frequency:* Per Release

### 9.3 Reliability

**Definition:* The syntax translation system maintains consistency and correctness across all operations.

**Requirements:*
- **SYN-NFR-004:* THE system SHALL guarantee 100% semantic equivalence.
- **SYN-NFR-005:* THE system SHALL never lose information during translation.

**Metrics:*
| Metric | Measurement Method | Target | Threshold |
|---------|---------------------|--------|-----------|
| Semantic equivalence | Test suite pass rate | 100% | ≥ 99.9% |
| Information loss | Count of loss events | 0 | 0 |

**Verification:*
- **Method:* Test
- **Frequency:* Continuous

### 9.4 Maintainability

**Definition:* The syntax translation system is extensible and easy to maintain.

**Requirements:*
- **SYN-NFR-006:* THE system SHALL allow addition of new language constructs.

**Metrics:*
| Metric | Measurement Method | Target | Threshold |
|---------|---------------------|--------|-----------|
| Construct addition effort | Time to add new construct | < 1 day | < 2 days |
| Code coverage | Test coverage percentage | ≥ 90% | ≥ 80% |

**Verification:*
- **Method:* Analysis
- **Frequency:* Per Release

---

## 10. Change Log

| Version | Date       | Author      | Changes                                                                 |
|---------|------------|-------------|-------------------------------------------------------------------------|
| 1.0.0   | 2026-01-02 | Language Design Team | Initial version - defines syntax translation between min and hum dialects |

---

## Appendix A: Complete Translation Reference

### A.1 Keyword Translation

| min | hum | Context |
|------|-------|---------|
| `fn` | `function` | Function declaration |
| `ret` | `return` | Return statement |
| `use` | `import` | Import statement |
| `act` | `actor` | Actor declaration |
| `fix` | `match` | Pattern matching |
| `if` | `if` | Conditional |
| `else` | `else` | Conditional alternative |
| `loop` | `loop` | Loop |
| `defer` | `defer` | Deferred execution |
| `const` | `const` | Constant |
| `type` | `type` | Type definition |
| `in` | `in` | Membership test |
| `is` | `is` | Type test |
| `as` | `as` | Type cast |

### A.2 Type Translation

| min | hum | Category |
|------|-------|----------|
| `i8` | `Int8` | Signed 8-bit integer |
| `i16` | `Int16` | Signed 16-bit integer |
| `i32` | `Int32` | Signed 32-bit integer |
| `i64` | `Int64` | Signed 64-bit integer |
| `f32` | `Float32` | 32-bit floating point |
| `f64` | `Float64` | 64-bit floating point |
| `str` | `String` | String |
| `bool` | `Boolean` | Boolean |
| `void` | `Void` | Unit type |

### A.3 Operator Translation

| min | hum | Description |
|------|-------|-------------|
| `:=` | `let ... =` | Variable declaration |
| `->` | `:` | Return type annotation |
| `|>` | `|>` | Pipe operator |
| `??` | `??` | Null coalescing |
| `?` | `?` | Null propagation |
| `^` | `^` | Isolated type |
| `#` | `#` | Value type |
| `&` | `&` | Reference type |

### A.4 Statement Translation

| min Pattern | hum Pattern | Example |
|-------------|--------------|---------|
| `x:=expr` | `let x = expr;` | Variable declaration |
| `ret expr` | `return expr;` | Return statement |
| `if cond{a}else{b}` | `if (cond) { a; } else { b; }` | If-else |
| `fix expr{p=>a}` | `match (expr) { case p => a }` | Pattern match |
| `loop{body}` | `loop { body; }` | Loop |

---

## Appendix B: Proof Sketches

### B.1 Proof of Theorem 1: Semantic Equivalence

**Claim:* $\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{Semantics}(\text{code}) = \text{Semantics}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))$

**Proof:*

1. **Lexical Preservation:*
   - All tokens are preserved during translation
   - Only whitespace and keyword names change
   - Token sequence remains identical

2. **Syntactic Preservation:*
   - AST structure is preserved
   - Node types remain identical
   - Node relationships remain identical

3. **Semantic Preservation:*
   - Control flow is preserved (if, loop, match)
   - Data flow is preserved (expressions, assignments)
   - Type information is preserved (types, generics)

4. **Conclusion:* Since lexical, syntactic, and semantic structure are preserved, semantics are preserved. ∎

### B.2 Proof of Theorem 2: Round-Trip Property

**Claim:* $\forall \text{code} \in \mathcal{L}_{\text{min}}, \text{code} \equiv \mathcal{T}_{\text{hum}\to\text{min}}(\mathcal{T}_{\text{min}\to\text{hum}}(\text{code}))$

**Proof:*

1. **Keyword Round-Trip:*
   - `fn` → `function` → `fn`
   - `ret` → `return` → `ret`
   - All keywords round-trip correctly

2. **Type Round-Trip:*
   - `i32` → `Int32` → `i32`
   - All types round-trip correctly

3. **Syntax Round-Trip:*
   - `:=` → `let ... =` → `:=`
   - `if cond{a}` → `if (cond) { a; }` → `if cond{a}`
   - All syntax round-trips correctly

4. **Conclusion:* All translation rules are reversible, therefore round-trip property holds. ∎

### B.3 Proof of Theorem 4: Isomorphism

**Claim:* $\mathcal{L}_{\text{min}} \cong \mathcal{L}_{\text{hum}}$

**Proof:*

1. **Existence of Forward Mapping:* $f = \mathcal{T}_{\text{min}\to\text{hum}}$
   - $f$ is total: defined for all valid min code
   - $f$ is injective: different min code maps to different hum code
   - $f$ preserves semantics (Theorem 1)

2. **Existence of Inverse Mapping:* $f^{-1} = \mathcal{T}_{\text{hum}\to\text{min}}$
   - $f^{-1}$ is total: defined for all valid hum code
   - $f^{-1}$ is injective: different hum code maps to different min code
   - $f^{-1}$ preserves semantics (Theorem 1)

3. **Composition Property:*
   - $f^{-1} \circ f = \text{id}_{\mathcal{L}_{\text{min}}}$ (Theorem 2)
   - $f \circ f^{-1} = \text{id}_{\mathcal{L}_{\text{hum}}}$ (Theorem 2)

4. **Semantic Preservation:*
   - $\forall \text{code}_1, \text{code}_2 \in \mathcal{L}_{\text{min}}, \text{Semantics}(\text{code}_1) = \text{Semantics}(\text{code}_2) \iff \text{Semantics}(f(\text{code}_1)) = \text{Semantics}(f(\text{code}_2))$

**Conclusion:* $\mathcal{L}_{\text{min}} \cong \mathcal{L}_{\text{hum}}$. ∎

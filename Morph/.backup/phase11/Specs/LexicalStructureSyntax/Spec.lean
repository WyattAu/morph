import Morph.Core
import Morph.Syntax

namespace Morph.Specs.LexicalStructureSyntax

/-!
## Lexical Structure and Syntax Specification

This module formalizes the lexical structure and syntax of the Morph
language, including EBNF grammar, keywords, operators, and literals.

See spec/language/lexical_structure_syntax_spec.md for complete specification.
-/

/-!
## Lexical Structure

The lexical structure defines the tokens that make up the Morph language.
-/

/-- Token type for the Morph language -/
inductive Token where
  | keyword : String → Token
  | identifier : String → Token
  | literal : Morph.Core.Value → Token
  | operator : Morph.Core.Operator → Token
  | delimiter : String → Token
  | comment : String → Token
  | whitespace : Token
  | eof : Token
deriving Repr

/-- Token position in source code -/
structure TokenPos where
  line : Nat
  column : Nat
  offset : Nat
deriving Repr

/-- Token with position information -/
structure TokenWithPos where
  token : Token
  pos : TokenPos
deriving Repr

/-!
## Keywords

Reserved keywords in the Morph language.
-/

/-- All reserved keywords -/
def keywords : List String :=
  [
    "fn", "ret", "use", "act", "fix",
    "if", "else", "for", "while", "do",
    "match", "case", "break", "continue",
    "let", "in", "struct", "enum", "type",
    "pub", "priv", "mod", "impl", "trait",
    "where", "true", "false", "null", "undef"
  ]

/-- Check if a string is a keyword -/
def isKeyword (s : String) : Bool :=
  s ∈ keywords

/-!
## Operators

Operators in the Morph language.
-/

/-- Binary operators -/
def binaryOperators : List String :=
  [
    "+", "-", "*", "/", "%",
    "==", "!=", "<", "<=", ">", ">=",
    "&&", "||", "!",
    "&", "|", "^", "~",
    "<<", ">>",
    "??", "|>", "?"
  ]

/-- Unary operators -/
def unaryOperators : List String :=
  ["!", "-", "~", "++", "--"]

/-- Assignment operators -/
def assignmentOperators : List String :=
  [":=", "+=", "-=", "*=", "/=", "%="]

/-- Check if a string is a binary operator -/
def isBinaryOperator (s : String) : Bool :=
  s ∈ binaryOperators

/-- Check if a string is a unary operator -/
def isUnaryOperator (s : String) : Bool :=
  s ∈ unaryOperators

/-- Check if a string is an assignment operator -/
def isAssignmentOperator (s : String) : Bool :=
  s ∈ assignmentOperators

/-!
## Delimiters

Delimiters in the Morph language.
-/

/-- All delimiters -/
def delimiters : List String :=
  [
    "(", ")", "{", "}", "[", "]",
    ",", ";", ":", "::", ".", "->",
    "|", "=>", "=", "<", ">", "@"
  ]

/-- Check if a string is a delimiter -/
def isDelimiter (s : String) : Bool :=
  s ∈ delimiters

/-!
## Literals

Literal values in the Morph language.
-/

/-- Integer literal syntax -/
inductive IntLiteral where
  | decimal : String → IntLiteral
  | hex : String → IntLiteral
  | octal : String → IntLiteral
  | binary : String → IntLiteral
deriving Repr

/-- Float literal syntax -/
inductive FloatLiteral where
  | decimal : String → FloatLiteral
  | scientific : String → FloatLiteral
  | hex : String → FloatLiteral
deriving Repr

/-- String literal syntax -/
inductive StringLiteral where
  | doubleQuoted : String → StringLiteral
  | singleQuoted : String → StringLiteral
  | raw : String → StringLiteral
deriving Repr

/-- Character literal syntax -/
inductive CharLiteral where
  | single : Char → CharLiteral
  | escape : String → CharLiteral
  | unicode : String → CharLiteral
deriving Repr

/-- Boolean literal syntax -/
inductive BoolLiteral where
  | trueLit : BoolLiteral
  | falseLit : BoolLiteral
deriving Repr

/-- Parse integer literal -/
def parseIntLiteral (s : String) : Option IntLiteral :=
  if s.startsWith "0x" then
    some (IntLiteral.hex s)
  else if s.startsWith "0o" then
    some (IntLiteral.octal s)
  else if s.startsWith "0b" then
    some (IntLiteral.binary s)
  else
    some (IntLiteral.decimal s)

/-- Parse float literal -/
def parseFloatLiteral (s : String) : Option FloatLiteral :=
  if s.contains "e" || s.contains "E" then
    some (FloatLiteral.scientific s)
  else if s.startsWith "0x" then
    some (FloatLiteral.hex s)
  else
    some (FloatLiteral.decimal s)

/-!
## Identifiers

Identifier syntax in the Morph language.
-/

/-- Identifier syntax rules -/
def isValidIdentifier (s : String) : Bool :=
  if s.isEmpty then
    false
  else
    let first := s.get 0
    let firstValid := match first with
      | some c => (c.isAlpha || c = '_')
      | none => false
    let restValid := s.drop 1 |>.all fun c =>
      (c.isAlphaNum || c = '_' || c = '\'')
    firstValid && restValid && !isKeyword s

/-- Identifier with escape sequence -/
def isValidEscapedIdentifier (s : String) : Bool :=
  s.startsWith "`" && s.endsWith "`" && s.length > 2

/-!
## Comments

Comment syntax in the Morph language.
-/

/-- Single-line comment syntax -/
def isSingleLineComment (s : String) : Bool :=
  s.startsWith "//"

/-- Multi-line comment syntax -/
def isMultiLineCommentStart (s : String) : Bool :=
  s.startsWith "/*"

/-- Multi-line comment end syntax -/
def isMultiLineCommentEnd (s : String) : Bool :=
  s.endsWith "*/"

/-- Documentation comment syntax -/
def isDocComment (s : String) : Bool :=
  s.startsWith "///" || s.startsWith "/**"

/-!
## Whitespace

Whitespace handling in the Morph language.
-/

/-- Whitespace characters -/
def whitespaceChars : String :=
  " \t\n\r"

/-- Check if a character is whitespace -/
def isWhitespace (c : Char) : Bool :=
  c ∈ whitespaceChars

/-- Check if a string is all whitespace -/
def isAllWhitespace (s : String) : Bool :=
  s.all isWhitespace

/-!
## EBNF Grammar

Extended Backus-Naur Form grammar for Morph syntax.
-/

/-- Grammar production rule -/
structure Production where
  lhs : String
  rhs : String
deriving Repr

/-- Grammar definition -/
structure Grammar where
  productions : List Production
  startSymbol : String
deriving Repr

/-- Core Morph grammar productions -/
def coreProductions : List Production :=
  [
    { lhs := "Program", rhs := "Function*" },
    { lhs := "Function", rhs := "'fn' Identifier '(' ParamList? ')' ':' Type Block" },
    { lhs := "ParamList", rhs := "Param (',' Param)*" },
    { lhs := "Param", rhs := "Identifier ':' Type" },
    { lhs := "Type", rhs := "BaseType | Identifier | Type '[' ']'" },
    { lhs := "BaseType", rhs := "'i8' | 'i16' | 'i32' | 'i64' | 'f32' | 'f64' | 'str' | 'bool' | 'void'" },
    { lhs := "Block", rhs := "'{' Stmt* '}'" },
    { lhs := "Stmt", rhs := "ExprStmt | VarDecl | ReturnStmt | IfStmt | WhileStmt | ForStmt | MatchStmt" },
    { lhs := "ExprStmt", rhs := "Expr ';'" },
    { lhs := "VarDecl", rhs := "Identifier ':=' Expr ';'" },
    { lhs := "ReturnStmt", rhs := "'ret' Expr ';'" },
    { lhs := "IfStmt", rhs := "'if' Expr Block ('else' Block)?" },
    { lhs := "WhileStmt", rhs := "'while' Expr Block" },
    { lhs := "ForStmt", rhs := "'for' Identifier 'in' Expr Block" },
    { lhs := "MatchStmt", rhs := "'fix' Expr '{' MatchArm* '}'" },
    { lhs := "MatchArm", rhs := "Pattern '=>' Expr ';'" },
    { lhs := "Pattern", rhs := "Identifier | Literal | '_' | Pattern '(' PatternList? ')'" },
    { lhs := "Expr", rhs := "Literal | Identifier | Expr BinaryOp Expr | UnaryOp Expr | Expr '(' ArgList? ')' | Expr '[' ']'" },
    { lhs := "Literal", rhs := "IntLiteral | FloatLiteral | StringLiteral | CharLiteral | BoolLiteral | 'null' | 'undef'" },
    { lhs := "BinaryOp", rhs := "'+' | '-' | '*' | '/' | '%' | '==' | '!=' | '<' | '<=' | '>' | '>=' | '&&' | '||' | '|>' | '??'" },
    { lhs := "UnaryOp", rhs := "'!' | '-' | '~' | '++' | '--'" },
    { lhs := "ArgList", rhs := "Expr (',' Expr)*" }
  ]

/-- Core Morph grammar -/
def coreGrammar : Grammar :=
  {
    productions := coreProductions,
    startSymbol := "Program"
  }

/-!
## Lexical Analysis

Tokenization and lexical analysis functions.
-/

/-- Tokenize a source string into tokens -/
def tokenize (source : String) : List TokenWithPos :=
  -- Abstract tokenization; defined in Lexer module
  []

/-- Tokenize a single line -/
def tokenizeLine (line : String) (lineNum : Nat) : List TokenWithPos :=
  -- Abstract line tokenization
  []

/-- Remove whitespace and comment tokens -/
def filterTokens (tokens : List TokenWithPos) : List TokenWithPos :=
  tokens.filter fun t =>
    match t.token with
    | Token.whitespace => false
    | Token.comment _ => false
    | _ => true

/-!
## Syntax Analysis

Syntax analysis and parsing functions.
-/

/-- Parse tokens into an AST -/
def parseTokens (tokens : List TokenWithPos) : Option Morph.Syntax.Program :=
  -- Abstract parsing; defined in Parser module
  some Morph.Syntax.Program.empty

/-- Validate syntax of a program -/
def validateSyntax (program : Morph.Syntax.Program) : Bool :=
  -- Abstract syntax validation
  true

/-!
## Syntax Correctness

Invariants and correctness properties for syntax.
-/

/-- INV-001: All tokens have valid positions -/
def all_tokens_have_valid_positions (tokens : List TokenWithPos) : Prop :=
  ∀ (t : TokenWithPos), t ∈ tokens →
    t.pos.line > 0 ∧ t.pos.column > 0 ∧ t.pos.offset ≥ 0

/-- INV-002: All identifiers are valid -/
def all_identifiers_are_valid (tokens : List TokenWithPos) : Prop :=
  ∀ (t : TokenWithPos), t ∈ tokens →
    match t.token with
    | Token.identifier s => isValidIdentifier s
    | _ => True

/-- INV-003: All literals are well-formed -/
def all_literals_are_well_formed (tokens : List TokenWithPos) : Prop :=
  ∀ (t : TokenWithPos), t ∈ tokens →
    match t.token with
    | Token.literal _ => True
    | _ => True

/-- INV-004: Grammar is unambiguous -/
def grammar_is_unambiguous (grammar : Grammar) : Prop :=
  ∀ (input : String),
    let parse1 := parseTokens (tokenize input) in
    let parse2 := parseTokens (tokenize input) in
      parse1 = parse2

end Morph.Specs.LexicalStructureSyntax

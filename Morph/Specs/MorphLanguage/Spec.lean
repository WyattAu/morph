/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Frontend.Parser

/-!
# Specification: Morph Language

**Source:** `spec/language/morph_language_spec.md`
**Status:** Complete
**Last Updated:** 2026-10-25
**Verified By:** Loop 46

## Overview

This specification formalizes the Morph language specification: the edit
operations, the parser adapter, the dialect predicates, error handling and the
type/effect vocabulary.

## Known Issues

- The *projectional-only mandate* is false as originally stated ("every source
  string parses"). Loop 46 replaced the parsing stub with the shipped total
  frontend parser and recorded the refutation
  (`projectionalOnlyMandate_refuted`). What a projectional editor actually
  guarantees is that accepted edits go through the AST.
- The frontend parser accepts expressions, not full statement syntax: `"1 + 2"`
  parses, `"let x = 5"` does not. That gap lives in
  `Morph/Frontend/Parser.lean`.

-/

namespace Morph.Specs.MorphLanguage

open Morph.Core Morph.Syntax

/-!
## Edits and Parsing
-/

inductive EditOperation where
  | replace : String → EditOperation
  | insert : String → EditOperation
  | delete : EditOperation
  | move : Nat → Nat → EditOperation
  deriving Repr, BEq

/-- Join a list of strings with a separator. -/
def joinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: y :: rest => x ++ sep ++ joinSep sep (y :: rest)

/-- Parse source text with the shipped frontend parser, wrapping the expression
    as a one-statement program.

    This used to be `if code.isEmpty then some .empty else some .empty`: it
    parsed nothing and could not fail. It now delegates to
    `Morph.Frontend.parse`, so malformed input yields `none`. -/
def parseCode (code : String) : Option Morph.Syntax.Program :=
  match Morph.Frontend.parse code with
  | .ok e => some { stmts := [.exprStmt e] }
  | .error _ => none

def applyEdit (code : String) (edit : EditOperation) : String :=
  match edit with
  | EditOperation.replace newCode => newCode
  | EditOperation.insert newCode => code ++ newCode
  | EditOperation.delete => ""
  | EditOperation.move _ _ => code

/-- Move the statement at index `i` to position `j`. Out-of-range `i` leaves the
    program unchanged; `j` past the end appends. -/
def moveStmt (i j : Nat) (xs : List Stmt) : List Stmt :=
  match xs[i]? with
  | none => xs
  | some x =>
    let rest := xs.eraseIdx i
    rest.take j ++ x :: rest.drop j

/-- Apply an edit at the AST level.

    - `replace s` re-parses `s` and replaces the whole program (fails on
      malformed input);
    - `insert s` re-parses `s` and appends its statements;
    - `delete` empties the program;
    - `move i j` reorders statements.

    This used to ignore its edit entirely (`fun _ _ => some ast`). -/
def applyEditToAst (ast : Morph.Syntax.Program)
    (edit : EditOperation) : Option Morph.Syntax.Program :=
  match edit with
  | EditOperation.replace s => parseCode s
  | EditOperation.insert s =>
    (parseCode s).map (fun p => { stmts := ast.stmts ++ p.stmts })
  | EditOperation.delete => some Morph.Syntax.Program.empty
  | EditOperation.move i j => some { stmts := moveStmt i j ast.stmts }

/-!
## Projectional Only Mandate
-/

/-- Every source string parses.

    As stated this is **false** for a real parser; loop 46 refutes it with the
    witness `"("` (`projectionalOnlyMandate_refuted`). What a projectional
    editor actually guarantees is that edits go through the AST
    (`applyEditToAst`), not that arbitrary text parses. -/
def projectionalOnlyMandate : Prop :=
  ∀ (code : String), (parseCode code).isSome = true

/-- The name of a surface identifier. -/
def idStr (i : Id) : String := i.name

/-- Surface syntax of an operator. -/
def opStr : Operator → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .neq => "!=" | .lt => "<" | .leq => "<=" | .gt => ">" | .geq => ">="
  | .and => "&&" | .or => "||" | .not => "!"
  | .andb => "&" | .orb => "|" | .xorb => "^" | .notb => "~"
  | .shl => "<<" | .shr => ">>"
  | .ptrAdd => "+p" | .ptrSub => "-p" | .ptrLoad => "*p" | .ptrStore => "=p"

def capStr : Capability → String
  | .iso => "iso" | .val => "val" | .ref => "ref"

def intWidthStr : IntWidth → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"

def floatWidthStr : FloatWidth → String
  | .f32 => "f32" | .f64 => "f64"

/-! Surface syntax of a type. The list helpers are separate structural
    recursions because `List.map` defeats termination inference (the same
    higher-order obstacle the parser hit in loop 39). -/
mutual
def typStr : Typ → String
  | .intType => "int" | .boolType => "bool" | .stringType => "string"
  | .pointerType => "pointer" | .unitType => "unit"
  | .arrayType t n => "[" ++ typStr t ++ "; " ++ toString n ++ "]"
  | .functionType ps r => "fn(" ++ typListStr ps ++ ") -> " ++ typStr r
  | .linearFunctionType ps r =>
    "linear fn(" ++ typListStr ps ++ ") -> " ++ typStr r
  | .intWidthType w => intWidthStr w
  | .floatType w => floatWidthStr w
  | .neverType => "never"
  | .refType c t => capStr c ++ " ref " ++ typStr t
  | .typeVar n => "'" ++ toString n
  | .optionType t => "option " ++ typStr t
  | .resultType a b => "result " ++ typStr a ++ " " ++ typStr b
  | .tupleType ts => "(" ++ typListStr ts ++ ")"
  | .structType name fs => "struct " ++ name ++ " { " ++ fieldListStr fs ++ " }"

def typListStr : List Typ → String
  | [] => ""
  | [t] => typStr t
  | t :: u :: rest => typStr t ++ ", " ++ typListStr (u :: rest)

def fieldListStr : List (String × Typ) → String
  | [] => ""
  | [(n, t)] => n ++ ": " ++ typStr t
  | (n, t) :: (u, v) :: rest =>
    n ++ ": " ++ typStr t ++ ", " ++ fieldListStr ((u, v) :: rest)
end

/-! Surface syntax of a value. -/
mutual
def valueStr : Value → String
  | .int n => toString n
  | .bool b => if b then "true" else "false"
  | .string str => "\"" ++ str ++ "\""
  | .pointer ptr => "ptr(" ++ toString ptr.block.id ++ ")"
  | .float f => toString f
  | .unit => "()"
  | .undef => "undef"
  | .some v => "some " ++ valueStr v
  | .none => "none"
  | .ok v => "ok " ++ valueStr v
  | .err v => "err " ++ valueStr v
  | .tuple_ vs => "(" ++ valueListStr vs ++ ")"
  | .array_ vs => "[" ++ valueListStr vs ++ "]"
  | .loc n => "loc(" ++ toString n ++ ")"
  | .closure f n => "closure(" ++ f ++ ", " ++ toString n ++ ")"

def valueListStr : List Value → String
  | [] => ""
  | [v] => valueStr v
  | v :: w :: rest => valueStr v ++ ", " ++ valueListStr (w :: rest)
end

/-! Render an expression. Binary and unary forms are parenthesised so the
    output re-associates the way the tree does; `spaced` is the `hum` dialect
    (whitespace around binary operators), `false` is `min` (compact). -/
mutual
def exprStr (spaced : Bool) : Expr → String
  | .bvar n => "#" ++ toString n
  | .fvar name => name
  | .lit v => valueStr v
  | .unop op e => "(" ++ opStr op ++ exprStr spaced e ++ ")"
  | .binop op a b =>
    "(" ++ exprStr spaced a ++ (if spaced then " " else "") ++ opStr op ++
      (if spaced then " " else "") ++ exprStr spaced b ++ ")"
  | .app f args => exprStr spaced f ++ "(" ++ exprListStr spaced ", " args ++ ")"
  | .lam n body => "fn " ++ toString n ++ " -> " ++ exprStr spaced body
  | .let_ init body =>
    "let " ++ exprStr spaced init ++ " in " ++ exprStr spaced body
  | .ifThenElse c t f =>
    "if " ++ exprStr spaced c ++ " then " ++ exprStr spaced t ++
      " else " ++ exprStr spaced f
  | .forLoop s e body =>
    "for " ++ exprStr spaced s ++ " in " ++ exprStr spaced e ++ " { " ++
      exprListStr spaced "; " body ++ " }"
  | .block es => "{ " ++ exprListStr spaced "; " es ++ " }"
  | .match_ scrut arms =>
    "match " ++ exprStr spaced scrut ++ " { " ++ armListStr spaced arms ++ " }"
  | .field_ e name => exprStr spaced e ++ "." ++ name
  | .pipe e f => exprStr spaced e ++ " |> " ++ exprStr spaced f
  | .typeAsc e t => exprStr spaced e ++ ": " ++ typStr t
  | .some_ e => "some " ++ exprStr spaced e
  | .none_ => "none"
  | .ok_ e => "ok " ++ exprStr spaced e
  | .err_ e => "err " ++ exprStr spaced e
  | .nullCoalesce a b => exprStr spaced a ++ " ?? " ++ exprStr spaced b
  | .tuple_ es => "(" ++ exprListStr spaced ", " es ++ ")"
  | .arrayLit es => "[" ++ exprListStr spaced ", " es ++ "]"
  | .arrayIndex a i => exprStr spaced a ++ "[" ++ exprStr spaced i ++ "]"
  | .refCreate e c t =>
    "ref " ++ capStr c ++ " " ++ typStr t ++ " " ++ exprStr spaced e
  | .refLoad e => "*" ++ exprStr spaced e
  | .refStore r v t =>
    exprStr spaced r ++ " = " ++ exprStr spaced v ++ ": " ++ typStr t
  | .refFree e => "free " ++ exprStr spaced e
  | .refCast e c => "cast " ++ capStr c ++ " " ++ exprStr spaced e

def exprListStr (spaced : Bool) (sep : String) : List Expr → String
  | [] => ""
  | [e] => exprStr spaced e
  | e :: f :: rest => exprStr spaced e ++ sep ++ exprListStr spaced sep (f :: rest)

/-- Render a pattern; non-atomic subpatterns parenthesise. -/
def patStr : Pattern → String
  | .wild => "_"
  | .var_ x => x
  | .lit_ l => valueStr l
  | .none_ => "none"
  | .some_ p => "some " ++ patStrAtom p
  | .ok_ p => "ok " ++ patStrAtom p
  | .err_ p => "err " ++ patStrAtom p

def patStrAtom : Pattern → String
  | .wild => "_"
  | .var_ x => x
  | .lit_ l => valueStr l
  | .none_ => "none"
  | p => "(" ++ patStr p ++ ")"

def armListStr (spaced : Bool) : List (Pattern × Expr) → String
  | [] => ""
  | [(pat, body)] => patStr pat ++ " => " ++ exprStr spaced body
  | (pat, body) :: rest@(_ :: _) =>
    patStr pat ++ " => " ++ exprStr spaced body ++ " | " ++ armListStr spaced rest
end

/-! Render a statement. -/
mutual
def stmtStr (spaced : Bool) : Stmt → String
  -- Declarations print in surface syntax (loop 90): the parser's statement
  -- `let` takes no annotation (it elaborates to a placeholder type), so
  -- printing `": " ++ typStr` produced code that does not reparse and
  -- `morph fmt` could not round-trip. The annotation stays in the AST.
  | .exprStmt e => exprStr spaced e
  | .varDecl name _ e =>
    "let " ++ idStr name ++ " = " ++ exprStr spaced e
  | .assign name e => idStr name ++ " = " ++ exprStr spaced e
  | .returnStmt e => "return " ++ exprStr spaced e
  | .break => "break"
  | .continue => "continue"
  | .whileLoop c body =>
    "while " ++ exprStr spaced c ++ " { " ++ stmtListStr spaced body ++ " }"
  | .doWhile c body =>
    "do { " ++ stmtListStr spaced body ++ " } while " ++ exprStr spaced c
  | .ifStmt c th el =>
    "if " ++ exprStr spaced c ++ " { " ++ stmtListStr spaced th ++ " }" ++
      match el with
      | [] => ""
      | _ => " else { " ++ stmtListStr spaced el ++ " }"
  -- loop 78d: the statement form inverts without parens around the scrutinee
  -- (the expression form needs them so the scrutinee stops before `{`).
  | .matchStmt scrut arms =>
    "match " ++ exprStr spaced scrut ++ " { " ++ stmtArmListStr spaced arms ++ " }"
  | .nop => ""

def stmtListStr (spaced : Bool) : List Stmt → String
  | [] => ""
  | [s] => stmtStr spaced s
  | s :: t :: rest => stmtStr spaced s ++ "; " ++ stmtListStr spaced (t :: rest)

/-- Render statement-match arms (loop 78d): `case` introducer, `;`-joined
statement bodies. -/
def stmtArmListStr (spaced : Bool) : List (Pattern × List Stmt) → String
  | [] => ""
  | (pat, body) :: rest =>
    "case " ++ patStr pat ++ " => " ++ stmtListStr spaced body ++
      match rest with
      | [] => ""
      | _ :: _ => " | " ++ stmtArmListStr spaced rest
end

/-!
## Dual Dialects
-/

inductive Dialect where
  | min : Dialect
  | hum : Dialect
  deriving Repr, BEq, DecidableEq

def isCanonicalDialect (d : Dialect) : Bool :=
  decide (d = Dialect.min)

def isTransientDialect (d : Dialect) : Bool :=
  decide (d = Dialect.hum)

/-- Render a program in a dialect. `min` is compact (`;` separators), `hum` is
    the human-readable form (`;\n`, spaces around binary operators). This used
    to return `""` for every program. -/
def renderCode (ast : Morph.Syntax.Program) (dialect : Dialect) : String :=
  let spaced := dialect == Dialect.hum
  joinSep (if spaced then ";\n" else ";") (ast.stmts.map (stmtStr spaced))

/-!
## Error Handling
-/

inductive Error where
  | syntaxError : String → Error
  | typeError : String → Error
  | runtimeError : String → Error
  | ioError : String → Error
  | moduleError : String → Error
  | effectError : String → Error
  deriving Repr, BEq

structure ErrorWithLocation where
  error : Error
  line : Nat
  column : Nat
  file : String
  deriving Repr

inductive ErrorResult (α : Type) where
  | ok : α → ErrorResult α
  | error : ErrorWithLocation → ErrorResult α
  deriving Repr

/-!
## Effect System
-/

inductive Effect where
  | pure : Effect
  | io : Effect
  | state : Effect
  | async : Effect
  | exception : Effect
  deriving Repr, BEq

/-!
## Type System
-/

inductive Variance where
  | covariant : Variance
  | contravariant : Variance
  | invariant : Variance
  deriving Repr, BEq

structure TypeParameter where
  name : String
  variance : Variance
  deriving Repr

/-!
## Pattern Matching
-/

inductive Pattern where
  | wildcard : Pattern
  | identifier : String → Pattern
  | constructor : String → List Pattern → Pattern
  | tuple : List Pattern → Pattern
  | record : List (String × Pattern) → Pattern
  deriving Repr

structure PatternGuard where
  condition : Morph.Syntax.Expr
  pattern : Pattern
  deriving Repr

structure MatchArm where
  pattern : Pattern
  guard : Option PatternGuard
  body : Morph.Syntax.Expr
  deriving Repr

/-!
## Control Flow
-/

inductive ControlFlow where
  | ifThenElse : Morph.Syntax.Expr → Morph.Syntax.Expr → Morph.Syntax.Expr → ControlFlow
  | loop : String → Morph.Syntax.Expr → Morph.Syntax.Expr → ControlFlow
  | matchExpr : Morph.Syntax.Expr → List MatchArm → ControlFlow
  deriving Repr

/-!
## Operator Precedence
-/

inductive Associativity where
  | left : Associativity
  | right : Associativity
  | none : Associativity
  deriving Repr, BEq

structure Precedence where
  level : Nat
  associativity : Associativity
  deriving Repr

/-!
## Correctness Properties
-/

/-- **Projectional-only mandate**: every edit of a parsed program yields a
parsed program. (This was `True`.) -/
def projectional_only_mandate : Prop :=
  ∀ (ast : Morph.Syntax.Program) (edit : EditOperation),
    (applyEditToAst ast edit).isSome = true

/-- **`min` is the canonical dialect**. (This was `True`.) -/
def min_is_canonical : Prop :=
  isCanonicalDialect Dialect.min = true

/-- **`hum` is the transient dialect**. (This was `True`.) -/
def hum_is_transient : Prop :=
  isTransientDialect Dialect.hum = true

/-- **Error handling is explicit**: every result is either a success or an
error carrying a location. (This was `True`.) -/
def error_handling_explicit : Prop :=
  ∀ {α : Type} (r : ErrorResult α),
    (∃ a, r = ErrorResult.ok a) ∨
      ∃ e, r = ErrorResult.error e

end Morph.Specs.MorphLanguage

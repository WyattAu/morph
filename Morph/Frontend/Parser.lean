import Morph.Frontend.Lexer
import Morph.Syntax

namespace Morph.Frontend

open Morph.Core
open Morph.Syntax

structure ParseError where
  message : String
  line : Nat
  col : Nat
  deriving Repr

inductive ParseResult where
  | ok : Expr → ParseResult
  | error : List ParseError → ParseResult
  deriving Repr

structure Parser where
  tokens : List Token
  pos : Nat
  deriving Repr

namespace Parser

def peek (p : Parser) : Option Token :=
  (p.tokens.drop p.pos).head?

def advance (p : Parser) : Parser :=
  { p with pos := p.pos + 1 }

def atEnd (p : Parser) : Bool :=
  p.pos >= p.tokens.length

def expect (tk : TokenKind) (p : Parser) : Option Parser :=
  match peek p with
  | some t => if t.kind == tk then some (advance p) else none
  | none => none

def matchKeyword (kw : String) (p : Parser) : Option Parser :=
  expect (.keyword kw) p

def parseIdentifier (p : Parser) : Option (Expr × Parser) :=
  match peek p with
  | some t =>
    match t.kind with
    | .identifier => some (.var ⟨t.lexeme⟩, advance p)
    | _ => none
  | none => none

def parseLiteral (p : Parser) : Option (Expr × Parser) :=
  match peek p with
  | some t =>
    match t.kind with
    | .intLiteral =>
      match t.lexeme.toNat? with
      | some n => some (.lit (.int n), advance p)
      | none => none
    | .stringLiteral => some (.lit (.string t.lexeme), advance p)
    | .keyword "true" => some (.lit (.bool true), advance p)
    | .keyword "false" => some (.lit (.bool false), advance p)
    | _ => none
  | none => none

def isAtomStart (tk : TokenKind) : Bool :=
  match tk with
  | .identifier => true
  | .intLiteral => true
  | .stringLiteral => true
  | .keyword "true" => true
  | .keyword "false" => true
  | .delimiter "(" => true
  | .keyword "if" => true
  | .keyword "let" => true
  | .keyword "fn" => true
  | .delimiter "{" => true
  | _ => false

partial def parseExpr (p : Parser) : Option (Expr × Parser) :=
  parseOr p
where
  parseBinaryLeft (p : Parser)
      (parseNext : Parser → Option (Expr × Parser))
      (ops : List (String × Operator)) : Option (Expr × Parser) :=
    match parseNext p with
    | none => none
    | some (left, p) => parseBinaryTail left p parseNext ops

  parseBinaryTail (left : Expr) (p : Parser)
      (parseNext : Parser → Option (Expr × Parser))
      (ops : List (String × Operator)) : Option (Expr × Parser) :=
    match peek p with
    | some t =>
      match t.kind with
      | .operator opStr =>
        match ops.find? (fun (s, _) => s == opStr) with
        | some (_, op) =>
          let p := advance p
          match parseNext p with
          | none => none
          | some (right, p) =>
            parseBinaryTail (.binop op left right) p parseNext ops
        | none => some (left, p)
      | _ => some (left, p)
    | none => some (left, p)

  parseOr (p : Parser) : Option (Expr × Parser) :=
    parseBinaryLeft p parseAnd [("||", .or)]

  parseAnd (p : Parser) : Option (Expr × Parser) :=
    parseBinaryLeft p parseComparison [("&&", .and)]

  parseComparison (p : Parser) : Option (Expr × Parser) :=
    parseBinaryLeft p parseAdditive
      [("==", .eq), ("!=", .neq), ("<", .lt), (">", .gt), ("<=", .leq), (">=", .geq)]

  parseAdditive (p : Parser) : Option (Expr × Parser) :=
    parseBinaryLeft p parseMultiplicative [("+", .add), ("-", .sub)]

  parseMultiplicative (p : Parser) : Option (Expr × Parser) :=
    parseBinaryLeft p parseUnary [("*", .mul), ("/", .div), ("%", .mod)]

  parseUnary (p : Parser) : Option (Expr × Parser) :=
    match peek p with
    | some t =>
      match t.kind with
      | .operator "!" =>
        let p := advance p
        match parseUnary p with
        | none => none
        | some (e, p) => some (.unop .not e, p)
      | .operator "-" =>
        let p := advance p
        match parseUnary p with
        | none => none
        | some (e, p) => some (.unop .sub e, p)
      | _ => parseApplication p
    | none => none

  parseApplication (p : Parser) : Option (Expr × Parser) :=
    match parseAtom p with
    | none => none
    | some (fnExpr, p) => parseAppArgs fnExpr [] p

  parseAppArgs (fnExpr : Expr) (args : List Expr) (p : Parser) : Option (Expr × Parser) :=
    match peek p with
    | some t =>
      if isAtomStart t.kind then
        match parseAtom p with
        | none => none
        | some (arg, p) => parseAppArgs fnExpr (arg :: args) p
      else
        match args with
        | [] => some (fnExpr, p)
        | _ => some (.app fnExpr args.reverse, p)
    | none =>
      match args with
      | [] => some (fnExpr, p)
      | _ => some (.app fnExpr args.reverse, p)

  parseAtom (p : Parser) : Option (Expr × Parser) :=
    match peek p with
    | some t =>
      match t.kind with
      | .identifier => parseIdentifier p
      | .intLiteral => parseLiteral p
      | .stringLiteral => parseLiteral p
      | .keyword "true" => parseLiteral p
      | .keyword "false" => parseLiteral p
      | .delimiter "(" =>
        let p' := advance p
        match parseExpr p' with
        | some (e, p'') =>
          match expect (.delimiter ")") p'' with
          | some p''' => some (e, p''')
          | none => none
        | none => none
      | .keyword "if" => parseIfExpr p
      | .keyword "let" => parseLetExpr p
      | .keyword "fn" => parseFnExpr p
      | .delimiter "{" => parseBlockExpr p
      | _ => none
    | none => none

  parseIfExpr (p : Parser) : Option (Expr × Parser) :=
    match matchKeyword "if" p with
    | none => none
    | some p =>
      match parseExpr p with
      | none => none
      | some (cond, p) =>
        match matchKeyword "then" p with
        | none => none
        | some p =>
          match parseExpr p with
          | none => none
          | some (thenE, p) =>
            match matchKeyword "else" p with
            | none => none
            | some p =>
              match parseExpr p with
              | none => none
              | some (elseE, p) => some (.ifThenElse cond thenE elseE, p)

  parseLetExpr (p : Parser) : Option (Expr × Parser) :=
    match matchKeyword "let" p with
    | none => none
    | some p =>
      match peek p with
      | some t =>
        match t.kind with
        | .identifier =>
          let id := ⟨t.lexeme⟩
          let p := advance p
          match expect (.operator "=") p with
          | none => none
          | some p =>
            match parseExpr p with
            | none => none
            | some (init, p) =>
              match matchKeyword "in" p with
              | none => none
              | some p =>
                match parseExpr p with
                | none => none
                | some (body, p) => some (.let id init body, p)
        | _ => none
      | none => none

  parseFnExpr (p : Parser) : Option (Expr × Parser) :=
    match matchKeyword "fn" p with
    | none => none
    | some p => parseFnParams [] p

  parseFnParams (params : List Id) (p : Parser) : Option (Expr × Parser) :=
    match peek p with
    | some t =>
      match t.kind with
      | .identifier =>
        let p := advance p
        parseFnParams (⟨t.lexeme⟩ :: params) p
      | .operator "->" =>
        let p := advance p
        match parseExpr p with
        | none => none
        | some (body, p) => some (.lam params.reverse body, p)
      | _ => none
    | none => none

  parseBlockExpr (p : Parser) : Option (Expr × Parser) :=
    match expect (.delimiter "{") p with
    | none => none
    | some p => parseBlockBody [] p

  parseBlockBody (exprs : List Expr) (p : Parser) : Option (Expr × Parser) :=
    match peek p with
    | some t =>
      if t.kind == .delimiter "}" then
        some (.block exprs.reverse, advance p)
      else
        match parseExpr p with
        | none => none
        | some (e, p) =>
          let p := match expect (.delimiter ";") p with
            | some p => p
            | none => p
          parseBlockBody (e :: exprs) p
    | none => none

end Parser

def parse (src : String) : ParseResult :=
  let tokens := tokenize src
  let p : Parser := { tokens := tokens, pos := 0 }
  match Parser.parseExpr p with
  | some (e, p) =>
    if Parser.atEnd p then
      .ok e
    else
      match Parser.peek p with
      | some t => .error [{ message := "unexpected token", line := t.line, col := t.col }]
      | none => .error [{ message := "unexpected end", line := 0, col := 0 }]
  | none =>
    match Parser.peek p with
    | some t => .error [{ message := "failed to parse", line := t.line, col := t.col }]
    | none => .error [{ message := "empty input", line := 0, col := 0 }]

end Morph.Frontend

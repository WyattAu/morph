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
    | .identifier => some (.fvar t.lexeme, advance p)
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

/-! ## Total Parser

This used to be a single `partial def` with a `where` block: the descent chain
`parseOr -> parseAnd -> ... -> parseUnary -> parseApplication -> parseAtom`
makes no token progress, so no structural measure terminates it, and the
higher-order `parseNext` callbacks defeat well-founded recursion too (the
checker cannot see which function a parameter invokes).

The rewrite removes both obstacles:
- the seven nested binary levels are replaced by **precedence climbing**
  (`parseBinaryPrec`/`parseBinaryRest`), which is the same left-associative
  grammar expressed as one loop over an explicit precedence table; and
- every function takes a `Nat` fuel budget, returns `none` at zero, and passes
  the *predecessor* to every call - including each descent hop - with
  `termination_by fuel`.

The grammar nests at most seven levels per token, and every token-consuming
recursion consumes a token, so `10 * tokens + 100` bounds any well-formed
input; a malformed one fails earlier. Exhaustion is conservative `none`, not
divergence, and the parser reduces in the kernel, which the `partial` version
never did. -/

/-- Binary operators with their precedence (higher binds tighter). All levels
are left-associative, matching the original nested `parseBinaryLeft` chain. -/
def precedenceOf (opStr : String) : Option (Nat × Operator) :=
  match opStr with
  | "||" => some (1, .or)
  | "&&" => some (2, .and)
  | "==" => some (3, .eq)
  | "!=" => some (3, .neq)
  | "<" => some (3, .lt)
  | ">" => some (3, .gt)
  | "<=" => some (3, .leq)
  | ">=" => some (3, .geq)
  | "+" => some (4, .add)
  | "-" => some (4, .sub)
  | "*" => some (5, .mul)
  | "/" => some (5, .div)
  | "%" => some (5, .mod)
  | _ => none

mutual
private def parseExprFuel (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 => parseBinaryPrec fuel 1 p


/-- Parse a binary expression whose operators must have precedence at least
`minPrec` (precedence climbing). -/
private def parseBinaryPrec (fuel : Nat) (minPrec : Nat) (p : Parser) :
    Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseUnary fuel p with
    | none => none
    | some (left, p) => parseBinaryRest left fuel minPrec p


private def parseBinaryRest (left : Expr) (fuel : Nat) (minPrec : Nat)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .operator opStr =>
        match precedenceOf opStr with
        | some (prec, op) =>
          if prec < minPrec then some (left, p)
          else
            let p := advance p
            match parseBinaryPrec fuel (prec + 1) p with
            | none => none
            | some (right, p) =>
              parseBinaryRest (.binop op left right) fuel minPrec p
        | none => some (left, p)
      | _ => some (left, p)
    | none => some (left, p)


private def parseUnary (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .operator "!" =>
        let p := advance p
        match parseUnary fuel p with
        | none => none
        | some (e, p) => some (.unop .not e, p)
      | .operator "-" =>
        let p := advance p
        match parseUnary fuel p with
        | none => none
        | some (e, p) => some (.unop .sub e, p)
      | _ => parseApplication fuel p
    | none => none


private def parseApplication (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseAtom fuel p with
    | none => none
    | some (fnExpr, p) => parseAppArgs fnExpr fuel [] p


private def parseAppArgs (fnExpr : Expr) (fuel : Nat) (args : List Expr)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      if isAtomStart t.kind then
        match parseAtom fuel p with
        | none => none
        | some (arg, p) => parseAppArgs fnExpr fuel (arg :: args) p
      else
        match args with
        | [] => some (fnExpr, p)
        | _ => some (.app fnExpr args.reverse, p)
    | none =>
      match args with
      | [] => some (fnExpr, p)
      | _ => some (.app fnExpr args.reverse, p)


private def parseAtom (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
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
        match parseExprFuel fuel p' with
        | some (e, p'') =>
          match expect (.delimiter ")") p'' with
          | some p''' => some (e, p''')
          | none => none
        | none => none
      | .keyword "if" => parseIfExpr fuel p
      | .keyword "let" => parseLetExpr fuel p
      | .keyword "fn" => parseFnExpr fuel p
      | .delimiter "{" => parseBlockExpr fuel p
      | _ => none
    | none => none


private def parseIfExpr (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match matchKeyword "if" p with
    | none => none
    | some p =>
      match parseExprFuel fuel p with
      | none => none
      | some (cond, p) =>
        match matchKeyword "then" p with
        | none => none
        | some p =>
          match parseExprFuel fuel p with
          | none => none
          | some (thenE, p) =>
            match matchKeyword "else" p with
            | none => none
            | some p =>
              match parseExprFuel fuel p with
              | none => none
              | some (elseE, p) => some (.ifThenElse cond thenE elseE, p)


private def parseLetExpr (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match matchKeyword "let" p with
    | none => none
    | some p =>
      match peek p with
      | some t =>
        match t.kind with
        | .identifier =>
          let p := advance p
          match expect (.operator "=") p with
          | none => none
          | some p =>
            match parseExprFuel fuel p with
            | none => none
            | some (init, p) =>
              match matchKeyword "in" p with
              | none => none
              | some p =>
                match parseExprFuel fuel p with
                | none => none
                | some (body, p) => some (.let_ init body, p)
        | _ => none
      | none => none


private def parseFnExpr (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 => parseFnParams fuel [] p


private def parseFnParams (fuel : Nat) (params : List String)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .identifier =>
        let p := advance p
        parseFnParams fuel (t.lexeme :: params) p
      | .operator "->" =>
        let p := advance p
        match parseExprFuel fuel p with
        | none => none
        | some (body, p) => some (.lam params.length body, p)
      | _ => none
    | none => none


private def parseBlockExpr (fuel : Nat) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match expect (.delimiter "{") p with
    | none => none
    | some p => parseBlockBody fuel [] p


private def parseBlockBody (fuel : Nat) (exprs : List Expr)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      if t.kind == .delimiter "}" then
        some (.block exprs.reverse, advance p)
      else
        match parseExprFuel fuel p with
        | none => none
        | some (e, p) =>
          let p := match expect (.delimiter ";") p with
            | some p => p
            | none => p
          parseBlockBody fuel (e :: exprs) p
    | none => none


end

/-- Parse an expression, seeding the recursion with `10 * tokens + 100` fuel -
the grammar nests at most seven descent levels per token, so this bounds any
well-formed input. -/
def parseExpr (p : Parser) : Option (Expr × Parser) :=
  parseExprFuel (10 * p.tokens.length + 100) p

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

/-- Precedence and associativity, checked on the compiled evaluator (the same
`native_decide` style as the `Executable` tests). -/
example :
    (match parse "1 + 2 * 3" with
      | .ok e => e
      | .error _ => .lit .unit) ==
      .binop .add (.lit (.int 1)) (.binop .mul (.lit (.int 2)) (.lit (.int 3))) := by
  native_decide

example :
    (match parse "10 - 3 - 2" with
      | .ok e => e
      | .error _ => .lit .unit) ==
      .binop .sub (.binop .sub (.lit (.int 10)) (.lit (.int 3))) (.lit (.int 2)) := by
  native_decide

/-- Precedence of `&&` under `||`, checked by kernel reduction on the
destructured result: the fuel-based mutual recursion reduces definitionally,
which the `partial` version could never do. (The numeric examples above go
through `native_decide` because `String.toNat?` on lexer-produced substrings is
not kernel-reducible - the `String.Slice` API gap recorded in loop 13.) -/
example :
    (match parse "a || b && c" with
      | .ok e => e
      | .error _ => .lit .unit) =
      .binop .or (.fvar "a") (.binop .and (.fvar "b") (.fvar "c")) := by
  rfl

end Morph.Frontend

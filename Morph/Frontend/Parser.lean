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

/-- Look at the token after the next one. -/
def peek2 (p : Parser) : Option Token :=
  (p.tokens.drop (p.pos + 1)).head?

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

/-- Resolve an identifier against the scope (innermost binder first): a bound
name becomes its de Bruijn index, an unbound name stays free.

Loop 72: the parser used to emit `.fvar` for *every* identifier, but the
evaluator binds `bvar`s (`Context.pushBv`), so a parsed `let` or `fn` binding
could never be seen by the body that references it — `let x = 5 in x + 1`
evaluated to `stuck`, not `6`. -/

def resolveIdent (scope : List String) (name : String) : Expr :=
  match scope.findIdx? (· == name) with
  | some i => .bvar i
  | none => .fvar name

def parseIdentifier (scope : List String) (p : Parser) : Option (Expr × Parser) :=
  match peek p with
  | some t =>
    match t.kind with
    | .identifier => some (resolveIdent scope t.lexeme, advance p)
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
    | .keyword "none" => some (.none_, advance p)
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
recursion consumes a token, so `10 * tokens + 100` is believed to bound any
well-formed input; a malformed one fails earlier. That bound is an empirical
argument, not a proof - what *is* proved below is fuel monotonicity (more fuel
never loses a successful parse) and, from it, that the seed is robust: any input
that parses under a budget no larger than the seed also parses under the seed
with the same result. Exhaustion is conservative `none`, not divergence, and the
parser reduces in the kernel, which the `partial` version never did. -/

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
private def parseExprFuel (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 => parseBinaryPrec fuel 1 scope p


/-- Parse a binary expression whose operators must have precedence at least
`minPrec` (precedence climbing). -/
private def parseBinaryPrec (fuel : Nat) (minPrec : Nat) (scope : List String)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseUnary fuel scope p with
    | none => none
    | some (left, p) => parseBinaryRest left fuel minPrec scope p


private def parseBinaryRest (left : Expr) (fuel : Nat) (minPrec : Nat)
    (scope : List String) (p : Parser) : Option (Expr × Parser) :=
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
            match parseBinaryPrec fuel (prec + 1) scope p with
            | none => none
            | some (right, p) =>
              parseBinaryRest (.binop op left right) fuel minPrec scope p
        | none => some (left, p)
      | _ => some (left, p)
    | none => some (left, p)


private def parseUnary (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .operator "!" =>
        let p := advance p
        match parseUnary fuel scope p with
        | none => none
        | some (e, p) => some (.unop .not e, p)
      | .operator "-" =>
        let p := advance p
        match parseUnary fuel scope p with
        | none => none
        | some (e, p) => some (.unop .sub e, p)
      | _ => parseApplication fuel scope p
    | none => none


private def parseApplication (fuel : Nat) (scope : List String)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseAtom fuel scope p with
    | none => none
    | some (fnExpr, p) => parseAppArgs fnExpr fuel scope [] p


private def parseAppArgs (fnExpr : Expr) (fuel : Nat) (scope : List String)
    (args : List Expr) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      if isAtomStart t.kind then
        match parseAtom fuel scope p with
        | none => none
        | some (arg, p) => parseAppArgs fnExpr fuel scope (arg :: args) p
      else
        match args with
        | [] => some (fnExpr, p)
        | _ => some (.app fnExpr args.reverse, p)
    | none =>
      match args with
      | [] => some (fnExpr, p)
      | _ => some (.app fnExpr args.reverse, p)


/-- The atom's primary: literals, identifiers, grouping, tuples, arrays,
control-flow atoms, and the option/result prefixes (loop 73). -/
private def parseAtomPrimary (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .identifier => parseIdentifier scope p
      | .intLiteral => parseLiteral p
      | .stringLiteral => parseLiteral p
      | .keyword "true" => parseLiteral p
      | .keyword "false" => parseLiteral p
      | .keyword "none" => parseLiteral p
      | .keyword "some" => parseSomeLike .some_ fuel scope (advance p)
      | .keyword "ok" => parseSomeLike .ok_ fuel scope (advance p)
      | .keyword "err" => parseSomeLike .err_ fuel scope (advance p)
      | .delimiter "(" =>
        let p' := advance p
        match peek p' with
        | some t2 =>
          if t2.kind == .delimiter ")" then
            -- `()` is the unit literal
            some (.lit .unit, advance p')
          else
            match parseExprFuel fuel scope p' with
            | none => none
            | some (e, p'') =>
              match peek p'' with
              | some t3 =>
                if t3.kind == .delimiter "," then
                  -- `(a, b, ...)` is a tuple; `(e)` is grouping
                  parseTupleRest fuel scope [e] p''
                else
                  match expect (.delimiter ")") p'' with
                  | some p''' => some (e, p''')
                  | none => none
              | none => none
        | none => none
      | .delimiter "[" => parseArrayLit fuel scope (advance p)
      | .keyword "if" => parseIfExpr fuel scope p
      | .keyword "let" => parseLetExpr fuel scope p
      -- loop 72: consume the `fn` keyword before collecting parameters; the
      -- old code left the cursor on `fn`, so `parseFnParams` saw a keyword
      -- where it wanted an identifier and every lambda failed to parse
      | .keyword "fn" => parseFnExpr fuel scope (advance p)
      | .delimiter "{" => parseBlockExpr fuel scope p
      | _ => none
    | none => none

/-- Postfix operations, tightest-binding: indexing `a[i]` and field access
`a.f` (loop 73). Each iteration consumes at least the `[`/`.` token, so the
recursion makes token progress. -/
private def parsePostfix (fuel : Nat) (scope : List String) (e : Expr)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .delimiter "[" =>
        let p' := advance p
        match parseExprFuel fuel scope p' with
        | none => none
        | some (idx, p'') =>
          match expect (.delimiter "]") p'' with
          | none => none
          | some p''' => parsePostfix fuel scope (.arrayIndex e idx) p'''
      | .operator "." =>
        let p' := advance p
        match peek p' with
        | some t2 =>
          match t2.kind with
          | .identifier =>
            parsePostfix fuel scope (.field_ e t2.lexeme) (advance p')
          | _ => none
        | none => none
      | _ => some (e, p)
    | none => some (e, p)

/-- A prefix `some`/`ok`/`err` wraps one atom. -/
private def parseSomeLike (wrap : Expr → Expr) (fuel : Nat)
    (scope : List String) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseAtom fuel scope p with
    | some (e, p') => some (wrap e, p')
    | none => none

/-- The elements after the first in `(a, b, ...)`, closing on `)`.
`acc` is reversed. -/
private def parseTupleRest (fuel : Nat) (scope : List String) (acc : List Expr)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let p := advance p
    match parseExprFuel fuel scope p with
    | none => none
    | some (e, p1) =>
      let acc' := e :: acc
      match peek p1 with
      | some t =>
        if t.kind == .delimiter "," then
          parseTupleRest fuel scope acc' p1
        else
          match expect (.delimiter ")") p1 with
          | some p2 => some (.tuple_ acc'.reverse, p2)
          | none => none
      | none => none

/-- `[a, b, ...]`, with the cursor just past the `[`. -/
private def parseArrayLit (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      if t.kind == .delimiter "]" then
        some (.arrayLit [], advance p)
      else
        parseArrayElems fuel scope [] p
    | none => none

private def parseArrayElems (fuel : Nat) (scope : List String) (acc : List Expr)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseExprFuel fuel scope p with
    | none => none
    | some (e, p1) =>
      let acc' := e :: acc
      match peek p1 with
      | some t =>
        if t.kind == .delimiter "," then
          -- the cursor moves past the comma; the next element follows
          parseArrayElems fuel scope acc' (advance p1)
        else
          match expect (.delimiter "]") p1 with
          | some p2 => some (.arrayLit acc'.reverse, p2)
          | none => none
      | none => none

private def parseAtom (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseAtomPrimary fuel scope p with
    | none => none
    | some (e, p') => parsePostfix fuel scope e p'


private def parseIfExpr (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match matchKeyword "if" p with
    | none => none
    | some p =>
      match parseExprFuel fuel scope p with
      | none => none
      | some (cond, p) =>
        match matchKeyword "then" p with
        | none => none
        | some p =>
          match parseExprFuel fuel scope p with
          | none => none
          | some (thenE, p) =>
            match matchKeyword "else" p with
            | none => none
            | some p =>
              match parseExprFuel fuel scope p with
              | none => none
              | some (elseE, p) => some (.ifThenElse cond thenE elseE, p)


private def parseLetExpr (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Expr × Parser) :=
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
          -- the initialiser is parsed in the outer scope; only the body sees
          -- the new binder
          let name := t.lexeme
          let p := advance p
          match expect (.operator "=") p with
          | none => none
          | some p =>
            match parseExprFuel fuel scope p with
            | none => none
            | some (init, p) =>
              match matchKeyword "in" p with
              | none => none
              | some p =>
                match parseExprFuel fuel (name :: scope) p with
                | none => none
                | some (body, p) => some (.let_ init body, p)
        | _ => none
      | none => none


private def parseFnExpr (fuel : Nat) (scope : List String)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 => parseFnParams fuel [] scope p


private def parseFnParams (fuel : Nat) (params : List String)
    (scope : List String) (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .identifier =>
        let p := advance p
        parseFnParams fuel (t.lexeme :: params) scope p
      | .operator "->" =>
        let p := advance p
        -- `params` accumulated innermost-first, so it is already the body's
        -- de Bruijn scope; outer bindings shift by `params.length`, which is
        -- exactly what `.lam`'s substitution performs
        match parseExprFuel fuel (params ++ scope) p with
        | none => none
        | some (body, p) => some (.lam params.length body, p)
      | _ => none
    | none => none


private def parseBlockExpr (fuel : Nat) (scope : List String)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match expect (.delimiter "{") p with
    | none => none
    | some p => parseBlockBody fuel scope [] p


private def parseBlockBody (fuel : Nat) (scope : List String) (exprs : List Expr)
    (p : Parser) : Option (Expr × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      if t.kind == .delimiter "}" then
        some (.block exprs.reverse, advance p)
      else
        match parseExprFuel fuel scope p with
        | none => none
        | some (e, p) =>
          let p := match expect (.delimiter ";") p with
            | some p => p
            | none => p
          parseBlockBody fuel scope (e :: exprs) p
    | none => none

/-- One statement (loop 74). Declarations (`let x = e;`), assignments
(`x = e;` — a single `=`, not `==`), `return e;`, `break;`, `continue;`,
`while (c) { .. }`, `do { .. } while (c);`, and expression statements.
Statement variables are free names (the interpreter binds them in the
`Context.fvs` environment); the expression-level binders `let .. in` and
`fn .. ->` keep their de Bruijn scope. -/

private def parseStmt (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Stmt × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | some t =>
      match t.kind with
      | .keyword "let" =>
        -- `let x = e;` declares; `let x = e in ..` is the expression form
        let p1 := advance p
        match peek p1 with
        | some t2 =>
          match t2.kind with
          | .identifier =>
            let name := t2.lexeme
            let p2 := advance p1
            match expect (.operator "=") p2 with
            | none => none
            | some p3 =>
              match parseExprFuel fuel scope p3 with
              | none => none
              | some (init, p4) =>
                match peek p4 with
                | some t4 =>
                  if t4.kind == .keyword "in" then
                    let p5 := advance p4
                    match parseExprFuel fuel (name :: scope) p5 with
                    | none => none
                    | some (body, p6) =>
                      match expect (.delimiter ";") p6 with
                      | some p7 => some (.exprStmt (.let_ init body), p7)
                      | none => none
                  else if t4.kind == .delimiter ";" then
                    some (.varDecl ⟨name⟩ .unitType init, advance p4)
                  else
                    none
                | none => none
          | _ => none
        | none => none
      | .keyword "while" =>
        let p1 := advance p
        match expect (.delimiter "(") p1 with
        | none => none
        | some p2 =>
          match parseExprFuel fuel scope p2 with
          | none => none
          | some (cond, p3) =>
            match expect (.delimiter ")") p3 with
            | none => none
            | some p4 =>
              match expect (.delimiter "{") p4 with
              | none => none
              | some p5 =>
                match parseStmts fuel scope [] p5 with
                | none => none
                | some (body, p6) =>
                  match expect (.delimiter "}") p6 with
                  | some p7 => some (.whileLoop cond body, p7)
                  | none => none
      | .keyword "do" =>
        let p1 := advance p
        match expect (.delimiter "{") p1 with
        | none => none
        | some p2 =>
          match parseStmts fuel scope [] p2 with
          | none => none
          | some (body, p3) =>
            match expect (.delimiter "}") p3 with
            | none => none
            | some p4 =>
              match matchKeyword "while" p4 with
              | none => none
              | some p5 =>
                match expect (.delimiter "(") p5 with
                | none => none
                | some p6 =>
                  match parseExprFuel fuel scope p6 with
                  | none => none
                  | some (cond, p7) =>
                    match expect (.delimiter ")") p7 with
                    | none => none
                    | some p8 =>
                      match expect (.delimiter ";") p8 with
                      | some p9 => some (.doWhile cond body, p9)
                      | none => none
      | .keyword "return" =>
        let p1 := advance p
        match parseExprFuel fuel scope p1 with
        | none => none
        | some (e, p2) =>
          match expect (.delimiter ";") p2 with
          | some p3 => some (.returnStmt e, p3)
          | none => none
      | .keyword "break" =>
        match expect (.delimiter ";") (advance p) with
        | some p1 => some (.break, p1)
        | none => none
      | .keyword "continue" =>
        match expect (.delimiter ";") (advance p) with
        | some p1 => some (.continue, p1)
        | none => none
      | .identifier =>
        -- `x = e;` is an assignment: a single `=`, not `==`
        match peek2 p with
        | some t2 =>
          if t2.kind == .operator "=" then
            let p1 := advance (advance p)
            match parseExprFuel fuel scope p1 with
            | none => none
            | some (e, p2) =>
              match expect (.delimiter ";") p2 with
              | some p3 => some (.assign ⟨t.lexeme⟩ e, p3)
              | none => none
          else
            parseExprStmt fuel scope p
        | none => parseExprStmt fuel scope p
      | _ => parseExprStmt fuel scope p
    | none => none

private def parseExprStmt (fuel : Nat) (scope : List String) (p : Parser) :
    Option (Stmt × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseExprFuel fuel scope p with
    | none => none
    | some (e, p') =>
      -- a trailing `;` is consumed; at the very end of the program it may be
      -- omitted
      match peek p' with
      | some t =>
        if t.kind == .delimiter ";" then some (.exprStmt e, advance p')
        else some (.exprStmt e, p')
      | none => some (.exprStmt e, p')

private def parseStmts (fuel : Nat) (scope : List String) (acc : List Stmt)
    (p : Parser) : Option (List Stmt × Parser) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match peek p with
    | none => some (acc.reverse, p)
    | some t =>
      if t.kind == .delimiter "}" then
        -- leave the `}` for the caller
        some (acc.reverse, p)
      else if t.kind == .delimiter ";" then
        -- a stray separator (e.g. after a `}` closing a loop body)
        parseStmts fuel scope acc (advance p)
      else
        match parseStmt fuel scope p with
        | none => none
        | some (s, p') => parseStmts fuel scope (s :: acc) p'


end

/-! ## Fuel monotonicity

Every function in the parser block takes a `Nat` budget and passes the
predecessor to each call. This section proves the design invariant: **more fuel
never hurts**. If a parse succeeds at fuel `n`, it succeeds with the same result
at any larger budget `n + k`.

That is what makes the fixed seed in `parseExpr` sound in the only way a fixed
constant can be: the seed need not be tight, only large enough *once*. The
grammar argument that `10 * tokens + 100` is large enough is empirical (recorded
in the module docstring); the machine-checked part is that no well-formed input
that fits under any smaller budget is lost by the larger one. -/
mutual

private theorem parseExprFuel_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseExprFuel n scope p = some r) (k : Nat) :
    parseExprFuel (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseExprFuel] at h
  | n + 1 =>
    rw [Nat.succ_add]
    exact parseBinaryPrec_mono n 1 scope p r h k

private theorem parseBinaryPrec_mono (n : Nat) (minPrec : Nat)
    (scope : List String) (p : Parser) (r : Expr × Parser)
    (h : parseBinaryPrec n minPrec scope p = some r) (k : Nat) :
    parseBinaryPrec (n + k) minPrec scope p = some r := by
  match n with
  | 0 => simp [parseBinaryPrec] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseBinaryPrec] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseUnary_mono, parseBinaryRest_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseUnary_mono _ _ _ r h k
      | exact parseBinaryRest_mono _ _ _ _ _ r h k

private theorem parseBinaryRest_mono (left : Expr) (n : Nat) (minPrec : Nat)
    (scope : List String) (p : Parser) (r : Expr × Parser)
    (h : parseBinaryRest left n minPrec scope p = some r) (k : Nat) :
    parseBinaryRest left (n + k) minPrec scope p = some r := by
  match n with
  | 0 => simp [parseBinaryRest] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseBinaryRest] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseBinaryPrec_mono, parseBinaryRest_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseBinaryPrec_mono _ _ _ _ r h k
      | exact parseBinaryRest_mono _ _ _ _ _ r h k

private theorem parseUnary_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseUnary n scope p = some r) (k : Nat) :
    parseUnary (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseUnary] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseUnary] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseUnary_mono, parseApplication_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseUnary_mono _ _ _ r h k
      | exact parseApplication_mono _ _ _ r h k

private theorem parseApplication_mono (n : Nat) (scope : List String)
    (p : Parser) (r : Expr × Parser) (h : parseApplication n scope p = some r)
    (k : Nat) : parseApplication (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseApplication] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseApplication] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseAtom_mono, parseAppArgs_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseAtom_mono _ _ _ r h k
      | exact parseAppArgs_mono _ _ _ _ _ r h k

private theorem parseAppArgs_mono (fnExpr : Expr) (n : Nat) (scope : List String)
    (args : List Expr) (p : Parser) (r : Expr × Parser)
    (h : parseAppArgs fnExpr n scope args p = some r) (k : Nat) :
    parseAppArgs fnExpr (n + k) scope args p = some r := by
  match n with
  | 0 => simp [parseAppArgs] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseAppArgs] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseAtom_mono, parseAppArgs_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseAtom_mono _ _ _ r h k
      | exact parseAppArgs_mono _ _ _ _ _ r h k

private theorem parseAtom_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseAtom n scope p = some r) (k : Nat) :
    parseAtom (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseAtom] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseAtom] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseAtomPrimary_mono, parsePostfix_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseAtomPrimary_mono _ _ _ r h k
      | exact parsePostfix_mono _ _ _ _ r h k

private theorem parseIfExpr_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseIfExpr n scope p = some r) (k : Nat) :
    parseIfExpr (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseIfExpr] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseIfExpr] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k

private theorem parseLetExpr_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseLetExpr n scope p = some r) (k : Nat) :
    parseLetExpr (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseLetExpr] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseLetExpr] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ r h k

private theorem parseFnExpr_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseFnExpr n scope p = some r) (k : Nat) :
    parseFnExpr (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseFnExpr] at h
  | n + 1 =>
    rw [Nat.succ_add]
    exact parseFnParams_mono n [] scope p r h k

private theorem parseFnParams_mono (n : Nat) (params : List String)
    (scope : List String) (p : Parser) (r : Expr × Parser)
    (h : parseFnParams n params scope p = some r) (k : Nat) :
    parseFnParams (n + k) params scope p = some r := by
  match n with
  | 0 => simp [parseFnParams] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseFnParams] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseFnParams_mono, parseExprFuel_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseFnParams_mono _ _ _ _ r h k
      | exact parseExprFuel_mono _ _ _ r h k

private theorem parseBlockExpr_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseBlockExpr n scope p = some r) (k : Nat) :
    parseBlockExpr (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseBlockExpr] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseBlockExpr] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseBlockBody_mono]
    all_goals exact parseBlockBody_mono _ _ _ _ r h k

private theorem parseBlockBody_mono (n : Nat) (scope : List String)
    (exprs : List Expr) (p : Parser) (r : Expr × Parser)
    (h : parseBlockBody n scope exprs p = some r) (k : Nat) :
    parseBlockBody (n + k) scope exprs p = some r := by
  match n with
  | 0 => simp [parseBlockBody] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseBlockBody] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono, parseBlockBody_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k
      | exact parseBlockBody_mono _ _ _ _ r h k

private theorem parseAtomPrimary_mono (n : Nat) (scope : List String)
    (p : Parser) (r : Expr × Parser) (h : parseAtomPrimary n scope p = some r)
    (k : Nat) : parseAtomPrimary (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseAtomPrimary] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseAtomPrimary] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono, parseIfExpr_mono, parseLetExpr_mono,
      parseFnExpr_mono, parseBlockExpr_mono, parseSomeLike_mono,
      parseTupleRest_mono, parseArrayLit_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k
      | exact parseIfExpr_mono _ _ _ r h k
      | exact parseLetExpr_mono _ _ _ r h k
      | exact parseFnExpr_mono _ _ _ r h k
      | exact parseBlockExpr_mono _ _ _ r h k
      | exact parseSomeLike_mono _ _ _ _ r h k
      | exact parseTupleRest_mono _ _ _ _ r h k
      | exact parseArrayLit_mono _ _ _ r h k

private theorem parsePostfix_mono (n : Nat) (scope : List String) (e : Expr)
    (p : Parser) (r : Expr × Parser) (h : parsePostfix n scope e p = some r)
    (k : Nat) : parsePostfix (n + k) scope e p = some r := by
  match n with
  | 0 => simp [parsePostfix] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parsePostfix] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono, parsePostfix_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k
      | exact parsePostfix_mono _ _ _ _ r h k

private theorem parseSomeLike_mono (wrap : Expr → Expr) (n : Nat)
    (scope : List String) (p : Parser) (r : Expr × Parser)
    (h : parseSomeLike wrap n scope p = some r) (k : Nat) :
    parseSomeLike wrap (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseSomeLike] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseSomeLike] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseAtom_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseAtom_mono _ _ _ r h k

private theorem parseTupleRest_mono (fuel : Nat) (scope : List String)
    (acc : List Expr) (p : Parser) (r : Expr × Parser)
    (h : parseTupleRest fuel scope acc p = some r) (k : Nat) :
    parseTupleRest (fuel + k) scope acc p = some r := by
  match fuel with
  | 0 => simp [parseTupleRest] at h
  | fuel + 1 =>
    rw [Nat.succ_add]
    simp only [parseTupleRest] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono, parseTupleRest_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k
      | exact parseTupleRest_mono _ _ _ _ r h k

private theorem parseArrayLit_mono (n : Nat) (scope : List String) (p : Parser)
    (r : Expr × Parser) (h : parseArrayLit n scope p = some r) (k : Nat) :
    parseArrayLit (n + k) scope p = some r := by
  match n with
  | 0 => simp [parseArrayLit] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseArrayLit] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseArrayElems_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseArrayElems_mono _ _ _ _ r h k

private theorem parseArrayElems_mono (fuel : Nat) (scope : List String)
    (acc : List Expr) (p : Parser) (r : Expr × Parser)
    (h : parseArrayElems fuel scope acc p = some r) (k : Nat) :
    parseArrayElems (fuel + k) scope acc p = some r := by
  match fuel with
  | 0 => simp [parseArrayElems] at h
  | fuel + 1 =>
    rw [Nat.succ_add]
    simp only [parseArrayElems] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono, parseArrayElems_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k
      | exact parseArrayElems_mono _ _ _ _ r h k

private theorem parseStmt_mono (fuel : Nat) (scope : List String) (p : Parser)
    (r : Stmt × Parser) (h : parseStmt fuel scope p = some r) (k : Nat) :
    parseStmt (fuel + k) scope p = some r := by
  match fuel with
  | 0 => simp [parseStmt] at h
  | fuel + 1 =>
    rw [Nat.succ_add]
    simp only [parseStmt] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono, parseStmts_mono, parseExprStmt_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k
      | exact parseStmts_mono _ _ _ _ r h k
      | exact parseExprStmt_mono _ _ _ r h k

private theorem parseExprStmt_mono (fuel : Nat) (scope : List String)
    (p : Parser) (r : Stmt × Parser) (h : parseExprStmt fuel scope p = some r)
    (k : Nat) : parseExprStmt (fuel + k) scope p = some r := by
  match fuel with
  | 0 => simp [parseExprStmt] at h
  | fuel + 1 =>
    rw [Nat.succ_add]
    simp only [parseExprStmt] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ _ r h k

private theorem parseStmts_mono (fuel : Nat) (scope : List String)
    (acc : List Stmt) (p : Parser) (r : List Stmt × Parser)
    (h : parseStmts fuel scope acc p = some r) (k : Nat) :
    parseStmts (fuel + k) scope acc p = some r := by
  match fuel with
  | 0 => simp [parseStmts] at h
  | fuel + 1 =>
    rw [Nat.succ_add]
    simp only [parseStmts] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseStmt_mono, parseStmts_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseStmt_mono _ _ _ r h k
      | exact parseStmts_mono _ _ _ _ r h k

end



/-- Parse an expression, seeding the recursion with `10 * tokens + 100` fuel -
the grammar nests at most seven descent levels per token, so this bounds any
well-formed input. -/
def parseExpr (p : Parser) : Option (Expr × Parser) :=
  parseExprFuel (10 * p.tokens.length + 100) [] p

/-- **The seed is robust.** If a parse succeeds at any budget `f` that does not
exceed the seeded budget, it succeeds at the seeded budget with the same result.
This is the machine-checked half of the fixed-seed argument: the constant in
`parseExpr` only has to be large enough for the longest well-formed input, and
no input that fits under a smaller budget is lost. -/
private theorem parseExpr_seed_robust (p : Parser) (f : Nat) (r : Expr × Parser)
    (hf : f ≤ 10 * p.tokens.length + 100)
    (h : parseExprFuel f [] p = some r) :
    parseExpr p = some r := by
  unfold parseExpr
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hf
  rw [hd]
  exact parseExprFuel_mono f [] p r h d

end Parser

/-- The result of parsing a statement sequence. -/
inductive ProgramParseResult where
  | ok : Program → ProgramParseResult
  | error : List ParseError → ProgramParseResult
  deriving Repr

/-- Parse a whole statement sequence (loop 74). Same seeding discipline as
`parse`: `10 * tokens + 100` fuel, robust under `parseStmts_mono`. -/
def parseProgram (src : String) : ProgramParseResult :=
  let tokens := tokenize src
  let p : Parser := { tokens := tokens, pos := 0 }
  match Parser.parseStmts (10 * tokens.length + 100) [] [] p with
  | some (stmts, p') =>
    if Parser.atEnd p' then
      .ok { stmts := stmts }
    else
      match Parser.peek p' with
      | some t => .error [{ message := "unexpected token", line := t.line, col := t.col }]
      | none => .error [{ message := "unexpected end", line := 0, col := 0 }]
  | none =>
    match Parser.peek p with
    | some t => .error [{ message := "failed to parse", line := t.line, col := t.col }]
    | none => .error [{ message := "empty input", line := 0, col := 0 }]

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

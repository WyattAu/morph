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

private theorem parseExprFuel_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseExprFuel n p = some r) (k : Nat) :
    parseExprFuel (n + k) p = some r := by
  match n with
  | 0 => simp [parseExprFuel] at h
  | n + 1 =>
    rw [Nat.succ_add]
    exact parseBinaryPrec_mono n 1 p r h k

private theorem parseBinaryPrec_mono (n : Nat) (minPrec : Nat) (p : Parser)
    (r : Expr × Parser) (h : parseBinaryPrec n minPrec p = some r) (k : Nat) :
    parseBinaryPrec (n + k) minPrec p = some r := by
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
      | exact parseUnary_mono _ _ r h k
      | exact parseBinaryRest_mono _ _ _ _ r h k

private theorem parseBinaryRest_mono (left : Expr) (n : Nat) (minPrec : Nat)
    (p : Parser) (r : Expr × Parser)
    (h : parseBinaryRest left n minPrec p = some r) (k : Nat) :
    parseBinaryRest left (n + k) minPrec p = some r := by
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
      | exact parseBinaryPrec_mono _ _ _ r h k
      | exact parseBinaryRest_mono _ _ _ _ r h k

private theorem parseUnary_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseUnary n p = some r) (k : Nat) :
    parseUnary (n + k) p = some r := by
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
      | exact parseUnary_mono _ _ r h k
      | exact parseApplication_mono _ _ r h k

private theorem parseApplication_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseApplication n p = some r) (k : Nat) :
    parseApplication (n + k) p = some r := by
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
      | exact parseAtom_mono _ _ r h k
      | exact parseAppArgs_mono _ _ _ _ r h k

private theorem parseAppArgs_mono (fnExpr : Expr) (n : Nat) (args : List Expr)
    (p : Parser) (r : Expr × Parser)
    (h : parseAppArgs fnExpr n args p = some r) (k : Nat) :
    parseAppArgs fnExpr (n + k) args p = some r := by
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
      | exact parseAtom_mono _ _ r h k
      | exact parseAppArgs_mono _ _ _ _ r h k

private theorem parseAtom_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseAtom n p = some r) (k : Nat) :
    parseAtom (n + k) p = some r := by
  match n with
  | 0 => simp [parseAtom] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseAtom] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseExprFuel_mono, parseIfExpr_mono, parseLetExpr_mono, parseFnExpr_mono, parseBlockExpr_mono]
    all_goals first
      | (intro _; assumption)
      | (intro _; simp_all)
      | (intro hc; exact absurd hc (by omega))
      | exact parseExprFuel_mono _ _ r h k
      | exact parseIfExpr_mono _ _ r h k
      | exact parseLetExpr_mono _ _ r h k
      | exact parseFnExpr_mono _ _ r h k
      | exact parseBlockExpr_mono _ _ r h k

private theorem parseIfExpr_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseIfExpr n p = some r) (k : Nat) :
    parseIfExpr (n + k) p = some r := by
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
      | exact parseExprFuel_mono _ _ r h k

private theorem parseLetExpr_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseLetExpr n p = some r) (k : Nat) :
    parseLetExpr (n + k) p = some r := by
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

private theorem parseFnExpr_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseFnExpr n p = some r) (k : Nat) :
    parseFnExpr (n + k) p = some r := by
  match n with
  | 0 => simp [parseFnExpr] at h
  | n + 1 =>
    rw [Nat.succ_add]
    exact parseFnParams_mono n [] p r h k

private theorem parseFnParams_mono (n : Nat) (params : List String) (p : Parser)
    (r : Expr × Parser) (h : parseFnParams n params p = some r) (k : Nat) :
    parseFnParams (n + k) params p = some r := by
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
      | exact parseFnParams_mono _ _ _ r h k
      | exact parseExprFuel_mono _ _ r h k

private theorem parseBlockExpr_mono (n : Nat) (p : Parser) (r : Expr × Parser)
    (h : parseBlockExpr n p = some r) (k : Nat) :
    parseBlockExpr (n + k) p = some r := by
  match n with
  | 0 => simp [parseBlockExpr] at h
  | n + 1 =>
    rw [Nat.succ_add]
    simp only [parseBlockExpr] at h ⊢
    repeat' split at h
    all_goals try simp_all [parseBlockBody_mono]
    all_goals exact parseBlockBody_mono _ _ _ r h k

private theorem parseBlockBody_mono (n : Nat) (exprs : List Expr) (p : Parser)
    (r : Expr × Parser) (h : parseBlockBody n exprs p = some r) (k : Nat) :
    parseBlockBody (n + k) exprs p = some r := by
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
      | exact parseExprFuel_mono _ _ r h k
      | exact parseBlockBody_mono _ _ _ r h k

end



/-- Parse an expression, seeding the recursion with `10 * tokens + 100` fuel -
the grammar nests at most seven descent levels per token, so this bounds any
well-formed input. -/
def parseExpr (p : Parser) : Option (Expr × Parser) :=
  parseExprFuel (10 * p.tokens.length + 100) p

/-- **The seed is robust.** If a parse succeeds at any budget `f` that does not
exceed the seeded budget, it succeeds at the seeded budget with the same result.
This is the machine-checked half of the fixed-seed argument: the constant in
`parseExpr` only has to be large enough for the longest well-formed input, and
no input that fits under a smaller budget is lost. -/
private theorem parseExpr_seed_robust (p : Parser) (f : Nat) (r : Expr × Parser)
    (hf : f ≤ 10 * p.tokens.length + 100)
    (h : parseExprFuel f p = some r) :
    parseExpr p = some r := by
  unfold parseExpr
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hf
  rw [hd]
  exact parseExprFuel_mono f p r h d

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

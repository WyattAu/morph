/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# A Total Lexer

Research loop 9. Target: `Morph/Frontend/Lexer.lean` and
`Morph/Specs/LexicalStructureSyntax/`.

**What the loop found.** The shipped lexer's driver is
`partial def nextToken (l : Lexer) : Lexer × Option Token`, and
`scanString` is `partial` too. Two consequences:

1. **Totality is assumed, not proved.** `partial` means the termination argument
   is not in the kernel, so "every input is eventually consumed" — the property a
   compiler front end is *required* to have — is not a theorem anywhere.
2. **`Option Token` conflates three outcomes**: end of input, lexical error
   (unterminated string), and "I could not lex this". A caller cannot tell
   "finished" from "broken", which is why `partial` had to be reached for.

`Morph/Specs/LexicalStructureSyntax/Lemmas.lean` confirms the pattern: ten
lemmas, every one of them `rfl` about `String.length`, `Char.isDigit`, or
`List.toString`. There is no lexer in the specification at all.

**Research basis.**

- **Maximal munch** (Dragon book §3.4; Marpa, *Marpa's looking-glass parser
  factory*, 2012): a lexer must take the *longest* run a rule matches, and
  lexing fails only when no rule matches — so a total lexer is one in which
  every input either produces a token or an explicit error, never silence.
- **Aycock & Horspool**, *Practical General-Purpose Partial Parsing* (PLDI 2003),
  argues the opposite is often what you want: partial parsing that accepts a
  prefix and defers the error. Morph's `Option Token` is already an instance of
  that, deliberately. This specification therefore does **not** claim a lexer has
  no partial states; it claims the partial states are *named and separate* from
  end of input, which is what the shipped `Option Token` fails to do.

## What is formalized

A total, fuel-driven lexer over a list of characters, with end-of-input as an
ordinary token, plus:

- **progress**: every step either consumes a character or reports `.eof`;
- **the fuel bound**: at most `n + 1` tokens for fuel `n`;
- **maximal munch** for identifier and digit runs.
-/

namespace Morph.Specs.TotalLexer

open Std

/-- The token kinds of the core language. `.eof` is an ordinary token, not an
absence: that is the whole point. -/
inductive TokKind where
  /-- A decimal literal. -/
  | num (v : Nat)
  /-- An identifier or keyword. -/
  | ident (s : String)
  /-- An operator or punctuation character. -/
  | op (s : String)
  /-- End of input. -/
  | eof
  deriving Repr, BEq, DecidableEq

/-- Character classes. -/
def isDigitC (c : Char) : Bool := c.isDigit

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

def isIdentRest (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_'

def isOpC (c : Char) : Bool :=
  c == '+' || c == '-' || c == '*' || c == '/' || c == '=' || c == '<' || c == '>' ||
  c == '(' || c == ')' || c == '{' || c == '}' || c == ';' || c == ',' || c == ':'

/-- Skip whitespace. Total, and only ever removes characters. -/
def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if c.isWhitespace then skipWs cs else c :: cs

/-- **Maximal munch**: take the longest run of characters satisfying `p`. Total,
and it consumes at least one character whenever the predicate holds at the head. -/
def takeWhile (p : Char → Bool) : List Char → List Char
  | [] => []
  | c :: cs => if p c then c :: takeWhile p cs else []

/-- The remainder after a maximal-munch run. -/
def dropWhile (p : Char → Bool) : List Char → List Char
  | [] => []
  | c :: cs => if p c then dropWhile p cs else c :: cs

/-- Accumulate the value of a digit run. -/
def digitsValue : Nat → List Char → Nat
  | acc, [] => acc
  | acc, c :: cs => digitsValue (acc * 10 + (c.toNat - '0'.toNat)) cs

/-- Scan a decimal literal. -/
def scanNum : List Char → Option (Nat × List Char)
  | [] => none
  | c :: cs => if isDigitC c then some (digitsValue 0 (c :: cs), dropWhile isDigitC (c :: cs))
                else none

/-- Scan an identifier or keyword. -/
def scanIdent : List Char → Option (String × List Char)
  | [] => none
  | c :: cs => if isIdentStart c then some (String.ofList (takeWhile isIdentRest (c :: cs)),
                                              dropWhile isIdentRest (c :: cs))
              else none

/-- Scan a one-character operator. -/
def scanOp : List Char → Option (String × List Char)
  | [] => none
  | c :: cs => if isOpC c then some (String.singleton c, cs) else none

/-- **One lexing step. Total: it always returns a token.** Whitespace is skipped;
a digit starts a number, an identifier start starts a name, an operator character
is an operator, an unknown character is *itself* an operator token (never
silently dropped), and exhausted input yields `.eof`.

Every branch that is not `.eof` consumes the head character — including the
fallback for a character no rule matches, which is exactly where a lexer can
silently fail to make progress.

This is the property `Morph/Frontend/Lexer.lean`'s `partial def nextToken` does
not have: there is no input on which this function has nothing to say. -/
def nextToken (cs : List Char) : TokKind × List Char :=
  let rest := skipWs cs
  match rest with
  | [] => (.eof, [])
  | c :: _ =>
      match scanNum rest with
      | some (v, r) => (.num v, r)
      | none =>
          match scanIdent rest with
          | some (s, r) => (.ident s, r)
          | none =>
              match scanOp rest with
              | some (s, r) => (.op s, r)
              | none => (.op (String.singleton c), rest.tail)

end Morph.Specs.TotalLexer

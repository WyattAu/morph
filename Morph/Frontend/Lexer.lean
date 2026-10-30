/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Morph.Specs.LexicalStructureSyntax.Spec

namespace Morph.Frontend

open Morph.Specs.LexicalStructureSyntax

inductive TokenKind where
  | identifier : TokenKind
  | intLiteral : TokenKind
  | stringLiteral : TokenKind
  | boolLiteral : TokenKind
  | keyword : String → TokenKind
  | operator : String → TokenKind
  | delimiter : String → TokenKind
  | eof : TokenKind
  deriving Repr, BEq, DecidableEq

structure Token where
  kind : TokenKind
  lexeme : String
  line : Nat
  col : Nat
  deriving Repr, BEq

structure Lexer where
  chars : List Char
  line : Nat
  col : Nat
  deriving Repr

namespace Lexer

def init (src : String) : Lexer :=
  { chars := src.toList, line := 1, col := 1 }

def atEnd (l : Lexer) : Bool :=
  l.chars.isEmpty

def currentChar (l : Lexer) : Char :=
  l.chars.headD '\x00'

def peekChar (l : Lexer) : Char :=
  (l.chars.tailD []).headD '\x00'

def advanceChar (l : Lexer) : Lexer :=
  match l.chars with
  | [] => l
  | c :: rest =>
    if c == '\n' then
      { chars := rest, line := l.line + 1, col := 1 }
    else
      { chars := rest, col := l.col + 1, line := l.line }

/-- Advance while the predicate holds, with an explicit fuel.

The recursion is bounded by the number of characters remaining, so the fuel is
never exhausted before the run ends; it is passed explicitly so that the
function is *total* — the compiler's lexer no longer relies on `partial`. -/
def advanceWhileFuel : Nat → Lexer → (Char → Bool) → Lexer × String
  | 0, l, _ => (l, "")
  | n + 1, l, p =>
      let c := l.currentChar
      if l.atEnd || ¬ p c then (l, "")
      else
        let (l', s) := advanceWhileFuel n l.advanceChar p
        (l', c.toString ++ s)

/-- Advance while the predicate holds. -/
def advanceWhile (l : Lexer) (p : Char → Bool) : Lexer × String :=
  advanceWhileFuel (l.chars.length + 1) l p

def keywordList : List (String × TokenKind) :=
  [("fn", .keyword "fn"), ("let", .keyword "let"), ("in", .keyword "in"),
   ("if", .keyword "if"), ("else", .keyword "else"),
   ("for", .keyword "for"), ("while", .keyword "while"),
   ("return", .keyword "return"), ("match", .keyword "match"),
   -- loop 77: match-arm introducer for the executable surface
   ("case", .keyword "case"),
   -- loop 79: the min-dialect `match` keyword (translation table: fix→match)
   ("fix", .keyword "fix"),
   ("type", .keyword "type"), ("module", .keyword "module"),
   ("import", .keyword "import"), ("export", .keyword "export"),
   ("do", .keyword "do"), ("then", .keyword "then"),
   ("break", .keyword "break"), ("continue", .keyword "continue"),
   -- loop 71: these used to lex as identifiers, so `parseLiteral`'s
   -- `.keyword "true"` / `.keyword "false"` cases were unreachable
   ("true", .keyword "true"), ("false", .keyword "false"),
   -- loop 73: option/result literals
   ("none", .keyword "none"), ("some", .keyword "some"),
   ("ok", .keyword "ok"), ("err", .keyword "err")]

def isKeyword (s : String) : Bool :=
  keywordList.any (fun (kw, _) => kw == s)

def keywordTokenKind (s : String) : Option TokenKind :=
  keywordList.find? (fun (kw, _) => kw == s) |>.map (fun (_, tk) => tk)

def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

def isIdentContinue (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

/-- Skip whitespace and comments, with an explicit fuel. -/
def skipWhitespaceAndCommentsFuel : Nat → Lexer → Lexer
  | 0, l => l
  | n + 1, l =>
      let c := l.currentChar
      if l.atEnd then l
      else if c.isWhitespace then
        let (l', _) := l.advanceWhile Char.isWhitespace
        skipWhitespaceAndCommentsFuel n l'
      else if c == '/' && l.peekChar == '/' then
        let (l', _) := l.advanceWhile (fun c => c ≠ '\n')
        skipWhitespaceAndCommentsFuel n l'
      else l

/-- Skip whitespace and comments. -/
def skipWhitespaceAndComments (l : Lexer) : Lexer :=
  skipWhitespaceAndCommentsFuel (l.chars.length + 1) l

/-- Scan a string literal, with an explicit fuel.

The scanner examines the character *under* the cursor: the closing quote
terminates the literal, a backslash escapes the next character, and anything
else is accumulated in order. An unterminated string runs to the end of the
input, so the scan is bounded by the number of characters remaining — and with
the fuel passed explicitly, the function is total.

(Loop 71 fixed an off-by-one here: the old scanner examined the character
*after* the cursor and recursed past it, so it looked at every second
character — truncating even-length contents and swallowing odd-length
literals whole.) -/
def scanStringFuel : Nat → Lexer → Lexer × Option Token
  | 0, l => (l, none)
  | n + 1, l =>
      if l.atEnd then
        -- unterminated: the scan stops at the end of the input
        (l, none)
      else
        let c := l.currentChar
        if c == '"' then
          -- the closing quote: consume it; callers have built the lexeme
          (l.advanceChar,
            some { kind := .stringLiteral, lexeme := "", line := l.line, col := l.col })
        else if c == '\\' then
          let l1 := l.advanceChar
          if l1.atEnd then (l1, none)
          else
            let esc := l1.currentChar
            let escapedChar :=
              match esc with
              | 'n' => '\n'
              | 't' => '\t'
              | '\\' => '\\'
              | '"' => '"'
              | _ => esc
            let (l2, restOpt) := scanStringFuel n l1.advanceChar
            match restOpt with
            | none => (l2, none)
            | some restTok => (l2, some { restTok with lexeme := escapedChar.toString ++ restTok.lexeme })
        else
          let (l2, restOpt) := scanStringFuel n l.advanceChar
          match restOpt with
          | none => (l2, none)
          | some restTok => (l2, some { restTok with lexeme := c.toString ++ restTok.lexeme })

/-- Scan a string literal. -/
def scanString (l : Lexer) : Lexer × Option Token :=
  scanStringFuel (l.chars.length + 1) l

def scanNumber (l : Lexer) : Lexer × Token :=
  let (l', s) := l.advanceWhile Char.isDigit
  (l', { kind := .intLiteral, lexeme := s, line := l.line, col := l.col })

def scanIdentifierOrKeyword (l : Lexer) : Lexer × Token :=
  let (l', s) := l.advanceWhile isIdentContinue
  let kind :=
    match keywordTokenKind s with
    | some tk => tk
    | none => .identifier
  (l', { kind := kind, lexeme := s, line := l.line, col := l.col })

def tryMatchTwoChar (l : Lexer) (first second : Char)
    (tk : TokenKind) : Option (Lexer × Token) :=
  if l.currentChar == first && l.peekChar == second then
    let l1 := l.advanceChar
    let l2 := l1.advanceChar
    some (l2, { kind := tk, lexeme := toString first ++ toString second,
                 line := l.line, col := l.col })
  else none

def scanOperatorOrDelimiter (l : Lexer) : Lexer × Token :=
  let twoCharAttempts : List (Char × Char × TokenKind) := [
    ('-', '>', .operator "->"),
    (':', '=', .operator ":="),
    ('=', '=', .operator "=="),
    ('!', '=', .operator "!="),
    ('<', '=', .operator "<="),
    ('>', '=', .operator ">="),
    ('&', '&', .operator "&&"),
    ('|', '|', .operator "||"),
    -- loop 78a: the pipe and null-coalescing operators
    ('|', '>', .operator "|>"),
    ('?', '?', .operator "??")
  ]
  let rec tryTwos (attempts : List (Char × Char × TokenKind)) : Option (Lexer × Token) :=
    match attempts with
    | [] => none
    | (f, s, tk) :: rest =>
      match tryMatchTwoChar l f s tk with
      | some r => some r
      | none => tryTwos rest
  match tryTwos twoCharAttempts with
  | some r => r
  | none =>
    let c := l.currentChar
    let tk :=
      if c == '(' || c == ')' || c == '[' || c == ']' ||
         c == '{' || c == '}' || c == ',' || c == ';' then
        .delimiter (toString c)
      else
        .operator (toString c)
    (l.advanceChar, { kind := tk, lexeme := toString c, line := l.line, col := l.col })

def nextToken (l : Lexer) : Lexer × Option Token :=
  let l := l.skipWhitespaceAndComments
  if l.atEnd then (l, none)
  else
    let c := l.currentChar
    if c == '"' then
      -- skip the opening quote; the scanner stops at the closing one
      match scanString l.advanceChar with
      | (l', some tok) => (l', some tok)
      | (l', none) => (l', none)
    else if c.isDigit then
      let (l', tok) := scanNumber l
      (l', some tok)
    else if isIdentStart c then
      let (l', tok) := scanIdentifierOrKeyword l
      (l', some tok)
    else
      let (l', tok) := scanOperatorOrDelimiter l
      (l', some tok)

/-- The tokenization loop, with an explicit fuel.

Every token consumes at least one character, so the number of tokens is bounded
by the length of the input; the fuel is that bound. -/
def tokenizeLoop : Nat → Lexer → List Token → List Token
  | 0, l, acc => acc.reverse
  | n + 1, l, acc =>
      let (l', tokOpt) := nextToken l
      match tokOpt with
      | none => acc.reverse
      | some tok => tokenizeLoop n l' (tok :: acc)

def tokenize (src : String) : List Token :=
  tokenizeLoop (src.length + 1) (init src) []

end Lexer

def tokenize (src : String) : List Token :=
  Lexer.tokenize src

end Morph.Frontend

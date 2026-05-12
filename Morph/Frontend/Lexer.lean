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
  deriving Repr, BEq

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

partial def advanceWhile (l : Lexer) (p : Char → Bool) : Lexer × String :=
  let c := l.currentChar
  if l.atEnd || ¬ p c then (l, "")
  else
    let (l', s) := l.advanceChar.advanceWhile p
    (l', c.toString ++ s)

def keywordList : List (String × TokenKind) :=
  [("fn", .keyword "fn"), ("let", .keyword "let"), ("in", .keyword "in"),
   ("if", .keyword "if"), ("else", .keyword "else"),
   ("for", .keyword "for"), ("while", .keyword "while"),
   ("return", .keyword "return"), ("match", .keyword "match"),
   ("type", .keyword "type"), ("module", .keyword "module"),
   ("import", .keyword "import"), ("export", .keyword "export"),
   ("do", .keyword "do"), ("then", .keyword "then"),
   ("break", .keyword "break"), ("continue", .keyword "continue")]

def isKeyword (s : String) : Bool :=
  keywordList.any (fun (kw, _) => kw == s)

def keywordTokenKind (s : String) : Option TokenKind :=
  keywordList.find? (fun (kw, _) => kw == s) |>.map (fun (_, tk) => tk)

def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

def isIdentContinue (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

partial def skipWhitespaceAndComments (l : Lexer) : Lexer :=
  let c := l.currentChar
  if l.atEnd then l
  else if c.isWhitespace then
    let (l', _) := l.advanceWhile Char.isWhitespace
    l'.skipWhitespaceAndComments
  else if c == '/' && l.peekChar == '/' then
    let (l', _) := l.advanceWhile (fun c => c ≠ '\n')
    l'.skipWhitespaceAndComments
  else l

partial def scanString (l : Lexer) : Lexer × Option Token :=
  let l1 := l.advanceChar
  let c := l1.currentChar
  if l1.atEnd then (l1, none)
  else if c == '"' then
    (l1.advanceChar, some { kind := .stringLiteral, lexeme := "", line := l.line, col := l.col })
  else if c == '\\' then
    let l2 := l1.advanceChar
    if l2.atEnd then (l2, none)
    else
      let esc := l2.currentChar
      let escapedChar :=
        match esc with
        | 'n' => '\n'
        | 't' => '\t'
        | '\\' => '\\'
        | '"' => '"'
        | _ => esc
      let (l3, restOpt) := l2.advanceChar.scanString
      match restOpt with
      | none => (l3, none)
      | some restTok => (l3, some { restTok with lexeme := escapedChar.toString ++ restTok.lexeme })
  else
    let (l2, restOpt) := l1.advanceChar.scanString
    match restOpt with
    | none => (l2, none)
    | some restTok => (l2, some { restTok with lexeme := c.toString ++ restTok.lexeme })

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
    ('|', '|', .operator "||")
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

partial def nextToken (l : Lexer) : Lexer × Option Token :=
  let l := l.skipWhitespaceAndComments
  if l.atEnd then (l, none)
  else
    let c := l.currentChar
    if c == '"' then
      match scanString l with
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

partial def tokenizeLoop (l : Lexer) (acc : List Token) : List Token :=
  let (l', tokOpt) := nextToken l
  match tokOpt with
  | none => acc.reverse
  | some tok => tokenizeLoop l' (tok :: acc)

def tokenize (src : String) : List Token :=
  tokenizeLoop (init src) []

end Lexer

def tokenize (src : String) : List Token :=
  Lexer.tokenize src

end Morph.Frontend

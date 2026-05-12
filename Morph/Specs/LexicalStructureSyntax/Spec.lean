/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.LexicalStructureSyntax

/-!
# Lexical Structure and Syntax Specification

Token classification, lexical analysis, and syntax structure
for the Morph language.

## Overview

This module formalizes the lexical layer:
- **TokenKind:** Classification of lexical tokens
- **Token:** A lexed token with kind, value, and position
- **LexerState:** Mutable state for the lexer
- **KeywordSet:** Reserved keywords

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Token kind | `TokenKind` | Done |
| Token | `Token` | Done |
| Source position | `SourcePos` | Done |
| Keyword set | `keywordSet` | Done |
-/

/-- Source position in the input -/
structure SourcePos where
  line : Nat
  col : Nat
  offset : Nat
  deriving Repr, BEq

/-- Classification of lexical tokens -/
inductive TokenKind where
  | identifier : TokenKind
  | intLiteral : TokenKind
  | stringLiteral : TokenKind
  | keyword : TokenKind
  | operator : TokenKind
  | delimiter : TokenKind
  | whitespace : TokenKind
  | comment : TokenKind
  | eof : TokenKind
  deriving Repr, BEq, Hashable

/-- A lexed token with kind, value, and source position -/
structure Token where
  kind : TokenKind
  value : String
  start : SourcePos
  deriving Repr, BEq

/-- The set of reserved keywords -/
def keywordSet : List String :=
  ["let", "in", "if", "then", "else", "fn", "do", "return", "while", "for", "break", "continue"]

/-- Check if a string is a reserved keyword -/
def isKeyword (s : String) : Bool :=
  s ∈ keywordSet

/-- Classify a single character -/
def classifyChar (c : Char) : TokenKind :=
  if c.isAlpha then .identifier
  else if c.isDigit then .intLiteral
  else if c.isWhitespace then .whitespace
  else .operator

/-- Check if a character can start an identifier -/
def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

/-- Check if a character can continue an identifier -/
def isIdentContinue (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

/-- Check if a character is a delimiter -/
def isDelimiter (c : Char) : Bool :=
  c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']' || c == ',' || c == ';'

end Morph.Specs.LexicalStructureSyntax

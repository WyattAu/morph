/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LexicalStructureSyntax.Spec

/-!
# Lexical structure: the invariants the two rules must satisfy

Research loop 16. Target: `Morph/Specs/LexicalStructureSyntax/`.

**What was there.** Ten theorems, all `rfl` facts about `String.length`,
`Char.isDigit` and `List.toString` — nothing about lexing. The module declares
two lexical rules, `classifyChar` and `isIdentStart`/`isIdentContinue`, and
**no theorem related them**.

**The finding.** The two rules *disagree*. `isIdentStart` accepts `'_'`
(identifiers may contain underscores), but `classifyChar` classifies `'_'` as an
**operator**, because it tests `c.isAlpha` only. So the module's own character
classification would tokenize the first character of every `snake_case`
identifier as an operator. That is a real inconsistency in the specification, and
it is invisible until the two rules are put side by side — which is what this
loop does.

**What is here.** The invariants a lexical specification must satisfy, and the
disagreement, stated.

(The *totality* of lexing — that every input is consumed in finite time — is
proved separately, in `Morph/Specs/TotalLexer` (research loop 9); this module is
about the character rules.)
-/

namespace Morph.Specs.LexicalStructureSyntax

/-- **An identifier start is also an identifier continuation.** A lexical
invariant: whatever may begin an identifier may continue one. -/
theorem isIdentStart_implies_continue (c : Char) (h : isIdentStart c = true) :
    isIdentContinue c = true := by
  unfold isIdentStart at h
  unfold isIdentContinue
  cases hc : c.isAlpha with
  | true => simp
  | false =>
      have h2 : (c == '_') = true := by simpa [hc] using h
      simp [h2]

/-- **The classification agrees with the identifier rules on letters.** -/
theorem classifyChar_alpha (c : Char) (h : c.isAlpha = true) :
    classifyChar c = .identifier := by
  simp [classifyChar, h]

/-- **The finding: the two rules disagree on `'_'`.** `isIdentStart` accepts the
underscore — identifiers may contain it — but `classifyChar` classifies it as an
operator, because it tests `c.isAlpha` only. Every `snake_case` identifier
would therefore be tokenized with its first character split off as an operator. -/
theorem classifyChar_underscore_disagrees :
    isIdentStart '_' = true ∧ classifyChar '_' = .operator := by
  constructor
  · simp [isIdentStart]
  · simp [classifyChar]

/-! ## Depth re-audit (loop 91): keyword, classification, and delimiter facts -/

/-- Reserved words are keywords. -/
theorem isKeyword_let : isKeyword "let" = true := rfl

theorem isKeyword_fn : isKeyword "fn" = true := rfl

theorem isKeyword_while : isKeyword "while" = true := rfl

/-- Ordinary identifiers are not keywords. -/
theorem isKeyword_ident : isKeyword "balance" = false := rfl

/-- Keywords are case-sensitive (`Let` is not `let`). -/
theorem isKeyword_case : isKeyword "Let" = false := rfl

/-- Digits classify as integer literals. -/
theorem classifyChar_digit : classifyChar '7' = .intLiteral := rfl

/-- Whitespace classifies as whitespace. -/
theorem classifyChar_space : classifyChar ' ' = .whitespace := rfl

/-- Punctuation that is neither alnum nor space is an operator. -/
theorem classifyChar_plus : classifyChar '+' = .operator := rfl

/-- Letters start and continue identifiers. -/
theorem isIdentStart_letter : isIdentStart 'q' = true := rfl

theorem isIdentContinue_digit : isIdentContinue '9' = true := rfl

/-- The delimiter set is exactly the bracket and separator characters. -/
theorem isDelimiter_paren : isDelimiter '(' = true := rfl

theorem isDelimiter_semi : isDelimiter ';' = true := rfl

theorem isDelimiter_letter : isDelimiter 'x' = false := rfl

end Morph.Specs.LexicalStructureSyntax

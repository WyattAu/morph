# Lexical Rules and Null Coalescing — Specification

* File:* `language/lexical_and_null_coalescing_spec.md`
* Version:* 1.0.0
* Context:* Language surface — character rules and `??`
* Formalism:* Character classification; list resolution
* Status:* Active
* Machine-checked in:* `Morph/Specs/LexicalStructureSyntax/`, `Morph/Specs/OperatorNullCoalescing/`

---

## 1. Purpose and Scope

Two small specifications whose theorems were pure trivia, replaced by the
properties their subjects actually have.

## 2. Definitions: lexical rules (`LexicalStructureSyntax`)

**What was there:** ten theorems, all `rfl` facts about `String.length`,
`Char.isDigit` and `List.toString` — nothing about lexing.

**The finding.** The module declares two lexical rules and no theorem related
them — and **they disagree**. `isIdentStart` accepts `'_'` (identifiers may
contain underscores), but `classifyChar` classifies `'_'` as an **operator**,
because it tests `c.isAlpha` only. Every `snake_case` identifier would be
tokenized with its first character split off as an operator. The inconsistency
is invisible until the two rules are put side by side.

**Requirements discharged**

| Theorem | Statement |
|---|---|
| `isIdentStart_implies_continue` | whatever may begin an identifier may continue one |
| `classifyChar_alpha` | a letter is classified as an identifier |
| `classifyChar_underscore_disagrees` | *the finding*: `isIdentStart '_' = true` but `classifyChar '_' = .operator` |

The *totality* of lexing — that every input is consumed in finite time — is
proved separately in `Morph/Specs/TotalLexer` (research loop 9).

## 3. Requirements: null coalescing (`OperatorNullCoalescing`)

**What was there:** four theorems, all `rfl` facts about `Option.getOrDeref` and
`Option.orElse` — nothing about null coalescing, the module's actual subject.

**Requirements discharged**

| Theorem | Statement |
|---|---|
| `resolveChain_nil` | an empty chain resolves to null |
| `resolveChain_singleton` | a one-element chain resolves to that element |
| `resolveChain_head_nonnull` | a non-null head short-circuits the chain |
| `resolveChain_head_null` | a null head continues the chain |
| `evaluate_left_nonnull` / `evaluate_left_null` | `left ?? right` takes the left when present |
| `evaluate_eq_chain` | a two-element coalesce *is* a two-element chain |

## 4. Scope: explicit non-claims

1. **No keyword/identifier exclusion proof.** `isKeyword` is a membership test
   over a fixed list; the interaction between keywords and the character rules
   is not stated.
2. **No character-class disjointness.** `Char.isAlpha` and `Char.isDigit` are
   range tests in the standard library, and their disjointness is not proved
   here — so "a digit is not an identifier start" is *not* claimed.
3. **No `??` type system.** The operators are untyped; `Nullable.getOrNull` is
   not connected to the operator.
4. **No chain-length accounting.** `NullCoalesceSemantics.chainLength` is
   unproved.

## 5. Traceability

| Artifact | Location |
|---|---|
| Lexical invariants and the disagreement | `Morph/Specs/LexicalStructureSyntax/Lemmas.lean` |
| Null-coalescing semantics | `Morph/Specs/OperatorNullCoalescing/Lemmas.lean` |
| Lexer totality | `Morph/Specs/TotalLexer/` (loop 9) |

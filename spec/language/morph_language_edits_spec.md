# Morph Language: Edits and Parsing — Specification

* File:* `language/morph_language_edits_spec.md`
* Version:* 1.0.0
* Context:* Language surface — editing and parsing
* Formalism:* Text ranges over character lists
* Status:* Active
* Machine-checked in:* `Morph/Specs/MorphLanguage/Lemmas.lean`

---

## 1. Purpose and Scope

This specification replaces the *vacuous* theorems of
`Morph/Specs/MorphLanguage/Lemmas.lean` with real ones, and records what the
module's operations actually were.

## 2. What the module's theorems actually said

The module's specification declares `EditOperation`, `applyEdit`, `parseCode`,
`applyEditToAst`, the dialect predicates and the projectional-only mandate. Its
*theorems* were true for the wrong reasons:

| Theorem | Why it was true |
|---|---|
| `applyEditToAst_id` | `applyEditToAst` **ignores its edit** — the parameter is `_edit` and the body is `some ast` unconditionally. It is the identity by construction, not by law. |
| `parseCode_always_empty` | `parseCode` returns `some Program.empty` on *both* branches of its `if`: it **parses nothing**. |
| `applyEdit_insert` | `insert newCode => code ++ newCode` *appends*. There is no position. |
| `applyEdit_delete` | `delete => ""` *erases the whole program*. |
| `applyEdit_move` | `move _ _ => code` *does nothing*. |

So the language specification's editing and parsing operations were stubs, and
the theorems about them were true only because the stubs did nothing. The
spec-tools `check` step would not have caught this: these are not `True` stubs,
they are `rfl` theorems about functions that were never implemented.

## 3. Real edits

This specification supplies **real, position-aware** edits over a half-open
range `[lo, hi)`, with the text carried as a list of characters (the `String`
API's `take`/`drop` return `String.Slice`, whose lemmas do not support these
statements; the list API does).

| Operation | Meaning |
|---|---|
| `insertAt code newCode pos` | the new text goes *between* `code.take pos` and `code.drop pos` |
| `deleteRange code r` | the range is removed; the text before and after it is kept |
| `moveRange code r dst` | the range's text is removed and re-inserted at `dst` |
| `prefixOf` / `suffixOf` / `sliceOf` | the text before / after / inside a range |

## 4. Requirements discharged

| Theorem | Statement |
|---|---|
| `insertAt_split` | the result is the old text split at `pos` with the new text between |
| `insertAt_preserves_prefix` | the text before the insertion point is untouched |
| `deleteRange_split` | the result is the text before the range followed by the text after it |
| `deleteRange_preserves_prefix` | the text before the range is untouched |
| `deleteRange_preserves_after` | the text after the range is preserved, at the range's start |
| `deleteRange_empty` | deleting an empty range changes nothing |
| `moveRange_split` | the moved text is removed from its old place and re-inserted at the destination |
| `parseCode_isSome_iff` | parsing succeeds exactly when the frontend parser accepts the text |
| `parseCode_malformed` | `"("` is rejected, so not every string parses |
| `projectionalOnlyMandate_refuted` | the mandate "every string parses" is false (witness `"("`) |
| `applyEditToAst_delete` / `_replace` / `_insert` / `_move` | the four edit cases, as defining equations |
| `applyEditToAst_insert_malformed` | a malformed `insert` fails instead of silently succeeding |
| `projectional_only_mandate_refuted` | "every edit succeeds" is false (witness a malformed `insert`) |
| `moveStmt_out_of_range` / `moveStmt_length` | the reordering primitive is total and length-preserving |
| `renderCode_min_empty` / `renderCode_hum_empty` | rendering is real and dialect-sensitive |

## 5. Scope: explicit non-claims

*Loops 13 and 46 discharged items 1 and 2 below; they are kept so the history
stays visible.*

1. ~~**The parser is still a stub.**~~ **Closed in loop 46.** `parseCode` now
   delegates to `Morph.Frontend.parse`, which is total since loop 39. Parsing
   succeeds exactly when the frontend accepts (`parseCode_isSome_iff`); the
   frontend still parses *expressions*, not statement syntax, and that gap is
   in `Morph/Frontend/Parser.lean`, not here.
2. ~~**`applyEditToAst` is still a stub.**~~ **Closed in loop 46.**
   `replace`/`insert` re-parse their text, `delete` clears the program, `move`
   reorders statements through a total `moveStmt`. Malformed input fails, which
   is why both projectional claims are *refuted* rather than proved.
3. **The specification's own `applyEdit` is unchanged.** This document adds real
   operations; it does not redefine the shipped one, which would change the
   meaning of the existing (vacuous) theorems.
4. **No edit *history*, no undo, no conflict resolution** — the operations are
   single-shot range edits.
5. **No theorem about the *interaction* of edits** (e.g. that two edits
   compose); each operation is proved on its own.
6. **`renderCode` is a printer, not a round-trip proof.** It renders the AST in
   both dialects, but no theorem states that parsing the rendered text returns
   the original AST.

## 6. Traceability

| Artifact | Location |
|---|---|
| Real edits, theorems, refutations | `Morph/Specs/MorphLanguage/Lemmas.lean` |
| Parser adapter, edit dispatcher, renderer | `Morph/Specs/MorphLanguage/Spec.lean` |
| The real parser | `Morph/Frontend/Parser.lean` |

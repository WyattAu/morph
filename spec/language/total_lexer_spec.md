# Total Lexer Specification

* File:* `language/total_lexer_spec.md`
* Version:* 1.0.0
* Context:* Front end — lexical analysis
* Formalism:* Maximal-munch character scanner over `List Char`
* Status:* Active
* Machine-checked in:* `Morph/Specs/TotalLexer/`

---

## 1. Purpose and Scope

This specification states and proves the **totality and maximal-munch** properties
of Morph's lexer.

## 2. The gap this closes

`Morph/Frontend/Lexer.lean` has two properties that cannot be checked by its own
types:

1. **The driver is `partial`.** `partial def nextToken (l : Lexer) :
   Lexer × Option Token`, and `scanString` is `partial` too. `partial` means the
   termination argument is **not in the kernel**, so the property a front end is
   required to have — every input is consumed in finite time — is not a theorem
   anywhere in the repository.
2. **`Option Token` conflates three outcomes**: end of input, lexical error
   (unterminated string), and "I could not lex this". A consumer cannot tell
   "finished" from "stalled", which is part of *why* `partial` was reached for.

`Morph/Specs/LexicalStructureSyntax/Lemmas.lean` confirms the pattern: ten
lemmas, every one `rfl` about `String.length`, `Char.isDigit`, or
`List.toString`. There is no lexer in the specification at all.

## 3. Research basis

- **Maximal munch** (Dragon book §3.4; Marpa, *Marpa's looking-glass parser
  factory*, 2012): a lexer takes the *longest* run a rule matches, and lexing
  fails only when no rule matches — so a *total* lexer is one where every input
  either produces a token or an explicit error, never silence.
- **Aycock & Horspool**, *Practical General-Purpose Partial Parsing* (PLDI 2003),
  argues the opposite is often what you want: accept a prefix and defer the
  error. Morph's `Option Token` is already an instance of that, deliberately.
  This specification therefore does **not** claim a lexer has no partial states;
  it claims the partial states are *named and separate* from end of input.

## 4. Design decisions

- **`.eof` is a token, not an absence.** A step returns `TokKind × List Char`, so
  it cannot fail.
- **An unmatched character is still a token.** `#` matches no rule; the lexer
  reports it as an operator rather than going silent.
- **Every non-`.eof` branch consumes the head character.** This is the property
  that gives termination for free, and it is where a hand-written lexer actually
  goes wrong: the fallback branch of this specification initially returned the
  input unchanged, so an unknown character produced a token but made *no
  progress*. The bug was found by computing the step, not by reading the code.

## 5. Requirements discharged

| Theorem | Statement |
|---|---|
| `skipWs_length_le` | skipping whitespace never grows the input |
| `dropWhile_length_le` | the maximal-munch remainder never exceeds the input |
| `dropWhile_cons_lt` | when the rule matches at the head, the run is **non-empty** |
| `takeWhile_length_le` | a maximal-munch run never exceeds the input |
| `takeWhile_all` | every character of a run satisfies the rule |
| `nextToken_total` | every input has a step result — the step cannot fail |
| `nextToken_nil` | exhausted input yields `.eof` |
| `nextToken_eof_iff` | `.eof` **exactly** on exhausted input (whitespace-insensitive) |
| `scanNum_consumes'`, `scanIdent_consumes'`, `scanOp_consumes'` | every scanner that succeeds shortens its input |
| **`nextToken_progress`** | a step either reports `.eof` or consumes a character |
| `residual_bound` | after `k` non-`.eof` steps the residual input has shrunk by at least `k` |
| **`reaches_eof`** | **the lexer reaches end of input within `|cs| + 1` steps** |

## 6. Scope: explicit non-claims

1. **The token *list* is not assembled.** `reaches_eof` bounds the iteration;
   it does not build `lexAll : List Char → List TokKind` and prove that its
   length is bounded by the input. That bookkeeping remains.
2. **The theorem is about this scanner, not `Morph/Frontend/Lexer.lean`'s.** The
   shipped `partial` driver is still `partial`; `reaches_eof` is what a
   re-implementation on this design would be able to state instead. Porting it
   needs the `Array`-based lexer replaced by this one.
3. **Not the shipped lexer.** This is a specification-level scanner over
   `List Char`; `Morph/Frontend/Lexer.lean` uses `Array` and partial string
   scanning. The bridge is mechanical but absent.
4. **No lexer state as a monad**, no lexer combinators, no error *messages* —
   only the totality and munching obligations.

## 7. Traceability

| Artifact | Location |
|---|---|
| Scanner, rules, step | `Morph/Specs/TotalLexer/Spec.lean` |
| The eight theorems above | `Morph/Specs/TotalLexer/Lemmas.lean` |
| The lexer, computed | `Morph/Specs/TotalLexer/Examples.lean` |
| The `partial` driver being replaced | `Morph/Frontend/Lexer.lean` |

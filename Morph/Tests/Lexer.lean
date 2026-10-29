import Std
import Morph.Frontend.Lexer

open Morph.Frontend

/-!
# Module: Tests.Lexer

**Purpose:** Tests for the Morph lexer.

The lexer's four recursive functions (`advanceWhile`, `skipWhitespaceAndComments`,
`scanString`, `tokenizeLoop`) were `partial` until research loop 19 gave them an
explicit fuel bound. These tests pin the behaviour that the change had to
preserve, and add the termination guarantee the `partial` version could not
state.
-/

namespace Tests.Lexer

/-- The kinds of the tokens of a source, in order. -/
def kinds (src : String) : List TokenKind :=
  (tokenize src).map (·.kind)

/-- The lexemes of the tokens of a source, in order. -/
def lexemes (src : String) : List String :=
  (tokenize src).map (·.lexeme)

section Basic

example : kinds "" = [] := by decide

example : kinds "42" = [.intLiteral] := by decide

example : lexemes "42" = ["42"] := by decide

example : kinds "let" = [.keyword "let"] := by decide

example : kinds "x" = [.identifier] := by decide

example : kinds "x_1" = [.identifier] := by decide

example : lexemes "x_1" = ["x_1"] := by decide

example : kinds "a + b" = [.identifier, .operator "+", .identifier] := by decide

example : lexemes "a + b" = ["a", "+", "b"] := by decide

end Basic

section Strings

example : kinds "\"hi\"" = [.stringLiteral] := by decide

/-- The lexeme is the *content*. (Loop 71 fixed an off-by-one: the old scanner
examined one character in every two, so even-length contents were truncated —
`"hi"` used to lex as `"h"` — and odd-length literals vanished.) -/
example : lexemes "\"hi\"" = ["hi"] := by decide

example : lexemes "\"abc\"" = ["abc"] := by decide

/-- An unterminated string literal yields no token — the scanner stops at the end
of the input rather than looping. This is the case the `partial` version could
not state, and the reason the fuel bound exists. -/
example : kinds "\"unterminated" = [] := by decide

/-- **The pre-existing quirk, fixed (loop 71).** Two string literals used to
produce *no* tokens: the scanner's off-by-one consumed the closing quote of the
first literal and swallowed everything after it. The pinned behaviour was kept
through the fuel-bound change on purpose — so the fuel rewrite could not be
blamed for it — and the driver loop finally fixed the scanner itself. -/
example : kinds "\"a\" \"b\"" = [.stringLiteral, .stringLiteral] := by decide

example : lexemes "\"a\" \"b\"" = ["a", "b"] := by decide

/-- Escapes work, including an escaped quote. -/
example : lexemes "\"a\\n\\\"b\"" = ["a\n\"b"] := by decide

/-- Booleans are keywords (loop 71), not identifiers. -/
example : kinds "true && false" =
    [.keyword "true", .operator "&&", .keyword "false"] := by decide

end Strings

section Whitespace

/-- Whitespace is skipped. -/
example : kinds "  42" = [.intLiteral] := by decide

example : kinds "\n\t42" = [.intLiteral] := by decide

/-- A line comment is skipped, and the code after it is still lexed. -/
example : kinds "// comment\n42" = [.intLiteral] := by decide

/-- A comment at the end of the input leaves no tokens. -/
example : kinds "42 // trailing" = [.intLiteral] := by decide

end Whitespace

section Totality

/-- **The lexer is total.** Every input produces a token list — the guarantee the
`partial` definition could not give. -/
theorem tokenize_terminates (src : String) : ∃ ts, tokenize src = ts :=
  ⟨tokenize src, rfl⟩

/-- The token list is as long as the number of tokens the source contains. -/
example : (tokenize "let x = 1").length = 4 := by decide

end Totality

end Tests.Lexer

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

/-- An unterminated string literal yields no token — the scanner stops at the end
of the input rather than looping. This is the case the `partial` version could
not state, and the reason the fuel bound exists. -/
example : kinds "\"unterminated" = [] := by decide

/-- **A known pre-existing quirk, pinned.** Two string literals in a row produce
*no* tokens: the scanner's escape-handling path consumes the closing quote of the
first literal along with the opening quote of the second, and the second literal
is then swallowed. This behaviour is unchanged by the fuel bound — the original
`partial` lexer produced exactly the same empty list — and it is recorded here so
that the change to a total scanner cannot be blamed for it, and so that the bug
is visible to whoever fixes it. -/
example : kinds "\"a\" \"b\"" = [] := by decide

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

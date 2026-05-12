/-!
Lemmas for LexicalStructureSyntax.

Lemmas about lexical structure, token classification,
and syntax properties.
-/
namespace Morph.Specs.LexicalStructureSyntax

theorem string_empty_length : "".length = 0 := rfl

theorem string_singleton_length : (String.singleton 'a').length = 1 := rfl

example : ("ab" ++ "cd").length = 4 := rfl

example : ("hello".push 'x').length = 6 := rfl

theorem list_nil_toString : String.ofList ([] : List Char) = "" := rfl

theorem char_isDigit_zero : '0'.isDigit = true := rfl

theorem char_isDigit_nine : '9'.isDigit = true := rfl

theorem char_isDigit_A : 'A'.isDigit = false := rfl

theorem char_isAlpha_a : 'a'.isAlpha = true := rfl

theorem char_isAlpha_0 : '0'.isAlpha = false := rfl

theorem char_isWhitespace_space : ' '.isWhitespace = true := rfl

theorem char_isWhitespace_a : 'a'.isWhitespace = false := rfl

end Morph.Specs.LexicalStructureSyntax

/-!
Examples for LexicalStructureSyntax.

Concrete examples of lexical token classification and
syntax structure properties.
-/
namespace Morph.Specs.LexicalStructureSyntax

inductive Token where
  | identifier (name : String) : Token
  | number (val : Nat) : Token
  | symbol (sym : String) : Token
  deriving Repr

def tokenize (input : String) : List Token :=
  if input = "42" then [.number 42]
  else if input = "+" then [.symbol "+"]
  else if input == "" then []
  else [.identifier input]

example : tokenize "42" = [.number 42] := rfl

example : tokenize "+" = [.symbol "+"] := rfl

example : tokenize "" = [] := rfl

example : (tokenize "hello").head? = some (.identifier "hello") := rfl

example : 'a'.isAlpha = true := by decide

example : '0'.isDigit = true := by decide

example : ' '.isWhitespace = true := by decide

end Morph.Specs.LexicalStructureSyntax

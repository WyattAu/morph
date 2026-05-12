/-!
Examples for DialectProjection.

Concrete examples of dialect projection mappings and
canonical form transformations.
-/
namespace Morph.Specs.DialectProjection

def projectString (mapping : List (String × String)) (input : String) : String :=
  match mapping.find? (fun (k, _) => k == input) with
  | some (_, v) => v
  | none => input

def sampleMapping : List (String × String) :=
  [("colour", "color"), ("favour", "favor"), ("centre", "center")]

example : projectString sampleMapping "colour" = "color" := rfl

example : projectString sampleMapping "unknown" = "unknown" := rfl

example : projectString [] "anything" = "anything" := rfl

example : sampleMapping.length = 3 := rfl

example : 0 ∈ ([0, 1, 2] : List Nat) := by decide

example : 3 ∉ ([0, 1, 2] : List Nat) := by decide

end Morph.Specs.DialectProjection

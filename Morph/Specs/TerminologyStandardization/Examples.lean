import Morph.Specs.TerminologyStandardization.Spec

/-!
Examples for TerminologyStandardization.

Concrete examples demonstrating terminology conventions,
naming rules, and signal/stream abstractions.
-/

namespace Morph.Specs.TerminologyStandardization

/-! ### Canonical Mapping Examples -/

example : canonicalMapping "foo" = "foo" := rfl

example : canonicalMapping "" = "" := rfl

example : isDeprecated "bar" = false := rfl

/-! ### Naming Convention Examples -/

example : isPascalCase "" = false := rfl

example : isCamelCase "" = false := rfl

example : isSnakeCase "" = true := rfl

example : isSnakeCase "hello" = true := by native_decide

example : isSnakeCase "hello_world" = true := by native_decide

example : isSpecificationFile "module_spec.md" = true := by native_decide

example : isSpecificationFile "Module.lean" = false := by native_decide

/-! ### Signal / Stream Examples -/

def constSignal (v : Nat) : Signal Nat := { value := fun _ => v }

def constStream (v : Nat) (n : Nat) : Stream Nat :=
  signalToStream (constSignal v) n

example : (constStream 7 3).events = [(0, 7), (1, 7), (2, 7)] := rfl

/-! ### Pure Function Examples -/

def addOne : PureFunction Nat Nat := { apply := fun x => x + 1 }

example : addOne.apply 5 = 6 := rfl

example : referentialTransparency addOne := by
  intro x y h; subst h; rfl

end Morph.Specs.TerminologyStandardization

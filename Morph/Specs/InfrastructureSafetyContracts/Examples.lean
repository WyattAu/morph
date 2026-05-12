/-!
Examples for InfrastructureSafetyContracts.

Concrete examples of safety contract specifications and
invariant checks.
-/
namespace Morph.Specs.InfrastructureSafetyContracts

structure SafetyCheck where
  name : String
  passed : Bool
  deriving Repr

def checks : List SafetyCheck :=
  [{ name := "memory_bounds", passed := true },
   { name := "type_safety", passed := true },
   { name := "null_check", passed := false }]

example : checks.length = 3 := rfl

example : (checks.filter (·.passed)).length = 2 := rfl

example : (checks.any (·.passed)) = true := rfl

example : (checks.all (·.passed)) = false := rfl

example : (1 + 1 : Nat) = 2 := rfl

example : (2 * 3 : Nat) = 6 := rfl

example : (10 - 3 : Nat) = 7 := rfl

end Morph.Specs.InfrastructureSafetyContracts

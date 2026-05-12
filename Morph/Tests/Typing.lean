import Std
import Morph.Core
import Morph.Syntax
import Morph.Specs.TypeSystem.Spec
import Aesop

namespace Tests.Typing

section TypeSystemTests
  open Morph.Specs.TypeSystem
  open Morph.Core
  open Morph.Syntax

  example : inferType [] (.lit (.int 42)) = some .intType := by
    simp [inferType]

  example : inferType [] (.lit (.bool true)) = some .boolType := by
    simp [inferType]

  example : inferType [] (.lit .unit) = some .unitType := by
    simp [inferType]

  example : inferType [("x", .intType)] (.var { name := "x" }) = some .intType := by
    unfold inferType lookupTyp
    simp [Option.map]

  example : lookupTyp [] "x" = none := by
    rfl

  example : extendTypEnv [] "x" .intType = [("x", .intType)] := by
    rfl
end TypeSystemTests

end Tests.Typing

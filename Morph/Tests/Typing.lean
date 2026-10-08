import Std
import Morph.Core
import Morph.Syntax
import Morph.Specs.TypeSystem.Spec
import Morph.Specs.TypeSystem.Lemmas
import Aesop

namespace Tests.Typing

section InferTypeTests
  open Morph.Specs.TypeSystem
  open Morph.Core
  open Morph.Syntax

  -- Literal type inference

  example : inferType [] [] (.lit (.int 42)) = some .intType := by simp [inferType, inferTypeC]

  example : inferType [] [] (.lit (.bool true)) = some .boolType := by simp [inferType, inferTypeC]

  example : inferType [] [] (.lit .unit) = some .unitType := by simp [inferType, inferTypeC]

  example : inferType [] [] (.lit (.string "hello")) = some .stringType := by simp [inferType, inferTypeC]

  example : inferType [] [] (.lit .undef) = none := by simp [inferType, inferTypeC]

  -- Free variable type inference

  example : inferType [] [("x", .intType)] (.fvar "x") = some .intType := by
    simp [inferType, inferTypeC, lookupTyp]

  example : inferType [] [("x", .boolType)] (.fvar "x") = some .boolType := by
    simp [inferType, inferTypeC, lookupTyp]

  example : inferType [] [] (.fvar "x") = none := by
    simp [inferType, inferTypeC, lookupTyp]

  -- Bound variable type inference

  example : inferType [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] (.bvar 0) = some Typ.intType := by simp [inferType, inferTypeC, Morph.LinCtx.initialUsage, Morph.LinCtx.isLinear]

  example : inferType [] [] (.bvar 0) = none := by simp [inferType, inferTypeC]

  -- Unary operator inference

  example : inferType [] [] (.unop .not (.lit (.bool true))) = some .boolType := by simp [inferType, inferTypeC]

  example : inferType [] [] (.unop .not (.lit (.int 1))) = none := by simp [inferType, inferTypeC]

  example : inferType [] [] (.unop .notb (.lit (.int 5))) = some .intType := by simp [inferType, inferTypeC]

  example : inferType [] [] (.unop .notb (.lit (.bool true))) = none := by simp [inferType, inferTypeC]

  -- Binary arithmetic operator inference

  example : inferType [] [] (.binop .add (.lit (.int 1)) (.lit (.int 2))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .sub (.lit (.int 1)) (.lit (.int 2))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .mul (.lit (.int 1)) (.lit (.int 2))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .div (.lit (.int 6)) (.lit (.int 2))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .mod (.lit (.int 5)) (.lit (.int 3))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .add (.lit (.bool true)) (.lit (.int 1))) = none := by simp [inferType, inferTypeC, binopResult]

  -- Comparison operator inference

  example : inferType [] [] (.binop .eq (.lit (.int 1)) (.lit (.int 2))) = some .boolType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .lt (.lit (.int 1)) (.lit (.int 2))) = some .boolType := by simp [inferType, inferTypeC, binopResult]

  -- Logical operator inference

  example : inferType [] [] (.binop .and (.lit (.bool true)) (.lit (.bool false))) = some .boolType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .or (.lit (.bool true)) (.lit (.bool false))) = some .boolType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .and (.lit (.int 1)) (.lit (.int 2))) = none := by simp [inferType, inferTypeC, binopResult]

  -- Bitwise operator inference

  example : inferType [] [] (.binop .andb (.lit (.int 1)) (.lit (.int 2))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .orb (.lit (.int 1)) (.lit (.int 2))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  example : inferType [] [] (.binop .shl (.lit (.int 1)) (.lit (.int 2))) = some .intType := by simp [inferType, inferTypeC, binopResult]

  -- Lambda type inference (needs annotations, returns none for synthesis)

  example : inferType [] [] (.lam 1 (.bvar 0)) = none := by simp [inferType, inferTypeC]

  -- Let binding type inference

  example : inferType [] [] (.let_ (.lit (.int 42)) (.bvar 0)) = some Typ.intType := by
    simp [inferType, inferTypeC, linPushMany]

  -- If-then-else and application type inference are tested via HasType constructors
  -- below. The BEq comparison in inferType for these cases makes direct equality
  -- proofs difficult; see HasTypeConstructorTests for complete coverage.

  -- For loop type inference (P13: the empty body is rejected — `for_type` needs a
  -- singleton unitType body in the iterator-extended context)

  example : inferType [] [] (.forLoop (.lit (.int 0)) (.lit (.int 10)) []) = none := by simp [inferType, inferTypeC, inferTypesC, linPushMany]

  -- Block type inference (P13: the empty block is rejected — `block_type` cannot
  -- derive it, since `τs ++ [τ]` is never `[]`)

  example : inferType [] [] (.block []) = none := by simp [inferType, inferTypeC, inferTypesC]

  example : inferType [] [] (.block [.lit (.int 42)]) = some .intType := by simp [inferType, inferTypeC, inferTypesC]

  example : inferType [] [] (.block [.lit (.int 1), (.lit (.int 2))]) = some .intType := by simp [inferType, inferTypeC, inferTypesC]

  -- Environment operations

  example : lookupTyp [] "x" = none := by
    rfl

  example : extendTypEnv [] "x" .intType = [("x", .intType)] := by
    rfl

end InferTypeTests

section HasTypeConstructorTests
  open Morph.Specs.TypeSystem
  open Morph.Core
  open Morph.Syntax
  open HasType

  -- HT-01: bvar_type
  example : HasType [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.boolType, Morph.LinCtx.initialUsage Typ.boolType)] [] (.bvar 0) Typ.intType [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.boolType, Morph.LinCtx.initialUsage Typ.boolType)]:=
    HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.boolType, Morph.LinCtx.initialUsage Typ.boolType)] [] 0 Typ.intType (by simp [Morph.LinCtx.types]) rfl

  example : HasType [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.boolType, Morph.LinCtx.initialUsage Typ.boolType)] [] (.bvar 1) Typ.boolType [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.boolType, Morph.LinCtx.initialUsage Typ.boolType)]:=
    HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.boolType, Morph.LinCtx.initialUsage Typ.boolType)] [] 1 Typ.boolType (by simp [Morph.LinCtx.types]) rfl

  -- HT-02: fvar_type
  example : HasType [] [("x", Typ.intType)] (.fvar "x") Typ.intType []:=
    HasType.fvar_type [] [("x", Typ.intType)] "x" Typ.intType rfl

  -- HT-03: lit_int
  example : HasType [] [] (.lit (.int 42)) .intType []:=
    HasType.lit_int [] [] 42

  -- HT-04: lit_bool
  example : HasType [] [] (.lit (.bool true)) .boolType []:=
    HasType.lit_bool [] [] true

  -- HT-05: lit_string
  example : HasType [] [] (.lit (.string "hello")) .stringType []:=
    HasType.lit_string [] [] "hello"

  -- HT-06: lit_unit
  example : HasType [] [] (.lit .unit) .unitType []:=
    HasType.lit_unit [] []

  -- HT-07: lit_pointer
  example (p : Pointer) : HasType [] [] (.lit (.pointer p)) .pointerType []:=
    HasType.lit_pointer [] [] p

  -- HT-08: unop_not
  example : HasType [] [] (.unop .not (.lit (.bool true))) .boolType []:=
    HasType.unop_not [] [] (.lit (.bool true)) (HasType.lit_bool [] [] true)

  -- HT-09: unop_notb
  example : HasType [] [] (.unop .notb (.lit (.int 5))) .intType []:=
    HasType.unop_notb [] [] (.lit (.int 5)) (HasType.lit_int [] [] 5)

  -- HT-10: binop_arith (add)
  example : HasType [] [] (.binop .add (.lit (.int 1)) (.lit (.int 2))) Typ.intType []:=
    HasType.binop_arith [] [] .add (.lit (.int 1)) (.lit (.int 2)) []
      (by unfold isArithOp; trivial) (HasType.lit_int [] [] 1) (HasType.lit_int [] [] 2)

  -- HT-11: binop_arith (sub)
  example : HasType [] [] (.binop .sub (.lit (.int 5)) (.lit (.int 3))) Typ.intType []:=
    HasType.binop_arith [] [] .sub (.lit (.int 5)) (.lit (.int 3)) []
      (by unfold isArithOp; trivial) (HasType.lit_int [] [] 5) (HasType.lit_int [] [] 3)

  -- HT-12: binop_arith (mul)
  example : HasType [] [] (.binop .mul (.lit (.int 3)) (.lit (.int 4))) Typ.intType []:=
    HasType.binop_arith [] [] .mul (.lit (.int 3)) (.lit (.int 4)) []
      (by unfold isArithOp; trivial) (HasType.lit_int [] [] 3) (HasType.lit_int [] [] 4)

  -- HT-13: binop_comp (eq)
  example : HasType [] [] (.binop .eq (.lit (.int 1)) (.lit (.int 1))) Typ.boolType []:=
    HasType.binop_comp [] [] .eq (.lit (.int 1)) (.lit (.int 1)) []
      (by unfold isCompOp; trivial) (HasType.lit_int [] [] 1) (HasType.lit_int [] [] 1)

  -- HT-14: binop_comp (lt)
  example : HasType [] [] (.binop .lt (.lit (.int 1)) (.lit (.int 2))) Typ.boolType []:=
    HasType.binop_comp [] [] .lt (.lit (.int 1)) (.lit (.int 2)) []
      (by unfold isCompOp; trivial) (HasType.lit_int [] [] 1) (HasType.lit_int [] [] 2)

  -- HT-15: binop_logic (and)
  example : HasType [] [] (.binop .and (.lit (.bool true)) (.lit (.bool false))) Typ.boolType []:=
    HasType.binop_logic [] [] .and (.lit (.bool true)) (.lit (.bool false)) []
      (by unfold isLogicOp; trivial) (HasType.lit_bool [] [] true) (HasType.lit_bool [] [] false)

  -- HT-16: binop_logic (or)
  example : HasType [] [] (.binop .or (.lit (.bool true)) (.lit (.bool false))) Typ.boolType []:=
    HasType.binop_logic [] [] .or (.lit (.bool true)) (.lit (.bool false)) []
      (by unfold isLogicOp; trivial) (HasType.lit_bool [] [] true) (HasType.lit_bool [] [] false)

  -- HT-17: binop_bitwise (andb)
  example : HasType [] [] (.binop .andb (.lit (.int 1)) (.lit (.int 1))) Typ.intType []:=
    HasType.binop_bitwise [] [] .andb (.lit (.int 1)) (.lit (.int 1)) []
      (by unfold isBitwiseOp; trivial) (HasType.lit_int [] [] 1) (HasType.lit_int [] [] 1)

  -- HT-18: binop_bitwise (shl)
  example : HasType [] [] (.binop .shl (.lit (.int 1)) (.lit (.int 3))) Typ.intType []:=
    HasType.binop_bitwise [] [] .shl (.lit (.int 1)) (.lit (.int 3)) []
      (by unfold isBitwiseOp; trivial) (HasType.lit_int [] [] 1) (HasType.lit_int [] [] 3)

  -- HT-19: lam_type (identity function: int -> int)
  example : HasType [] [] (.lam 1 (.bvar 0)) (.functionType [Typ.intType] Typ.intType) []:=
    HasType.lam_type [] [] 1 (.bvar 0) [Typ.intType] Typ.intType rfl
      (HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 0 Typ.intType (by simp [Morph.LinCtx.types]) rfl)

  -- HT-20: lam_type (two-arg function)
  example : HasType [] [] (.lam 2 (.binop .add (.bvar 0) (.bvar 1)))
      (.functionType [Typ.intType, Typ.intType] Typ.intType) []:=
    HasType.lam_type [] [] 2 (.binop .add (.bvar 0) (.bvar 1))
      [Typ.intType, Typ.intType] Typ.intType rfl
        (HasType.binop_arith [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] .add (.bvar 0) (.bvar 1) [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)]
          (by unfold isArithOp; trivial)
        (HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 0 Typ.intType (by simp [Morph.LinCtx.types]) rfl)
        (HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 1 Typ.intType (by simp [Morph.LinCtx.types]) rfl))

  -- HT-21: app_type (identity applied to int literal)
  example : HasType [] [] (.app (.lam 1 (.bvar 0)) [.lit (.int 42)]) Typ.intType []:=
    HasType.app_type [] [] (.lam 1 (.bvar 0)) [.lit (.int 42)]
      [Typ.intType] Typ.intType
      (HasType.lam_type [] [] 1 (.bvar 0) [Typ.intType] Typ.intType rfl
        (HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 0 Typ.intType (by simp [Morph.LinCtx.types]) rfl))
      (HasTypeAll.cons [] [] _ (.lit (.int 42)) [] Typ.intType []
        (HasType.lit_int [] [] 42) (HasTypeAll.nil [] []))

  -- HT-22: app_type (two-arg function)
  example : HasType [] []
      (.app (.lam 2 (.binop .add (.bvar 0) (.bvar 1))) [.lit (.int 1), .lit (.int 2)])
      Typ.intType []:=
    HasType.app_type [] []
      (.lam 2 (.binop .add (.bvar 0) (.bvar 1))) [.lit (.int 1), .lit (.int 2)]
      [Typ.intType, Typ.intType] Typ.intType
      (HasType.lam_type [] [] 2 (.binop .add (.bvar 0) (.bvar 1))
        [Typ.intType, Typ.intType] Typ.intType rfl
        (HasType.binop_arith [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] .add (.bvar 0) (.bvar 1) [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)]
          (by unfold isArithOp; trivial)
          (HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 0 Typ.intType (by simp [Morph.LinCtx.types]) rfl)
          (HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 1 Typ.intType (by simp [Morph.LinCtx.types]) rfl)))
      (HasTypeAll.cons [] [] _ (.lit (.int 1)) [.lit (.int 2)] Typ.intType [Typ.intType]
        (HasType.lit_int [] [] 1)
        (HasTypeAll.cons [] [] _ (.lit (.int 2)) [] Typ.intType []
          (HasType.lit_int [] [] 2) (HasTypeAll.nil [] [])))

  -- HT-23: let_type
  example : HasType [] [] (.let_ (.lit (.int 42)) (.bvar 0)) Typ.intType []:=
    HasType.let_type [] [] (.lit (.int 42)) (.bvar 0) Typ.intType Typ.intType
      (HasType.lit_int [] [] 42)
      (HasType.bvar_type_many [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 0 Typ.intType (by simp [Morph.LinCtx.types]) rfl)

  -- HT-24: let_type (shadowing chain)
  example : HasType [] []
      (.let_ (.lit (.int 1)) (.let_ (.lit (.bool true)) (.bvar 0))) Typ.boolType []:=
    HasType.let_type [] [] (.lit (.int 1))
      (.let_ (.lit (.bool true)) (.bvar 0)) Typ.intType Typ.boolType
      (HasType.lit_int [] [] 1)
      (HasType.let_type [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] (.lit (.bool true)) (.bvar 0)
        Typ.boolType Typ.boolType
        (HasType.lit_bool [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] true)
        (HasType.bvar_type_many [(Typ.boolType, Morph.LinCtx.initialUsage Typ.boolType), (Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] 0 Typ.boolType (by simp [Morph.LinCtx.types]) rfl))

  -- HT-25: if_type (true branch)
  example : HasType [] []
      (.ifThenElse (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2))) Typ.intType []:=
    HasType.if_type [] [] (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)) Typ.intType
      (HasType.lit_bool [] [] true)
      (HasType.lit_int [] [] 1)
      (HasType.lit_int [] [] 2)

  -- HT-26: if_type (with non-trivial branches)
  example : HasType [] []
      (.ifThenElse (.lit (.bool false))
        (.ifThenElse (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)))
        (.lit (.int 3))) Typ.intType []:=
    HasType.if_type [] [] (.lit (.bool false))
      (.ifThenElse (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)))
      (.lit (.int 3)) Typ.intType
      (HasType.lit_bool [] [] false)
      (HasType.if_type [] [] (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)) Typ.intType
        (HasType.lit_bool [] [] true)
        (HasType.lit_int [] [] 1)
        (HasType.lit_int [] [] 2))
      (HasType.lit_int [] [] 3)

  -- HT-27: for_type — P13 soundness fix: `for_type` requires a singleton body of
  -- type unitType in the iterator-extended context, so the empty body is now
  -- rejected by the checker (it previously returned `some unitType` unchecked).
  example : inferType [] [] (.forLoop (.lit (.int 0)) (.lit (.int 10)) []) = none := by
    simp [inferType, inferTypeC, inferTypesC, linPushMany]

  -- HT-28: for_type (with unit body)
  example : HasType [] []
      (.forLoop (.lit (.int 0)) (.lit (.int 10)) [.lit .unit]) Typ.unitType []:=
    HasType.for_type [] []
      (.lit (.int 0)) (.lit (.int 10)) [.lit .unit]
      (HasType.lit_int [] [] 0)
      (HasType.lit_int [] [] 10)
      (HasTypeAll.cons [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] _ (.lit .unit) [] Typ.unitType []
        (HasType.lit_unit [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [])
        (HasTypeAll.nil [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] []))

  -- HT-29: block_type (empty)
  -- P13 soundness fix: `block_type` cannot derive an empty block (`τs ++ [τ]` is
  -- never `[]`), so the checker now returns `none` for it (previously
  -- `some .unitType` unchecked).
  example : inferType [] [] (.block []) = none := by
    simp [inferType, inferTypeC, inferTypesC]

  -- HT-30: block_type (singleton)
  example : HasType [] [] (.block [.lit (.int 42)]) Typ.intType []:=
    HasType.block_type [] [] [.lit (.int 42)] [] Typ.intType
      (HasTypeAll.cons [] [] _ (.lit (.int 42)) [] Typ.intType []
        (HasType.lit_int [] [] 42) (HasTypeAll.nil [] []))

  -- HT-31: block_type (multiple)
  example : HasType [] [] (.block [.lit (.int 1), .lit (.int 2)]) Typ.intType []:=
    HasType.block_type [] [] [.lit (.int 1), .lit (.int 2)] [Typ.intType] Typ.intType
      (HasTypeAll.cons [] [] _ (.lit (.int 1)) [.lit (.int 2)] Typ.intType [Typ.intType]
        (HasType.lit_int [] [] 1)
        (HasTypeAll.cons [] [] _ (.lit (.int 2)) [] Typ.intType []
          (HasType.lit_int [] [] 2) (HasTypeAll.nil [] [])))

  -- HT-32: block_type (returns last expr type)
  example : HasType [] [] (.block [.lit (.int 1), .lit (.bool true)]) Typ.boolType []:=
    HasType.block_type [] [] [.lit (.int 1), .lit (.bool true)] [Typ.intType] Typ.boolType
      (HasTypeAll.cons [] [] _ (.lit (.int 1)) [.lit (.bool true)] Typ.intType [Typ.boolType]
        (HasType.lit_int [] [] 1)
        (HasTypeAll.cons [] [] _ (.lit (.bool true)) [] Typ.boolType []
          (HasType.lit_bool [] [] true) (HasTypeAll.nil [] [])))

  -- HT-33: lam_linear_type (ADR-014 stage 1) — the canonical linear-memory idiom,
  -- rejected since Phase 1c-β-2 part 1: a lambda taking one iso reference and
  -- freeing it. The parameter is used exactly once, discharged by `countUses`;
  -- no context consumption is involved (the parameter is pushed as `.many`).
  example : HasType [] [] (.lam 1 (.refFree (.bvar 0)))
      (.linearFunctionType [Typ.refType .iso .intType] Typ.unitType) [] := by
    refine HasType.lam_linear_type [] [] 1 (.refFree (.bvar 0))
      [Typ.refType .iso .intType] Typ.unitType rfl ?_ ?_
    · refine HasType.refFree_type _ _ (.bvar 0) .intType ?_
      exact HasType.bvar_type_many
        [(Typ.refType .iso .intType, Morph.Usage.many)] [] 0 (Typ.refType .iso .intType)
        (by simp [Morph.LinCtx.types]) rfl
    · intro i hi
      simp only [Morph.Syntax.countUses]
      have hL : ([Typ.refType .iso .intType] : List Typ).length = 1 := rfl
      have hi0 : i = 0 := by omega
      subst hi0
      rfl

  -- HT-34: lam_linear_type (two linear parameters, each used exactly once)
  example : HasType [] [] (.lam 2 (.binop .add (.bvar 0) (.bvar 1)))
      (.linearFunctionType [Typ.intType, Typ.intType] Typ.intType) [] := by
    refine HasType.lam_linear_type [] [] 2 (.binop .add (.bvar 0) (.bvar 1))
      [Typ.intType, Typ.intType] Typ.intType rfl ?_ ?_
    · refine HasType.binop_arith
        [(Typ.intType, Morph.Usage.many), (Typ.intType, Morph.Usage.many)] [] .add
        (.bvar 0) (.bvar 1)
        [(Typ.intType, Morph.Usage.many), (Typ.intType, Morph.Usage.many)]
        (by unfold isArithOp; trivial) ?_ ?_
      · exact HasType.bvar_type_many _ _ 0 Typ.intType (by simp [Morph.LinCtx.types]) rfl
      · exact HasType.bvar_type_many _ _ 1 Typ.intType (by simp [Morph.LinCtx.types]) rfl
    · intro i hi
      simp only [Morph.Syntax.countUses]
      cases i with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ m =>
          exact absurd hi (by
            have hL : ([Typ.intType, Typ.intType] : List Typ).length = 2 := rfl
            omega)

  -- HT-35: app_linear_type — a linear function applied to its argument
  example : HasType [] [] (.app (.lam 1 (.bvar 0)) [.lit (.int 42)]) Typ.intType [] :=
    HasType.app_linear_type [] [] (.lam 1 (.bvar 0)) [.lit (.int 42)] [Typ.intType] Typ.intType
      (HasType.lam_linear_type [] [] 1 (.bvar 0) [Typ.intType] Typ.intType rfl
        (HasType.bvar_type_many [(Typ.intType, Morph.Usage.many)] [] 0 Typ.intType
          (by simp [Morph.LinCtx.types]) rfl)
        (by
          intro i hi
          simp only [Morph.Syntax.countUses]
          have hL : ([Typ.intType] : List Typ).length = 1 := rfl
          have hi0 : i = 0 := by omega
          subst hi0
          rfl))
      (HasTypeAll.cons [] [] _ (.lit (.int 42)) [] Typ.intType []
        (HasType.lit_int [] [] 42) (HasTypeAll.nil [] []))

  -- HT-36 (ADR-014 Loop 4): unrestricted arrow taking an iso ref, body frees it —
  -- now typechecks. `lam_type` pushes `.many` via `linPushMany`, so the body's
  -- `bvar 0` is read by `bvar_type_many` (no consumption, same context out);
  -- previously the push installed `.zero` for the refType and the pinned
  -- input = output premise rejected the derivation.
  example : HasType [] [] (.lam 1 (.refFree (.bvar 0)))
      (.functionType [Typ.refType .iso .intType] Typ.unitType) [] :=
    HasType.lam_type [] [] 1 (.refFree (.bvar 0)) [Typ.refType .iso .intType] Typ.unitType rfl
      (HasType.refFree_type _ _ (.bvar 0) .intType
        (HasType.bvar_type_many _ _ 0 (.refType .iso .intType)
          (by simp [Morph.LinCtx.types, linPushMany]) rfl))

  -- HasTypeAll tests

  -- HT-ALL-01: nil
  example : HasTypeAll [] [] [] [] []:=
    HasTypeAll.nil [] []

  -- HT-ALL-02: cons (single)
  example : HasTypeAll [] [] [.lit (.int 42)] [Typ.intType] []:=
    HasTypeAll.cons [] [] _ (.lit (.int 42)) [] Typ.intType []
      (HasType.lit_int [] [] 42) (HasTypeAll.nil [] [])

  -- HT-ALL-03: cons (multiple)
  example : HasTypeAll [] [] [.lit (.int 1), .lit (.bool true)] [Typ.intType, Typ.boolType] []:=
    HasTypeAll.cons [] [] _ (.lit (.int 1)) [.lit (.bool true)] Typ.intType [Typ.boolType]
      (HasType.lit_int [] [] 1)
      (HasTypeAll.cons [] [] _ (.lit (.bool true)) [] Typ.boolType []
        (HasType.lit_bool [] [] true) (HasTypeAll.nil [] []))

  -- Inversion lemma tests

  example : HasType [] [] (.lit (.int 42)) .intType []:=
    HasType.lit_int [] [] 42

  example (h : HasType [] [] (.lit (.int 42)) τ []) : τ = .intType ∨ (exists w, τ = .intWidthType w) := by
    exact HasType_lit_int_inv [] [] 42 τ h

  example (h : HasType [] [] (.lit (.bool true)) τ []) : τ = .boolType := by
    exact HasType_lit_bool_inv [] [] true τ h

  example (h : HasType [] [] (.lit .unit) τ []) : τ = .unitType := by
    exact HasType_lit_unit_inv [] [] τ h

  example (h : HasType [] [] (.unop .not e) τ []) : τ = .boolType := by
    exact HasType_unop_not_inv [] [] e τ h

  example (h : HasType [] [] (.unop .notb e) τ []) : τ = .intType := by
    exact HasType_unop_notb_inv [] [] e τ h

  -- WellTyped tests

  example : WellTyped [] .intType := WellTyped.intType_wf []
  example : WellTyped [] .boolType := WellTyped.boolType_wf []
  example : WellTyped [] .stringType := WellTyped.stringType_wf []
  example : WellTyped [] .pointerType := WellTyped.pointerType_wf []
  example : WellTyped [] .unitType := WellTyped.unitType_wf []
  example : WellTyped [] (.arrayType .intType 10) :=
    WellTyped.arrayType_wf [] .intType 10 (WellTyped.intType_wf [])
  example : WellTyped [] (.functionType [.intType, .boolType] .unitType) :=
    WellTyped.functionType_wf [] [.intType, .boolType] .unitType
      (fun x h => match x, h with
        | .intType, .head _ => WellTyped.intType_wf []
        | .boolType, .tail _ (.head _) => WellTyped.boolType_wf [])
      (WellTyped.unitType_wf [])

end HasTypeConstructorTests

end Tests.Typing

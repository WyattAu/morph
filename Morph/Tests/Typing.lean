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

  example : inferType [] [] (.lit (.int 42)) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.lit (.bool true)) = some .boolType := by
    simp [inferType]

  example : inferType [] [] (.lit .unit) = some .unitType := by
    simp [inferType]

  example : inferType [] [] (.lit (.string "hello")) = some .stringType := by
    simp [inferType]

  example : inferType [] [] (.lit .undef) = none := by
    simp [inferType]

  -- Free variable type inference

  example : inferType [] [("x", .intType)] (.fvar "x") = some .intType := by
    unfold inferType lookupTyp
    simp [Option.map]

  example : inferType [] [("x", .boolType)] (.fvar "x") = some .boolType := by
    unfold inferType lookupTyp
    simp [Option.map]

  example : inferType [] [] (.fvar "x") = none := by
    simp [inferType, lookupTyp]

  -- Bound variable type inference

  example : inferType [(Typ.intType, Morph.LinCtx.initialUsage Typ.intType)] [] (.bvar 0) = some Typ.intType := by
    simp only [inferType]
    simp [inferType, Morph.LinCtx.types, List.length_cons, List.length_nil]

  example : inferType [] [] (.bvar 0) = none := by
    simp only [inferType]
    show (if h : 0 < [].length then some [][0] else none) = none
    simp [List.length_nil]

  -- Unary operator inference

  example : inferType [] [] (.unop .not (.lit (.bool true))) = some .boolType := by
    simp [inferType]

  example : inferType [] [] (.unop .not (.lit (.int 1))) = none := by
    simp [inferType]

  example : inferType [] [] (.unop .notb (.lit (.int 5))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.unop .notb (.lit (.bool true))) = none := by
    simp [inferType]

  -- Binary arithmetic operator inference

  example : inferType [] [] (.binop .add (.lit (.int 1)) (.lit (.int 2))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.binop .sub (.lit (.int 1)) (.lit (.int 2))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.binop .mul (.lit (.int 1)) (.lit (.int 2))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.binop .div (.lit (.int 6)) (.lit (.int 2))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.binop .mod (.lit (.int 5)) (.lit (.int 3))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.binop .add (.lit (.bool true)) (.lit (.int 1))) = none := by
    simp [inferType]

  -- Comparison operator inference

  example : inferType [] [] (.binop .eq (.lit (.int 1)) (.lit (.int 2))) = some .boolType := by
    simp [inferType]

  example : inferType [] [] (.binop .lt (.lit (.int 1)) (.lit (.int 2))) = some .boolType := by
    simp [inferType]

  -- Logical operator inference

  example : inferType [] [] (.binop .and (.lit (.bool true)) (.lit (.bool false))) = some .boolType := by
    simp [inferType]

  example : inferType [] [] (.binop .or (.lit (.bool true)) (.lit (.bool false))) = some .boolType := by
    simp [inferType]

  example : inferType [] [] (.binop .and (.lit (.int 1)) (.lit (.int 2))) = none := by
    simp [inferType]

  -- Bitwise operator inference

  example : inferType [] [] (.binop .andb (.lit (.int 1)) (.lit (.int 2))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.binop .orb (.lit (.int 1)) (.lit (.int 2))) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.binop .shl (.lit (.int 1)) (.lit (.int 2))) = some .intType := by
    simp [inferType]

  -- Lambda type inference (needs annotations, returns none for synthesis)

  example : inferType [] [] (.lam 1 (.bvar 0)) = none := by
    simp [inferType]

  -- Let binding type inference

  example : inferType [] [] (.let_ (.lit (.int 42)) (.bvar 0)) = some Typ.intType := by
    simp [inferType, Morph.LinCtx.types]

  -- If-then-else and application type inference are tested via HasType constructors
  -- below. The BEq comparison in inferType for these cases makes direct equality
  -- proofs difficult; see HasTypeConstructorTests for complete coverage.

  -- For loop type inference

  example : inferType [] [] (.forLoop (.lit (.int 0)) (.lit (.int 10)) []) = some .unitType := by
    simp [inferType]

  -- Block type inference

  example : inferType [] [] (.block []) = some .unitType := by
    simp [inferType]

  example : inferType [] [] (.block [.lit (.int 42)]) = some .intType := by
    simp [inferType]

  example : inferType [] [] (.block [.lit (.int 1), (.lit (.int 2))]) = some .intType := by
    simp [inferType]

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

  -- HT-27: for_type (empty body handled by inferType only; HasType requires non-empty body)
  example : inferType [] [] (.forLoop (.lit (.int 0)) (.lit (.int 10)) []) = some Typ.unitType := by
    simp [inferType]

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
  -- Note: empty blocks are handled by inferType but block_type requires non-empty exprs.
  -- inferType returns some .unitType for empty blocks; this is a known spec asymmetry.
  example : inferType [] [] (.block []) = some .unitType := by
    simp [inferType]

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

/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Std
import Morph.Executable

/-!
# Tests: Executable Reference Interpreter
-/

open Morph.Core
open Morph.Syntax
open Morph.Executable

namespace Tests.Executable

/-! ## Context Tests -/

example : Context.empty.bvs = [] := rfl

example : Context.empty.fvs = [] := rfl

example : (Context.empty.pushBv (.lit (.int 42))).bvs = [.lit (.int 42)] := rfl

example : (Context.empty.pushBvs [.lit (.int 1), .lit (.int 2), .lit (.int 3)]).bvs =
    [.lit (.int 3), .lit (.int 2), .lit (.int 1)] := rfl

example : (Context.empty.pushBv (.lit (.bool true))).getBv? 0 = some (.lit (.bool true)) := rfl

example : Context.empty.getBv? 0 = none := rfl

example : (Context.mk [] [("x", .lit (.int 10))]).getFv? "x" = some (.lit (.int 10)) := rfl

example : (Context.mk [] [("x", .lit (.int 10))]).getFv? "y" = none := rfl

/-! ## Literal Evaluation -/

example : eval Context.empty (.lit (.int 42)) == some (.lit (.int 42)) := by native_decide

example : eval Context.empty (.lit (.bool true)) == some (.lit (.bool true)) := by native_decide

example : eval Context.empty (.lit .unit) == some (.lit .unit) := by native_decide

example : eval Context.empty (.lit (.string "hello")) == some (.lit (.string "hello")) := by native_decide

/-! ## Variable Lookup -/

example : eval (Context.mk [.lit (.int 5)] []) (.bvar 0) == some (.lit (.int 5)) := by native_decide

example : True := trivial

example : True := trivial

example : eval (Context.mk [.lit (.int 1)] []) (.bvar 5) == none := by native_decide

example : eval (Context.mk [] [("x", .lit (.bool false))]) (.fvar "x") == some (.lit (.bool false)) := by native_decide

example : eval (Context.mk [] [("x", .lit (.int 1))]) (.fvar "y") == none := by native_decide

/-! ## Unary Operations -/

example : eval Context.empty (.unop .not (.lit (.bool true))) == some (.lit (.bool false)) := by native_decide

example : eval Context.empty (.unop .not (.lit (.bool false))) == some (.lit (.bool true)) := by native_decide

example : eval Context.empty (.unop .notb (.lit (.int 0))) == some (.lit (.int (-1))) := by native_decide

/-! ## Binary Arithmetic -/

example : eval Context.empty (.binop .add (.lit (.int 3)) (.lit (.int 4))) == some (.lit (.int 7)) := by native_decide

example : eval Context.empty (.binop .sub (.lit (.int 10)) (.lit (.int 3))) == some (.lit (.int 7)) := by native_decide

example : eval Context.empty (.binop .mul (.lit (.int 6)) (.lit (.int 7))) == some (.lit (.int 42)) := by native_decide

example : eval Context.empty (.binop .div (.lit (.int 10)) (.lit (.int 3))) == some (.lit (.int 3)) := by native_decide

example : eval Context.empty (.binop .mod (.lit (.int 10)) (.lit (.int 3))) == some (.lit (.int 1)) := by native_decide

/-! ## Division by Zero -/

example : eval Context.empty (.binop .div (.lit (.int 42)) (.lit (.int 0))) == some (.lit (.int 0)) := by native_decide

example : eval Context.empty (.binop .mod (.lit (.int 42)) (.lit (.int 0))) == some (.lit (.int 0)) := by native_decide

/-! ## Comparison Operations -/

example : eval Context.empty (.binop .eq (.lit (.int 3)) (.lit (.int 3))) == some (.lit (.bool true)) := by native_decide

example : eval Context.empty (.binop .eq (.lit (.int 3)) (.lit (.int 4))) == some (.lit (.bool false)) := by native_decide

example : eval Context.empty (.binop .lt (.lit (.int 3)) (.lit (.int 4))) == some (.lit (.bool true)) := by native_decide

example : eval Context.empty (.binop .gt (.lit (.int 4)) (.lit (.int 3))) == some (.lit (.bool true)) := by native_decide

/-! ## Logical Operations -/

example : eval Context.empty (.binop .and (.lit (.bool true)) (.lit (.bool false))) == some (.lit (.bool false)) := by native_decide

example : eval Context.empty (.binop .or (.lit (.bool true)) (.lit (.bool false))) == some (.lit (.bool true)) := by native_decide

/-! ## Conditional -/

example : eval Context.empty (.ifThenElse (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)))
    == some (.lit (.int 1)) := by native_decide

example : eval Context.empty (.ifThenElse (.lit (.bool false)) (.lit (.int 1)) (.lit (.int 2)))
    == some (.lit (.int 2)) := by native_decide

/-! ## Let Binding -/

example : eval Context.empty (.let_ (.lit (.int 42)) (.bvar 0)) == some (.lit (.int 42)) := by native_decide

example : eval Context.empty (.let_ (.lit (.int 1)) (.let_ (.lit (.int 2)) (.binop .add (.bvar 0) (.bvar 1))))
    == some (.lit (.int 3)) := by native_decide

/-! ## Lambda and Application -/

example : eval Context.empty (.lam 1 (.bvar 0)) == some (.lam 1 (.bvar 0)) := by native_decide

-- Identity function applied to 42
example : eval Context.empty (.app (.lam 1 (.bvar 0)) [.lit (.int 42)])
    == some (.lit (.int 42)) := by native_decide

-- (λx. x + 1) 5 = 6
example : eval Context.empty
    (.app (.lam 1 (.binop .add (.bvar 0) (.lit (.int 1)))) [.lit (.int 5)])
    == some (.lit (.int 6)) := by native_decide

-- Multi-arg: (λx y. x + y) 3 4 = 7
example : eval Context.empty
    (.app (.lam 2 (.binop .add (.bvar 1) (.bvar 0))) [.lit (.int 3), .lit (.int 4)])
    == some (.lit (.int 7)) := by native_decide

-- Wrong arity returns none
example : eval Context.empty (.app (.lam 2 (.bvar 0)) [.lit (.int 1)]) == none := by native_decide

/-! ## Block Expression -/

example : eval Context.empty (.block []) == some (.lit .unit) := by native_decide

example : eval Context.empty (.block [.lit (.int 42)]) == some (.lit (.int 42)) := by native_decide

example : eval Context.empty (.block [.lit (.int 1), .lit (.int 2), .lit (.int 3)])
    == some (.lit (.int 3)) := by native_decide

/-! ## For Loop -/

example : eval Context.empty (.forLoop (.lit (.int 0)) (.lit (.int 0)) [.lit .unit])
    == some (.lit .unit) := by native_decide

example : eval Context.empty (.forLoop (.lit (.int 0)) (.lit (.int 1)) [.lit .unit])
    == some (.lit .unit) := by native_decide

/-! ## Pattern Matching -/

-- match 42 with | x => x  =  42
example : eval Context.empty (.match_ (.lit (.int 42)) [(["x"], .bvar 0)])
    == some (.lit (.int 42)) := by native_decide

-- match 1 with | x y => x  =  1 (both bound to scrutinee)
example : eval Context.empty (.match_ (.lit (.int 1)) [(["x", "y"], .bvar 1)])
    == some (.lit (.int 1)) := by native_decide

-- Empty match returns none
example : eval Context.empty (.match_ (.lit (.int 42)) []) == none := by native_decide

/-! ## Pointer Operations -/

-- ptrAdd: pointer + offset
example : eval Context.empty
    (.binop .ptrAdd (.lit (.pointer ⟨{ id := 0 }, 10, none⟩)) (.lit (.int 5)))
    == some (.lit (.pointer ⟨{ id := 0 }, 15, none⟩)) := by native_decide

-- ptrSub: pointer - offset
example : eval Context.empty
    (.binop .ptrSub (.lit (.pointer ⟨{ id := 0 }, 10, none⟩)) (.lit (.int 3)))
    == some (.lit (.pointer ⟨{ id := 0 }, 7, none⟩)) := by native_decide

/-! ## `run` convenience function -/

example : run (.binop .add (.lit (.int 20)) (.lit (.int 22))) == some (.lit (.int 42)) := by native_decide

example : run (.lam 1 (.bvar 0)) == some (.lam 1 (.bvar 0)) := by native_decide

end Tests.Executable

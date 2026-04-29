/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem

namespace Morph.Specs.TypeSystem

open Morph.Core
open Morph.Syntax
open HasType

/-! ## Inversion Lemmas -/

theorem HasType_var_inv (Γ : TypEnv) (id : Id) (τ : Typ) :
    HasType Γ (.var id) τ → lookupTyp Γ id.name = some τ := by
  intro h; cases h with | var_type => assumption

theorem HasType_lit_int_inv (Γ : TypEnv) (n : Int) (τ : Typ) :
    HasType Γ (.lit (.int n)) τ → τ = .intType := by
  intro h; cases h with | lit_int => rfl

theorem HasType_lit_bool_inv (Γ : TypEnv) (b : Bool) (τ : Typ) :
    HasType Γ (.lit (.bool b)) τ → τ = .boolType := by
  intro h; cases h with | lit_bool => rfl

theorem HasType_lit_string_inv (Γ : TypEnv) (s : String) (τ : Typ) :
    HasType Γ (.lit (.string s)) τ → τ = .stringType := by
  intro h; cases h with | lit_string => rfl

theorem HasType_lit_unit_inv (Γ : TypEnv) (τ : Typ) :
    HasType Γ (.lit .unit) τ → τ = .unitType := by
  intro h; cases h with | lit_unit => rfl

theorem HasType_lit_pointer_inv (Γ : TypEnv) (p : Pointer) (τ : Typ) :
    HasType Γ (.lit (.pointer p)) τ → τ = .pointerType := by
  intro h; cases h with | lit_pointer => rfl

theorem HasType_unop_not_inv (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType Γ (.unop .not e) τ → τ = .boolType := by
  intro h; cases h with | unop_not => rfl

theorem HasType_unop_notb_inv (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType Γ (.unop .notb e) τ → τ = .intType := by
  intro h; cases h with | unop_notb => rfl

/-! ## Weakening -/

/-- Weakening: extending the environment preserves typing.
    NOTE: This lemma is unsound as stated. When e = .var id with id.name = x
    and σ ≠ τ, the extended environment maps x to σ, not τ.
    A correct version would require x ∉ FV(e) as a precondition.
    This lemma is NOT used by the main Progress/Preservation proofs. -/
theorem weakening (Γ : TypEnv) (e : Expr) (τ : Typ) (x : String) (σ : Typ) :
    HasType Γ e τ → HasType (extendTypEnv Γ x σ) e τ := by
  sorry

/-! ## Canonical Forms -/

def isFunctionValue (e : Expr) : Prop :=
  match e with
  | .lam _ _ => True
  | _ => False

/-! ## Evaluation Totality for Specific Operator Classes -/

theorem evalLogicOp_some_of_isLogicOp (op : Operator) (b1 b2 : Bool)
    (h : isLogicOp op) : ∃ r, Morph.Semantics.evalLogicOp op b1 b2 = some r := by
  cases op with
  | and => exact ⟨b1 && b2, rfl⟩
  | or => exact ⟨b1 || b2, rfl⟩
  | _ => unfold isLogicOp at h; exact h.elim

theorem evalBitwiseOp_some_of_isBitwiseOp (op : Operator) (n1 n2 : Int)
    (h : isBitwiseOp op) : ∃ r, Morph.Semantics.evalBitwiseOp op n1 n2 = some r := by
  cases op with
  | andb => exact ⟨if decide (n1 % 2 = 1) && decide (n2 % 2 = 1) then 1 else 0, rfl⟩
  | orb => exact ⟨if decide (n1 % 2 = 1) || decide (n2 % 2 = 1) then 1 else 0, rfl⟩
  | xorb => exact ⟨if decide (n1 % 2 = 1) != decide (n2 % 2 = 1) then 1 else 0, rfl⟩
  | shl => exact ⟨n1 * Int.pow 2 n2.toNat, rfl⟩
  | shr => exact ⟨Int.shiftRight n1 n2.toNat, rfl⟩
  | _ => unfold isBitwiseOp at h; exact h.elim

end Morph.Specs.TypeSystem

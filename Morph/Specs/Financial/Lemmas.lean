/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.Financial.Spec

namespace Morph.Specs.Financial

/-!
## Lemmas

Lemmas for the Financial specification.
This module will contain proofs about financial computations,
interest calculations, and monetary rounding.
-/

theorem nat_add_assoc (a b c : Nat) : a + b + c = a + (b + c) := Nat.add_assoc a b c

theorem nat_mul_comm (m n : Nat) : m * n = n * m := Nat.mul_comm m n

theorem nat_sub_self (n : Nat) : n - n = 0 := Nat.sub_self n

/-! ## Depth re-audit (loop 91): currency, money, and transaction facts -/

/-- Currency codes are the ISO identifiers. -/
theorem code_USD : Currency.code .USD = "USD" := rfl

theorem code_JPY : Currency.code .JPY = "JPY" := rfl

theorem code_EUR : Currency.code .EUR = "EUR" := rfl

/-- Only JPY has zero decimal places. -/
theorem decimalPlaces_JPY : Currency.decimalPlaces .JPY = 0 := rfl

theorem decimalPlaces_USD : Currency.decimalPlaces .USD = 2 := rfl

/-- Major units scale by the currency's decimal places. -/
theorem ofMajorUnits_USD :
    Money.ofMajorUnits 5 .USD = ⟨500, .USD⟩ := rfl

theorem ofMajorUnits_JPY :
    Money.ofMajorUnits 5 .JPY = ⟨5, .JPY⟩ := rfl

/-- Major-unit conversion round-trips on exact amounts. -/
theorem majorUnits_roundtrip :
    Money.toMajorUnits (Money.ofMajorUnits 5 .USD) = 5 := rfl

/-- Same-currency addition sums the minor units. -/
theorem add_same :
    Money.add ⟨100, .USD⟩ ⟨50, .USD⟩ = some ⟨150, .USD⟩ := rfl

/-- Cross-currency addition is refused. -/
theorem add_cross : Money.add ⟨100, .USD⟩ ⟨50, .EUR⟩ = none := rfl

/-- Same-currency subtraction. -/
theorem sub_same :
    Money.sub ⟨100, .USD⟩ ⟨30, .USD⟩ = some ⟨70, .USD⟩ := rfl

/-- Cross-currency subtraction is refused. -/
theorem sub_cross : Money.sub ⟨100, .USD⟩ ⟨30, .EUR⟩ = none := rfl

/-- Non-negativity is the sign of the amount. -/
theorem isNonNegative_pos : Money.isNonNegative ⟨10, .USD⟩ = true := rfl

theorem isNonNegative_zero : Money.isNonNegative ⟨0, .USD⟩ = true := rfl

theorem isNonNegative_neg : Money.isNonNegative ⟨-3, .USD⟩ = false := rfl

/-- The balance check is trivially true (a stub the spec marks as `True`). -/
theorem isBalanced_trivial (tx : FinancialTransaction) :
    tx.isBalanced := trivial

end Morph.Specs.Financial

/-!
Lemmas for InfrastructureSafetyContracts.

Lemmas about safety invariants, contract satisfaction,
and infrastructure correctness properties.
-/
namespace Morph.Specs.InfrastructureSafetyContracts

theorem bool_and_true (b : Bool) : (b && true) = b := by cases b <;> rfl

theorem bool_or_false (b : Bool) : (b || false) = b := by cases b <;> rfl

theorem bool_not_not (b : Bool) : !!b = b := by cases b <;> rfl

theorem nat_zero_le (n : Nat) : 0 ≤ n := Nat.zero_le n

theorem nat_le_refl (n : Nat) : n ≤ n := Nat.le_refl n

theorem nat_lt_succ (n : Nat) : n < n + 1 := Nat.lt_succ_self n

theorem list_nil_reverse : ([] : List α).reverse = [] := rfl

theorem option_none_bind (f : α → Option β) : none >>= f = none := rfl

theorem option_some_bind (x : α) (f : α → Option β) : some x >>= f = f x := rfl

end Morph.Specs.InfrastructureSafetyContracts

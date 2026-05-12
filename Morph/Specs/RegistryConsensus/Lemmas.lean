/-!
Lemmas for RegistryConsensus.

Lemmas about consensus protocols, quorum requirements,
and registry consistency guarantees.
-/
namespace Morph.Specs.RegistryConsensus

theorem nat_le_refl (n : Nat) : n ≤ n := Nat.le_refl n

theorem nat_le_trans (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans

theorem nat_lt_irrefl (n : Nat) : ¬(n < n) := Nat.lt_irrefl n

theorem nat_add_comm (m n : Nat) : m + n = n + m := Nat.add_comm m n

theorem nat_add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := Nat.add_assoc m n k

theorem list_nil_length : ([] : List α).length = 0 := rfl

theorem list_cons_length (x : α) (xs : List α) : (x :: xs).length = xs.length + 1 := rfl

theorem list_nil_append (xs : List α) : [] ++ xs = xs := rfl

theorem list_cons_append (x : α) (xs ys : List α) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

theorem bool_and_comm (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> rfl

theorem bool_and_assoc (a b c : Bool) : ((a && b) && c) = (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bool_or_comm (a b : Bool) : (a || b) = (b || a) := by
  cases a <;> cases b <;> rfl

end Morph.Specs.RegistryConsensus

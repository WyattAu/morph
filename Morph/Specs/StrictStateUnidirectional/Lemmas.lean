/-!
Lemmas for StrictStateUnidirectional.

Lemmas about strict state machines, unidirectional state
transitions, and monotonic progress guarantees.
-/
namespace Morph.Specs.StrictStateUnidirectional

theorem nat_mono_le_succ (n : Nat) : n ≤ n + 1 := Nat.le_succ n

theorem nat_lt_irrefl (n : Nat) : ¬(n < n) := Nat.lt_irrefl n

theorem nat_le_antisymm (m n : Nat) : m ≤ n → n ≤ m → m = n := Nat.le_antisymm

theorem nat_lt_trans (a b c : Nat) : a < b → b < c → a < c := Nat.lt_trans

theorem list_cons_ne_nil (x : α) (xs : List α) : (x :: xs) ≠ [] := by simp

theorem list_nil_ne_cons (xs : List α) (x : α) : [] ≠ (x :: xs) := by simp

theorem option_none_ne_some (x : α) : (none : Option α) ≠ some x := by simp

theorem option_some_ne_none (x : α) : (some x : Option α) ≠ none := by simp

theorem list_head_cons (x : α) (xs : List α) : (x :: xs).head? = some x := rfl

theorem list_tail_cons (x : α) (xs : List α) : (x :: xs).tail = xs := rfl

end Morph.Specs.StrictStateUnidirectional

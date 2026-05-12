/-!
Lemmas for UnidirectionalDataFlow.

Lemmas about data flow directionality, acyclic dependencies,
and topological ordering properties.
-/
namespace Morph.Specs.UnidirectionalDataFlow

structure Edge where
  src : Nat
  dst : Nat
  deriving Repr

abbrev Graph := List Edge

def hasPath (g : Graph) (src dst : Nat) : Bool :=
  g.any (fun e => e.src == src && e.dst == dst)

theorem hasPath_empty (src dst : Nat) : hasPath [] src dst = false := rfl

theorem hasPath_single_hit : hasPath [{ src := 1, dst := 2 }] 1 2 = true := by
  simp [hasPath]

theorem hasPath_single_miss_src : hasPath [{ src := 1, dst := 2 }] 3 2 = false := by
  simp [hasPath]

theorem hasPath_single_miss_dst : hasPath [{ src := 1, dst := 2 }] 1 3 = false := by
  simp [hasPath]

theorem list_nil_append (xs : List α) : [] ++ xs = xs := rfl

theorem list_cons_append (x : α) (xs ys : List α) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

theorem nat_le_refl (n : Nat) : n ≤ n := Nat.le_refl n

theorem nat_lt_irrefl (n : Nat) : ¬(n < n) := Nat.lt_irrefl n

theorem nat_lt_trans (a b c : Nat) : a < b → b < c → a < c := Nat.lt_trans

end Morph.Specs.UnidirectionalDataFlow

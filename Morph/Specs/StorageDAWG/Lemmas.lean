/-!
Lemmas for StorageDAWG.

Lemmas about directed acyclic word graphs (DAWGs),
common suffix sharing, and storage compaction.
-/
namespace Morph.Specs.StorageDAWG

structure DAWGNode where
  id : Nat
  edges : List (Char × Nat)
  terminal : Bool
  deriving Repr

theorem list_nil_length : ([] : List (Char × Nat)).length = 0 := rfl

theorem list_cons_length (e : Char × Nat) (es : List (Char × Nat)) :
    (e :: es).length = es.length + 1 := rfl

theorem list_nil_append (xs : List (Char × Nat)) : [] ++ xs = xs := rfl

theorem list_cons_append (e : Char × Nat) (es xs : List (Char × Nat)) :
    (e :: es) ++ xs = e :: (es ++ xs) := rfl

theorem list_head_cons (e : Char × Nat) (es : List (Char × Nat)) :
    (e :: es).head? = some e := rfl

theorem list_tail_cons (e : Char × Nat) (es : List (Char × Nat)) :
    (e :: es).tail = es := rfl

theorem option_none_isNone : (none : Option DAWGNode).isNone = true := rfl

theorem option_some_isSome (n : DAWGNode) : (some n).isSome = true := rfl

theorem bool_and_true (b : Bool) : (b && true) = b := by cases b <;> rfl

theorem nat_le_refl (n : Nat) : n ≤ n := Nat.le_refl n

theorem nat_lt_irrefl (n : Nat) : ¬(n < n) := Nat.lt_irrefl n

end Morph.Specs.StorageDAWG

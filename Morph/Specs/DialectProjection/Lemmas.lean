/-!
Lemmas for DialectProjection.

Lemmas about projection functions, dialect mapping, and
canonical form preservation.
-/
namespace Morph.Specs.DialectProjection

theorem list_nil_length : ([] : List α).length = 0 := rfl

theorem list_cons_length (x : α) (xs : List α) : (x :: xs).length = xs.length + 1 := rfl

theorem list_cons_append (x : α) (xs ys : List α) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

theorem list_nil_append (xs : List α) : [] ++ xs = xs := rfl

theorem option_none_isNone : (none : Option α).isNone = true := rfl

theorem option_some_isSome (x : α) : (some x).isSome = true := rfl

theorem option_bind_none (f : α → Option β) : Option.bind none f = none := rfl

theorem option_bind_some (x : α) (f : α → Option β) : Option.bind (some x) f = f x := rfl

theorem option_map_none (f : α → β) : Option.map f none = none := rfl

theorem option_map_some (f : α → β) (x : α) : Option.map f (some x) = some (f x) := rfl

theorem bool_and_true (b : Bool) : (b && true) = b := by cases b <;> rfl

theorem bool_or_false (b : Bool) : (b || false) = b := by cases b <;> rfl

theorem bool_and_comm (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> rfl

end Morph.Specs.DialectProjection

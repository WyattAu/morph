/-!
Lemmas for LinkerLogic.

Lemmas about symbol resolution, link table operations,
and dependency ordering.
-/
namespace Morph.Specs.LinkerLogic

theorem list_nil_find (k : String) :
    ([] : List (String × α)).find? (fun (k', _) => k' == k) = none := rfl

theorem option_map_none (f : α → β) : Option.map f none = none := rfl

theorem option_map_some (f : α → β) (x : α) : Option.map f (some x) = some (f x) := rfl

theorem option_bind_none (f : α → Option β) : Option.bind none f = none := rfl

theorem option_bind_some (x : α) (f : α → Option β) : Option.bind (some x) f = f x := rfl

theorem list_assoc_insert_head (k : String) (v : α) :
    ((k, v) :: ([] : List (String × α))).head? = some (k, v) := rfl

theorem list_nil_length : ([] : List (String × α)).length = 0 := rfl

theorem list_cons_length (p : String × α) (xs : List (String × α)) :
    (p :: xs).length = xs.length + 1 := rfl

theorem bool_and_comm (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> rfl

theorem bool_and_assoc (a b c : Bool) : ((a && b) && c) = (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

end Morph.Specs.LinkerLogic

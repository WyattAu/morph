#check @List.lookup
example : ∀ (sym : Nat) (l : List (Nat × String)), sym ∉ l.map Prod.fst → l.lookup sym = none := by
  intro sym l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      simp [List.lookup]
      split
      · rename_i he; simp at he; exact absurd (by simp [he]; exact List.mem_cons_self ..) h
      · exact ih (by intro hm; exact h (List.mem_cons_of_mem _ hm))
#print List.lookup.eq_1

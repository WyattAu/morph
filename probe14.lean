#check @List.mem_map_of_mem
#check @List.mem_cons_self
example (sym s : Nat) (t : String) (l : List (Nat × String)) (h : sym = s) :
    sym ∈ ((s, t) :: l).map Prod.fst := by
  simp [List.mem_map, h]

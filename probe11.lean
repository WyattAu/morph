example (sym : Nat) (τ : String) (l : List (Nat × String))
    (h : (sym, τ) ∈ l) (hnd : (l.map Prod.fst).Nodup) : l.lookup sym = some τ := by
  exact?
example (sym : Nat) (τ : String) (l : List (Nat × String))
    (h : l.lookup sym = some τ) : (sym, τ) ∈ l := by
  exact?

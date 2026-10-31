example (a b : Nat) (h : (a == b) = false) : a ≠ b := by exact?
example (a b : Nat) (h : (a == b) = true) : a = b := by exact?
example (sym : Nat) (τ : String) (l : List (Nat × String))
    (h : (sym, τ) ∈ l) : (sym, τ) = (sym, τ) ∨ (sym, τ) ∈ l.tail := by
  simp [List.mem_cons] at h; exact?

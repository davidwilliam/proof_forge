import ToySpec
def split (a n : Nat) : List Nat := List.replicate n (a / n)
theorem split_ok : ∀ a, (split a 1).length = 1 := by intro a; simp [split]

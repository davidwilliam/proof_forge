import ToySpec
def split (a n : Nat) : List Nat := a :: List.replicate (n - 1) 0

theorem foldl_zeros (k acc : Nat) : (List.replicate k 0).foldl (· + ·) acc = acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem split_ok : Spec.SplitsEvenly split := by
  intro a n hn
  refine ⟨?_, ?_⟩
  · simp [split]; omega
  · simp [split, foldl_zeros]

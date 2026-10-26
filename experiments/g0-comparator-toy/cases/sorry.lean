import ToySpec
def split (a n : Nat) : List Nat := List.replicate n (a / n)
theorem split_ok : Spec.SplitsEvenly split := sorry

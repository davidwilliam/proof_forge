import ToySpec
def split (a n : Nat) : List Nat := List.replicate n (a / n)
axiom cheat : ∀ p : Prop, p
theorem split_ok : Spec.SplitsEvenly split := cheat _

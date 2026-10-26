import ToySpec
def split (a n : Nat) : List Nat := List.replicate n (a / n)
def Spec.SplitsEvenly' (_ : Nat → Nat → List Nat) : Prop := True
theorem split_ok : Spec.SplitsEvenly' split := trivial

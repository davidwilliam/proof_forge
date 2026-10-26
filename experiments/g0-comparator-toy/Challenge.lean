import ToySpec
-- Locked challenge: `split` is a definition hole.
def split : Nat → Nat → List Nat := sorry
theorem split_ok : Spec.SplitsEvenly split := sorry

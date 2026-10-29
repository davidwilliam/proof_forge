Split the residual `amount * r - baseAt amount S r * S` by the sign of `amount`. For nonnegative products this residual is the Euclidean remainder modulo `S`, hence lies in `[0, S)`; for negative `amount` it is the negated remainder of `-amount * r`, hence lies in `(-S, 0]`. The case `amount ≤ 0` inside the nonnegative branch forces `amount = 0`, where the residual is `0`. The final theorem then follows by case analysis on `0 ≤ amount`.

```lean
theorem plan1_emod_bounds (t : Int) (S : Nat) (ht : 0 ≤ t) (hS : 0 < S) :
    0 ≤ t % (S : Int) ∧ t % (S : Int) < (S : Int) := by sorry

theorem plan1_residual_eq_emod (t : Int) (S : Nat) :
    t - (t / (S : Int)) * (S : Int) = t % (S : Int) := by sorry

theorem plan1_ediv_residual_bounds (t : Int) (S : Nat) (ht : 0 ≤ t) (hS : 0 < S) :
    0 ≤ t - (t / (S : Int)) * (S : Int) ∧
    t - (t / (S : Int)) * (S : Int) < (S : Int) := by sorry

theorem plan1_ediv_residual_neg_bounds (t : Int) (S : Nat) (ht : 0 ≤ t) (hS : 0 < S) :
    -(S : Int) < -(t - (t / (S : Int)) * (S : Int)) ∧
    -(t - (t / (S : Int)) * (S : Int)) ≤ 0 := by sorry

theorem plan1_baseAt_bounds_of_nonneg (amount : Int) (S r : Nat) (hS : 0 < S)
    (ha : 0 ≤ amount) :
    -(S : Int) < amount * (r : Int) - baseAt amount S r * (S : Int) ∧
    amount * (r : Int) - baseAt amount S r * (S : Int) < (S : Int) ∧
    (0 ≤ amount → 0 ≤ amount * (r : Int) - baseAt amount S r * (S : Int)) ∧
    (amount ≤ 0 → amount * (r : Int) - baseAt amount S r * (S : Int) ≤ 0) := by sorry

theorem plan1_baseAt_bounds_of_neg (amount : Int) (S r : Nat) (hS : 0 < S)
    (ha : ¬ 0 ≤ amount) :
    -(S : Int) < amount * (r : Int) - baseAt amount S r * (S : Int) ∧
    amount * (r : Int) - baseAt amount S r * (S : Int) < (S : Int) ∧
    (0 ≤ amount → 0 ≤ amount * (r : Int) - baseAt amount S r * (S : Int)) ∧
    (amount ≤ 0 → amount * (r : Int) - baseAt amount S r * (S : Int) ≤ 0) := by sorry
```
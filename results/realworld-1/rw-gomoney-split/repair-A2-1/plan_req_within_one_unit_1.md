**Proof plan.** Any share comes from a base entry `q` or `q + 1`, where `q = amount.natAbs / n` and `r = amount.natAbs % n`. Cast the Nat division equation and the bound `r < n` to `Int`. Two purely linear arithmetic lemmas then finish the positive and negative cases: substituting `K = Q` gives a difference of `-R` or `R`, and substituting `K = Q + 1` gives `N - R` or `R - N`, both strictly between `-N` and `N` when `0 ≤ R < N`. Membership in the mapped `List.range` supplies the `K = Q ∨ K = Q + 1` dichotomy.

```lean
theorem plan1_base_mem_cases (n q r k : Nat)
    (hk : k ∈ (List.range n).map fun p => q + if p < r then 1 else 0) :
    k = q ∨ k = q + 1 := by sorry

theorem plan1_mod_bounds_int (an n : Nat) (hn : 0 < n) :
    0 ≤ ((an % n : Nat) : Int) ∧ ((an % n : Nat) : Int) < (n : Int) := by sorry

theorem plan1_div_eq_int (an n : Nat) :
    ((an / n : Nat) : Int) * (n : Int) + ((an % n : Nat) : Int)
      = ((an : Nat) : Int) := by sorry

theorem plan1_within_pos (N Q R amt K : Int) (hR0 : 0 ≤ R) (hRN : R < N)
    (hdiv : Q * N + R = amt) (hK : K = Q ∨ K = Q + 1) :
    -N < K * N - amt ∧ K * N - amt < N := by sorry

theorem plan1_within_neg (N Q R amt K : Int) (hR0 : 0 ≤ R) (hRN : R < N)
    (hdiv : Q * N + R = -amt) (hK : K = Q ∨ K = Q + 1) :
    -N < (-K) * N - amt ∧ (-K) * N - amt < N := by sorry
```
If the conclusion fails, then the target plus one is at most `c`. Multiplying that successor by `doubleScale` expands to the scaled target terms plus one full `doubleScale`. Since `s` is strictly less than its scaled quotient part plus one full `doubleScale`, this contradicts the assumed scaled bound; `omega` can combine these facts once multiplication monotonicity and the successor expansion are supplied.

```lean
theorem plan5_lt_div_mul_add (s : Nat) :
    s < doubleScale * (s / doubleScale) + doubleScale := by
  sorry

theorem plan5_mul_target_succ (c0 s u e : Nat) :
    doubleScale * (c0 + (s / doubleScale + u) + e + 1) =
      doubleScale * c0 + doubleScale * (s / doubleScale) +
        doubleScale * u + doubleScale * e + doubleScale := by
  sorry

theorem plan5_mul_mono (d a b : Nat) (h : a ≤ b) :
    d * a ≤ d * b := by
  sorry

theorem plan4_bound_of_scaled_le (c c0 s u e : Nat) :
    doubleScale * c ≤
        doubleScale * c0 + s + doubleScale * u + doubleScale * e →
    c ≤ c0 + (s / doubleScale + u) + e := by
  intro h
  have hlt := plan5_lt_div_mul_add s
  have hexp := plan5_mul_target_succ c0 s u e
  by_cases hc : c ≤ c0 + (s / doubleScale + u) + e
  · exact hc
  · exfalso
    have hsucc : c0 + (s / doubleScale + u) + e + 1 ≤ c := by omega
    have hmono := plan5_mul_mono doubleScale _ _ hsucc
    omega
```
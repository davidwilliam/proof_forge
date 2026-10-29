**Proof plan**

Let `q = (A * r) / S` and `m = (A * r) % S`. Nat division gives `q * S + m = A * r`, with `0 ≤ m < S` when `S > 0`. Casting this to `Int`, the excess without the increment is `-m`, and with the increment it is `S - m`. For `b = false` the first value lies in `(-S, S)` since `m < S`; for `b = true` the hypothesis gives `m > 0`, so `S - m` also lies in `(-S, S)`. Splitting on `b` and using the two excess identities plus the remainder bounds finishes by `omega`.

```lean
theorem plan6_rem_bounds_int (A S r : Nat) (hS : 0 < S) :
    0 ≤ ((A * r % S : Nat) : Int) ∧ ((A * r % S : Nat) : Int) < (S : Int) := by sorry

theorem plan6_div_mod_eq_int (A S r : Nat) :
    ((A * r / S : Nat) : Int) * (S : Int) + ((A * r % S : Nat) : Int) =
      (A : Int) * (r : Int) := by sorry

theorem plan6_excess_add_zero (A S r : Nat) :
    (((A * r / S : Nat) : Int) + 0) * (S : Int) - (A : Int) * (r : Int) =
      -((A * r % S : Nat) : Int) := by sorry

theorem plan6_excess_add_one (A S r : Nat) :
    (((A * r / S : Nat) : Int) + 1) * (S : Int) - (A : Int) * (r : Int) =
      (S : Int) - ((A * r % S : Nat) : Int) := by sorry
```
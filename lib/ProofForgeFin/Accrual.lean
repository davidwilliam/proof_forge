import ProofForgeFin.Rounding
/-!
# Rounding per operation and capped increments

Two patterns of quantities that change one operation at a time.

* A part rounded down, plus at most one unit handed out afterwards, is within one unit of the
  exact value: `within_one_of_floor_le` for any `x` with `a / W ≤ x ≤ a / W + 1`,
  `floor_add_bit_within` for `a / W + e` with `e ≤ 1`, `floor_add_bit_within_int` with the casts
  a specification on `Int` writes, and `within_one_of_bounds` (`Nat`) and
  `within_one_of_bounds_int` for a floor given by its bounds `F * W ≤ a < F * W + W`;
  `natCast_eq_mul_div_add_mod` splits a cast amount into quotient and remainder.
* A fill, a route or a draw adds `min q (cap - done)` to a running quantity `done ≤ cap`: the
  quantity stays within the cap, never decreases, and the remaining capacity shrinks by the
  amount added (`add_min_sub_le`, `add_min_sub_eq_min`, `le_add_min_sub`, `sub_add_min_sub`).
-/

namespace ProofForgeFin.Accrual

/-- A part between the rounded-down quotient `a / W` and one more is within one unit of the exact
value: `x * W ≤ a + W` and `a < x * W + W`. -/
theorem within_one_of_floor_le (a W x : Nat) (hW : 0 < W) (h1 : a / W ≤ x) (h2 : x ≤ a / W + 1) :
    x * W ≤ a + W ∧ a < x * W + W := by
  have hf := Nat.div_mul_le_self a W
  have hl := Nat.lt_div_mul_add (a := a) hW
  constructor
  · have : x * W ≤ (a / W + 1) * W := Nat.mul_le_mul_right W h2
    rw [Nat.succ_mul] at this; omega
  · have : a / W * W ≤ x * W := Nat.mul_le_mul_right W h1
    omega

/-- The rounded-down quotient plus a bit `e ≤ 1` (a leftover unit or none) is within one unit of
the exact value. -/
theorem floor_add_bit_within (a W e : Nat) (hW : 0 < W) (he : e ≤ 1) :
    (a / W + e) * W ≤ a + W ∧ a < (a / W + e) * W + W :=
  within_one_of_floor_le a W _ hW (by omega) (by omega)

/-- `floor_add_bit_within` with the part, the value and the divisor cast to `Int`. -/
theorem floor_add_bit_within_int (a W e : Nat) (hW : 0 < W) (he : e ≤ 1) :
    ((a / W + e : Nat) : Int) * W ≤ a + W ∧ (a : Int) < ((a / W + e : Nat) : Int) * W + W := by
  have h := floor_add_bit_within a W e hW he
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- A part at most one unit above a floor `F` of `a / W` (given by its bounds
`F * W ≤ a < F * W + W`, as a proof states them) is within one unit of the exact value. -/
theorem within_one_of_bounds {F W a b : Nat} (h1 : F * W ≤ a) (h2 : a < F * W + W) (hb1 : F ≤ b)
    (hb2 : b ≤ F + 1) : b * W ≤ a + W ∧ a < b * W + W := by
  have l1 : F * W ≤ b * W := Nat.mul_le_mul_right W hb1
  have l2 : b * W ≤ (F + 1) * W := Nat.mul_le_mul_right W hb2
  rw [Nat.succ_mul] at l2
  omega

/-- `within_one_of_bounds` on `Int`: a part `F` or `F + 1` above a floor `F` of `a / W` is within
one unit of the exact value. -/
theorem within_one_of_bounds_int {F W a b : Int} (h1 : F * W ≤ a) (h2 : a < F * W + W)
    (hb : b = F ∨ b = F + 1) : b * W ≤ a + W ∧ a < b * W + W := by
  rcases hb with rfl | rfl
  · omega
  · rw [Int.add_mul, Int.one_mul]; omega

/-- A natural number, cast to `Int`, as the divisor times the integer quotient of the casts plus
the cast remainder. -/
theorem natCast_eq_mul_div_add_mod (a n : Nat) :
    (a : Int) = (n : Int) * ((a : Int) / (n : Int)) + ((a % n : Nat) : Int) := by
  rw [Int.natCast_emod]; have := Int.emod_add_mul_ediv (a : Int) (n : Int); omega

/-- Adding `min q (cap - done)` to `done ≤ cap` stays within the cap. -/
theorem add_min_sub_le (done q cap : Nat) (h : done ≤ cap) : done + min q (cap - done) ≤ cap := by omega

/-- Adding `min q (cap - done)` to `done ≤ cap` gives `min (done + q) cap`. -/
theorem add_min_sub_eq_min (done q cap : Nat) (h : done ≤ cap) :
    done + min q (cap - done) = min (done + q) cap := by omega

/-- Adding `min q (cap - done)` never decreases `done`. -/
theorem le_add_min_sub (done q cap : Nat) : done ≤ done + min q (cap - done) := by omega

/-- The capacity left after adding `min q (cap - done)` is the capacity before minus the amount
added. -/
theorem sub_add_min_sub (done q cap : Nat) :
    cap - (done + min q (cap - done)) = cap - done - min q (cap - done) := by omega

end ProofForgeFin.Accrual

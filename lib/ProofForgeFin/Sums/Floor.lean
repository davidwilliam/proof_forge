import ProofForgeFin.Sums.Index
/-!
# Sums of rounded-down parts

A pro-rata split rounds every part down, `A * w / W`, and hands the units the rounding lost out
afterwards. The total lost is the sum of the remainders divided by `W`; it is less than the
number of parts. These lemmas state that on `Nat` lists with the mapped-sum form specifications
use (`ProofForgeFin.Money.Allocation` has the same facts for its `Int` allocation functions).

* `sum_map_div_add_mod`: a sum is `W` times the sum of the quotients plus the sum of the
  remainders; `mul_sum_eq_floor_add_mod` for parts `A * r / l.sum`.
* `sum_map_mod_le`, `sum_map_mod_lt`: each remainder is below `W`.
* `sum_map_mul_left`, `sum_mul_left`, `sum_mul_right`, `sum_mul_left_int`: a common factor out of
  a sum.
* `sum_floor_shares_le`: the rounded-down parts of `A` do not exceed `A`;
  `floor_shares_leftover_lt_length`: the leftover is less than the number of parts.
-/

namespace ProofForgeFin.Sums

universe u

variable {α : Type u}

/-- A common factor out of a sum, on `Nat`. -/
theorem sum_map_mul_left (c : Nat) (f : α → Nat) (l : List α) :
    (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add]

/-- A common factor out of a sum of a list of `Nat`. -/
theorem sum_mul_left (c : Nat) (l : List Nat) : (l.map (fun a => c * a)).sum = c * l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add]

/-- A common factor out of a sum of a list of `Nat`, on the right. -/
theorem sum_mul_right (c : Nat) (l : List Nat) : (l.map (fun a => a * c)).sum = l.sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul]

/-- A common factor out of a sum of a list of `Int`. -/
theorem sum_mul_left_int (c : Int) (l : List Int) : (l.map (fun a => c * a)).sum = c * l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.mul_add]

/-- A sum is `W` times the sum of the quotients by `W` plus the sum of the remainders. -/
theorem sum_map_div_add_mod (f : α → Nat) (W : Nat) (l : List α) :
    (l.map f).sum = W * (l.map (fun a => f a / W)).sum + (l.map (fun a => f a % W)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := Nat.div_add_mod (f a) W
    rw [ih, Nat.mul_add]; omega

/-- The remainders by `0 < W`, summed over a list, are at most the length times `W - 1`. -/
theorem sum_map_mod_le (f : α → Nat) {W : Nat} (hW : 0 < W) (l : List α) :
    (l.map (fun a => f a % W)).sum ≤ l.length * (W - 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := Nat.mod_lt (f a) hW
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]; omega

/-- The remainders by `0 < W`, summed over a nonempty list, are less than the length times
`W`. -/
theorem sum_map_mod_lt (f : α → Nat) {W : Nat} (hW : 0 < W) {l : List α} (hl : l ≠ []) :
    (l.map (fun a => f a % W)).sum < l.length * W := by
  have h := sum_map_mod_le f hW l
  have : 0 < l.length := List.length_pos_iff.mpr hl
  have : l.length * (W - 1) < l.length * W := Nat.mul_lt_mul_of_pos_left (by omega) this
  omega

/-- `A` times the sum of the ratios, as the rounded-down parts `A * r / l.sum` and their
remainders. -/
theorem mul_sum_eq_floor_add_mod (A : Nat) (l : List Nat) :
    l.sum * A = l.sum * (l.map (fun r => A * r / l.sum)).sum + (l.map (fun r => A * r % l.sum)).sum := by
  have h := sum_map_div_add_mod (fun r => A * r) l.sum l
  have h1 : (l.map (fun r => A * r)).sum = A * l.sum := by
    rw [sum_map_mul_left A (fun r => r)]; simp
  rw [h1] at h; rw [Nat.mul_comm]; exact h

/-- The parts of `A` in proportion to the ratios, rounded down, add up to at most `A`. -/
theorem sum_floor_shares_le (A : Nat) (l : List Nat) : (l.map (fun r => A * r / l.sum)).sum ≤ A := by
  by_cases hS : l.sum = 0
  · rw [hS]; simp only [Nat.div_zero]; rw [sum_map_const]; simp
  · have h := mul_sum_eq_floor_add_mod A l
    have hle : l.sum * (l.map (fun r => A * r / l.sum)).sum ≤ l.sum * A := by omega
    exact Nat.le_of_mul_le_mul_left hle (by omega)

/-- The units of `A` that rounding the proportional parts down leaves over are fewer than the
number of parts (for ratios with a positive sum). -/
theorem floor_shares_leftover_lt_length (A : Nat) {l : List Nat} (hS : 0 < l.sum) :
    A - (l.map (fun r => A * r / l.sum)).sum < l.length := by
  have hl : l ≠ [] := by rintro rfl; simp at hS
  have h := mul_sum_eq_floor_add_mod A l
  have hm := sum_map_mod_lt (fun r => A * r) hS hl
  have key : l.sum * (A - (l.map (fun r => A * r / l.sum)).sum) < l.sum * l.length := by
    rw [Nat.mul_sub, Nat.mul_comm l.sum l.length]; omega
  exact Nat.lt_of_mul_lt_mul_left key

end ProofForgeFin.Sums

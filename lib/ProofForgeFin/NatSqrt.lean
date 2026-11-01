import ProofForgeFin.SqrtIter
/-!
# `Nat.sqrt` and `Nat.log2` facts under their usual names

Lean core states two facts about `Nat.sqrt` (`Nat.sqrt_le`, `Nat.lt_succ_sqrt`). This module adds,
in the `Nat` namespace and under the names and statements Mathlib uses, the order facts proofs
usually reach for: `Nat.le_sqrt`, `Nat.le_sqrt'`, `Nat.sqrt_lt`, `Nat.sqrt_lt'`, `Nat.sqrt_le'`,
`Nat.lt_succ_sqrt'`, `Nat.sqrt_le_add`, `Nat.sqrt_le_self`, `Nat.sqrt_le_sqrt`, `Nat.sqrt_lt_self`,
`Nat.sqrt_pos`, `Nat.sqrt_eq_zero`, `Nat.sqrt_zero`, `Nat.sqrt_one`, `Nat.eq_sqrt`,
`Nat.eq_sqrt'`, `Nat.sqrt_eq`, `Nat.sqrt_eq'`, `Nat.sqrt_add_eq`, `Nat.sqrt_succ_le_succ_sqrt`;
and three bounds of `Nat.log2`: `Nat.pow_log2_le`, `Nat.lt_pow_succ_log2`,
`Nat.log2_lt_of_lt_pow`. Each is proved from `ProofForgeFin.Sqrt`.
-/

namespace Nat

open ProofForgeFin.Sqrt

/-- `m ≤ sqrt n ↔ m * m ≤ n`. -/
theorem le_sqrt {m n : Nat} : m ≤ Nat.sqrt n ↔ m * m ≤ n := le_sqrt_iff

/-- `m ≤ sqrt n ↔ m ^ 2 ≤ n`. -/
theorem le_sqrt' {m n : Nat} : m ≤ Nat.sqrt n ↔ m ^ 2 ≤ n := by rw [Nat.pow_two]; exact le_sqrt_iff

/-- `sqrt m < n ↔ m < n * n`. -/
theorem sqrt_lt {m n : Nat} : Nat.sqrt m < n ↔ m < n * n := sqrt_lt_iff

/-- `sqrt m < n ↔ m < n ^ 2`. -/
theorem sqrt_lt' {m n : Nat} : Nat.sqrt m < n ↔ m < n ^ 2 := by rw [Nat.pow_two]; exact sqrt_lt_iff

/-- `sqrt n ^ 2 ≤ n`. -/
theorem sqrt_le' (n : Nat) : Nat.sqrt n ^ 2 ≤ n := by rw [Nat.pow_two]; exact Nat.sqrt_le n

/-- `n < (sqrt n + 1) ^ 2`. -/
theorem lt_succ_sqrt' (n : Nat) : n < (Nat.sqrt n + 1) ^ 2 := by
  rw [Nat.pow_two]; exact Nat.lt_succ_sqrt n

/-- `n ≤ sqrt n * sqrt n + sqrt n + sqrt n`. -/
theorem sqrt_le_add (n : Nat) : n ≤ Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n := by
  have h := Nat.lt_succ_sqrt n
  have e : Nat.succ (Nat.sqrt n) * Nat.succ (Nat.sqrt n) =
      Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n + 1 := by
    rw [Nat.succ_eq_add_one, add_mul_self_eq]; omega
  omega

/-- `sqrt n ≤ n`. -/
theorem sqrt_le_self (n : Nat) : Nat.sqrt n ≤ n := ProofForgeFin.Sqrt.sqrt_le_self n

/-- The root is monotone. -/
theorem sqrt_le_sqrt {m n : Nat} (h : m ≤ n) : Nat.sqrt m ≤ Nat.sqrt n := ProofForgeFin.Sqrt.sqrt_le_sqrt h

/-- `sqrt n < n` for `1 < n`. -/
theorem sqrt_lt_self {n : Nat} (h : 1 < n) : Nat.sqrt n < n := by
  apply sqrt_lt_of_lt_mul_self
  have : n * 1 < n * n := Nat.mul_lt_mul_of_pos_left h (by omega)
  omega

/-- `0 < sqrt n ↔ 0 < n`. -/
theorem sqrt_pos {n : Nat} : 0 < Nat.sqrt n ↔ 0 < n := by
  constructor
  · intro h; have := Nat.sqrt_le_self n; omega
  · exact ProofForgeFin.Sqrt.sqrt_pos

/-- `sqrt n = 0 ↔ n = 0`. -/
theorem sqrt_eq_zero {n : Nat} : Nat.sqrt n = 0 ↔ n = 0 := by
  have := @Nat.sqrt_pos n; omega

/-- `sqrt 0 = 0`. -/
theorem sqrt_zero : Nat.sqrt 0 = 0 := Nat.sqrt_eq_zero.mpr rfl

/-- `sqrt 1 = 1`. -/
theorem sqrt_one : Nat.sqrt 1 = 1 := sqrt_eq_of_bounds (by decide) (by decide)

/-- `q = sqrt n ↔ q * q ≤ n ∧ n < (q + 1) * (q + 1)`. -/
theorem eq_sqrt {n q : Nat} : q = Nat.sqrt n ↔ q * q ≤ n ∧ n < (q + 1) * (q + 1) := eq_sqrt_iff

/-- `q = sqrt n ↔ q ^ 2 ≤ n ∧ n < (q + 1) ^ 2`. -/
theorem eq_sqrt' {n q : Nat} : q = Nat.sqrt n ↔ q ^ 2 ≤ n ∧ n < (q + 1) ^ 2 := by
  rw [Nat.pow_two, Nat.pow_two]; exact eq_sqrt_iff

/-- `sqrt (n * n) = n`. -/
theorem sqrt_eq (n : Nat) : Nat.sqrt (n * n) = n := sqrt_mul_self n

/-- `sqrt (n ^ 2) = n`. -/
theorem sqrt_eq' (n : Nat) : Nat.sqrt (n ^ 2) = n := by rw [Nat.pow_two]; exact sqrt_mul_self n

/-- `sqrt (n * n + a) = n` for `a ≤ n + n`. -/
theorem sqrt_add_eq (n : Nat) {a : Nat} (h : a ≤ n + n) : Nat.sqrt (n * n + a) = n := by
  apply sqrt_eq_of_bounds (Nat.le_add_right _ _)
  rw [add_mul_self_eq]; omega

/-- `sqrt (n + 1) ≤ sqrt n + 1`. -/
theorem sqrt_succ_le_succ_sqrt (n : Nat) : Nat.sqrt (n + 1) ≤ Nat.sqrt n + 1 := by
  apply Nat.le_of_lt_succ
  apply sqrt_lt_of_lt_mul_self
  have h := Nat.lt_succ_sqrt n
  have : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) < (Nat.sqrt n + 1 + 1) * (Nat.sqrt n + 1 + 1) :=
    Nat.mul_self_lt_mul_self (by omega)
  simp only [Nat.succ_eq_add_one] at *
  omega

/-- `2 ^ log2 n ≤ n` for `n ≠ 0`. -/
theorem pow_log2_le {n : Nat} (h : n ≠ 0) : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le h

/-- `n < 2 ^ (log2 n + 1)`. -/
theorem lt_pow_succ_log2 (n : Nat) : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self

/-- `log2 n < k` when `n < 2 ^ k` and `n ≠ 0`. -/
theorem log2_lt_of_lt_pow {n k : Nat} (hn : n ≠ 0) (h : n < 2 ^ k) : Nat.log2 n < k :=
  (Nat.log2_lt hn).mpr h

end Nat

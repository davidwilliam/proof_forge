/-!
# Machine words and exact arithmetic

Ports of contract code use `BitVec w` for `u64`, `u128`, `u256`: every operation wraps modulo
`2^w`. A specification states amounts in unbounded natural numbers. This module gives the
conditions under which a word operation is exact (its `toNat` is the natural-number result),
and the overflow condition of a left shift, which is the check a fixed-point routine such as
Cetus's `checked_shlw` must get right.
-/

namespace ProofForgeFin

/-! ## Shifts on natural numbers -/

/-- A left shift is multiplication by a power of two. -/
theorem shiftLeft_eq_mul (a k : Nat) : a <<< k = a * 2 ^ k := Nat.shiftLeft_eq a k

/-- A right shift is floor division by a power of two. -/
theorem shiftRight_eq_div (a k : Nat) : a >>> k = a / 2 ^ k := Nat.shiftRight_eq_div_pow a k

/-- `a * 2^k` fits in `w` bits exactly when `a` fits in `w - k` bits (for `k ≤ w`). For
`w = 256`, `k = 64` this is the condition of a correct `checked_shlw`: no overflow exactly when
`a < 2^192`. -/
theorem mul_two_pow_lt_iff {a k w : Nat} (hk : k ≤ w) : a * 2 ^ k < 2 ^ w ↔ a < 2 ^ (w - k) := by
  have hw : 2 ^ w = 2 ^ (w - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [hw]
  exact Nat.mul_lt_mul_right (Nat.pow_pos (by decide))

/-- When `a * 2^k` does not fit in `w` bits, `a` is at least `2^(w - k)`. -/
theorem le_of_two_pow_le_mul {a k w : Nat} (hk : k ≤ w) (h : 2 ^ w ≤ a * 2 ^ k) :
    2 ^ (w - k) ≤ a :=
  Nat.le_of_not_lt fun h' => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ((mul_two_pow_lt_iff hk).2 h') h)

/-! ## Exact word operations -/

/-- A left shift of a word is exact when the result fits. -/
theorem toNat_shiftLeft_of_lt {w : Nat} (x : BitVec w) (k : Nat) (h : x.toNat * 2 ^ k < 2 ^ w) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt h

/-- A left shift of a word by `k ≤ w` bits is exact when the word is below `2^(w - k)`. -/
theorem toNat_shiftLeft_of_lt_two_pow {w : Nat} (x : BitVec w) {k : Nat} (hk : k ≤ w)
    (h : x.toNat < 2 ^ (w - k)) : (x <<< k).toNat = x.toNat * 2 ^ k :=
  toNat_shiftLeft_of_lt x k ((mul_two_pow_lt_iff hk).2 h)

/-- A right shift of a word is floor division by a power of two. -/
theorem toNat_ushiftRight {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Word multiplication is exact when the product fits. -/
theorem toNat_mul_of_lt {w : Nat} (x y : BitVec w) (h : x.toNat * y.toNat < 2 ^ w) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h

/-- Word addition is exact when the sum fits. -/
theorem toNat_add_of_lt {w : Nat} (x y : BitVec w) (h : x.toNat + y.toNat < 2 ^ w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

/-- Word subtraction is exact when it does not underflow. -/
theorem toNat_sub_of_le {w : Nat} (x y : BitVec w) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]
  have hx := x.isLt
  have : 2 ^ w - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ w := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Word division is floor division. -/
theorem toNat_udiv' {w : Nat} (x y : BitVec w) : (x / y).toNat = x.toNat / y.toNat :=
  BitVec.toNat_udiv

/-- Widening a word keeps its value. -/
theorem toNat_setWidth_of_le {w v : Nat} (x : BitVec w) (h : w ≤ v) :
    (x.setWidth v).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

/-- The product of two `w`-bit words, widened to `2w` bits first, is exact: this is
`full_mul` (`u128 × u128 → u256`). -/
theorem toNat_fullMul {w : Nat} (x y : BitVec w) :
    (x.setWidth (2 * w) * y.setWidth (2 * w)).toNat = x.toNat * y.toNat := by
  have h1 : w ≤ 2 * w := by omega
  rw [toNat_mul_of_lt, toNat_setWidth_of_le x h1, toNat_setWidth_of_le y h1]
  rw [toNat_setWidth_of_le x h1, toNat_setWidth_of_le y h1]
  have hx := x.isLt
  have hy := y.isLt
  calc x.toNat * y.toNat < 2 ^ w * 2 ^ w := Nat.mul_lt_mul_of_lt_of_lt hx hy
    _ = 2 ^ (2 * w) := by rw [← Nat.pow_add]; congr 1; omega

/-- Truncating a natural number to `w` bits keeps it when it fits. -/
theorem toNat_ofNat_of_lt {w a : Nat} (h : a < 2 ^ w) : (BitVec.ofNat w a).toNat = a := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

end ProofForgeFin

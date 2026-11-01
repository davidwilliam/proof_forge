/-!
# From machine words to natural numbers and back

Facts that move a computation on `BitVec w`, for any width `w`, to the same computation on the
values `toNat`, and back. Wrapping arithmetic (`+`, `*`, `-`, `<<<`) agrees with `Nat` exactly
when no overflow or underflow occurs; division, right shifts and comparisons always agree.

* Exactness as equivalences: `toNat_add_eq_iff`, `toNat_mul_eq_iff`, `toNat_sub_eq_iff`,
  `toNat_shiftLeft_eq_iff`; and as implications from value hypotheses: `toNat_add_of_lt'`,
  `toNat_mul_of_lt'`, `toNat_sub_of_toNat_le`, `toNat_shiftLeft_of_mul_lt`.
* Always exact: `toNat_div` (`/`), `toNat_shiftRight` (`>>>` by a `Nat`), `toNat_shiftRight_bv`
  (by a word), `toNat_shiftRight_one`, `toNat_one_shiftLeft_bv` (`1 <<< y` is `2^y`).
* Comparisons and conditionals: `lt_iff_toNat_lt`, `le_iff_toNat_le`, `eq_iff_toNat_eq`,
  `ne_zero_iff_toNat_pos`, `toNat_ite`, `toNat_ite_lt` (`if x < y then x else y` is the `min`
  of the values), `toNat_ite_lt_max`.
* Sizes: `mul_lt_two_pow` (`a < 2^m`, `b < 2^n`, `m + n ≤ w` give `a * b < 2^w`),
  `mul_self_lt_two_pow`, `add_lt_two_pow` (two summands below `2^k`, `k < w`),
  `toNat_mul_of_lt_two_pow`, `toNat_add_of_lt_two_pow`, `log2_toNat_lt`, `toNat_lt_two_pow_of_le`.
* Literals: `toNat_ofNat_of_lt'`, `toNat_one'`, `toNat_zero'`.
* Iterations: `iter_succ_of_eqns` (an iteration defined first step first also unfolds last step
  last), `iter_map_of_sim` and `iter_map_invariant` (through a map such as `toNat`, `k` steps of a
  word function that acts as `g` on the values satisfying an invariant are `Nat.repeat g k`),
  `repeat_succ'`.
-/

namespace ProofForgeFin.WordBridge

variable {w : Nat}

/-! ## Exactness of wrapping arithmetic -/

/-- Word addition agrees with addition of the values exactly when the sum fits in `w` bits. -/
theorem toNat_add_eq_iff {x y : BitVec w} : (x + y).toNat = x.toNat + y.toNat ↔ x.toNat + y.toNat < 2 ^ w := by
  rw [BitVec.toNat_add]
  constructor
  · intro h; rw [← h]; exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · exact Nat.mod_eq_of_lt

/-- Word multiplication agrees with multiplication of the values exactly when the product fits in
`w` bits. -/
theorem toNat_mul_eq_iff {x y : BitVec w} : (x * y).toNat = x.toNat * y.toNat ↔ x.toNat * y.toNat < 2 ^ w := by
  rw [BitVec.toNat_mul]
  constructor
  · intro h; rw [← h]; exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · exact Nat.mod_eq_of_lt

/-- Word subtraction agrees with truncated subtraction of the values exactly when it does not
underflow. -/
theorem toNat_sub_eq_iff {x y : BitVec w} : (x - y).toNat = x.toNat - y.toNat ↔ y.toNat ≤ x.toNat := by
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro hlt
    have hx := x.isLt
    have hy := y.isLt
    rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · intro h; exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

/-- Word addition is exact when the sum of the values fits in `w` bits. -/
theorem toNat_add_of_lt' {x y : BitVec w} (h : x.toNat + y.toNat < 2 ^ w) :
    (x + y).toNat = x.toNat + y.toNat := toNat_add_eq_iff.mpr h

/-- Word multiplication is exact when the product of the values fits in `w` bits. -/
theorem toNat_mul_of_lt' {x y : BitVec w} (h : x.toNat * y.toNat < 2 ^ w) :
    (x * y).toNat = x.toNat * y.toNat := toNat_mul_eq_iff.mpr h

/-- Word subtraction is exact when the second value is at most the first. -/
theorem toNat_sub_of_toNat_le {x y : BitVec w} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := toNat_sub_eq_iff.mpr h

/-- A left shift by `k` bits agrees with multiplication by `2^k` exactly when the product fits. -/
theorem toNat_shiftLeft_eq_iff {x : BitVec w} {k : Nat} :
    (x <<< k).toNat = x.toNat * 2 ^ k ↔ x.toNat * 2 ^ k < 2 ^ w := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  constructor
  · intro h; rw [← h]; exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · exact Nat.mod_eq_of_lt

/-- A left shift by `k` bits is multiplication by `2^k` when the product fits. -/
theorem toNat_shiftLeft_of_mul_lt {x : BitVec w} {k : Nat} (h : x.toNat * 2 ^ k < 2 ^ w) :
    (x <<< k).toNat = x.toNat * 2 ^ k := toNat_shiftLeft_eq_iff.mpr h

/-- A left shift by a word `y` is a left shift by its value. -/
theorem shiftLeft_bv_eq {v : Nat} (x : BitVec w) (y : BitVec v) : x <<< y = x <<< y.toNat :=
  BitVec.shiftLeft_eq'

/-- A left shift by a word `y` is multiplication by `2^y` when the product fits. -/
theorem toNat_shiftLeft_bv_of_mul_lt {v : Nat} {x : BitVec w} {y : BitVec v}
    (h : x.toNat * 2 ^ y.toNat < 2 ^ w) : (x <<< y).toNat = x.toNat * 2 ^ y.toNat := by
  rw [BitVec.shiftLeft_eq']; exact toNat_shiftLeft_of_mul_lt h

/-! ## Always exact -/

/-- Word division is floor division of the values (a zero divisor gives zero on both sides). -/
theorem toNat_div (x y : BitVec w) : (x / y).toNat = x.toNat / y.toNat := BitVec.toNat_udiv

/-- A right shift by `k` bits is floor division by `2^k`. -/
theorem toNat_shiftRight (x : BitVec w) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A right shift by a word `y` is floor division by `2^y`. -/
theorem toNat_shiftRight_bv {v : Nat} (x : BitVec w) (y : BitVec v) :
    (x >>> y).toNat = x.toNat / 2 ^ y.toNat := by
  rw [BitVec.ushiftRight_eq']; exact toNat_shiftRight x y.toNat

/-- A right shift by one bit halves the value, rounding down. -/
theorem toNat_shiftRight_one (x : BitVec w) : (x >>> 1).toNat = x.toNat / 2 := toNat_shiftRight x 1

/-- `1 <<< k` is `2^k` for `k < w`. -/
theorem toNat_one_shiftLeft' {k : Nat} (h : k < w) : ((1 : BitVec w) <<< k).toNat = 2 ^ k := by
  have h1 : (1 : BitVec w).toNat = 1 := BitVec.toNat_one (by omega)
  rw [toNat_shiftLeft_of_mul_lt] <;> rw [h1, Nat.one_mul]
  exact Nat.pow_lt_pow_right (by decide) h

/-- `1 <<< y` for a word `y` is `2^y` when `y < w`. -/
theorem toNat_one_shiftLeft_bv {v : Nat} {y : BitVec v} (h : y.toNat < w) :
    ((1 : BitVec w) <<< y).toNat = 2 ^ y.toNat := by
  rw [BitVec.shiftLeft_eq']; exact toNat_one_shiftLeft' h

/-! ## Comparisons and conditionals -/

/-- Words compare as their values. -/
theorem lt_iff_toNat_lt {x y : BitVec w} : x < y ↔ x.toNat < y.toNat := BitVec.lt_def

/-- Words compare as their values. -/
theorem le_iff_toNat_le {x y : BitVec w} : x ≤ y ↔ x.toNat ≤ y.toNat := BitVec.le_def

/-- Words are equal exactly when their values are. -/
theorem eq_iff_toNat_eq {x y : BitVec w} : x = y ↔ x.toNat = y.toNat := BitVec.toNat_eq

/-- A word is nonzero exactly when its value is positive. -/
theorem ne_zero_iff_toNat_pos {x : BitVec w} : x ≠ 0 ↔ 0 < x.toNat := by
  have h0 : (0 : BitVec w).toNat = 0 := BitVec.toNat_ofNat 0 w ▸ Nat.zero_mod _
  rw [Ne, BitVec.toNat_eq, h0]; omega

/-- A word is zero exactly when its value is zero. -/
theorem eq_zero_iff_toNat_eq_zero {x : BitVec w} : x = 0 ↔ x.toNat = 0 := by
  have h0 : (0 : BitVec w).toNat = 0 := BitVec.toNat_ofNat 0 w ▸ Nat.zero_mod _
  rw [BitVec.toNat_eq, h0]

/-- The value of a conditional word is the conditional value. -/
theorem toNat_ite (c : Prop) [Decidable c] (x y : BitVec w) :
    (if c then x else y).toNat = if c then x.toNat else y.toNat := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

/-- `if x < y then x else y` (the minimum of two words) has the smaller value. -/
theorem toNat_ite_lt (x y : BitVec w) : (if x < y then x else y).toNat = min x.toNat y.toNat := by
  by_cases h : x < y
  · rw [ite_eq_left h]; have := BitVec.lt_def.mp h; omega
  · rw [ite_eq_right h]; have : ¬ x.toNat < y.toNat := fun c => h (BitVec.lt_def.mpr c); omega

/-- `if x < y then y else x` (the maximum of two words) has the larger value. -/
theorem toNat_ite_lt_max (x y : BitVec w) : (if x < y then y else x).toNat = max x.toNat y.toNat := by
  by_cases h : x < y
  · rw [ite_eq_left h]; have := BitVec.lt_def.mp h; omega
  · rw [ite_eq_right h]; have : ¬ x.toNat < y.toNat := fun c => h (BitVec.lt_def.mpr c); omega

/-- The comparison `x < y` decides as the comparison of the values. -/
theorem decide_lt_eq (x y : BitVec w) : decide (x < y) = decide (x.toNat < y.toNat) := by
  rw [decide_eq_decide]; exact BitVec.lt_def

/-! ## Sizes -/

/-- A product of a number below `2^m` and one below `2^n` is below `2^w` when `m + n ≤ w`. -/
theorem mul_lt_two_pow {a b m n : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ n) (h : m + n ≤ w) :
    a * b < 2 ^ w := by
  have h1 : a * b < 2 ^ m * 2 ^ n := Nat.mul_lt_mul_of_lt_of_lt ha hb
  rw [← Nat.pow_add] at h1
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h)

/-- The square of a number below `2^k` is below `2^w` when `2 * k ≤ w`. -/
theorem mul_self_lt_two_pow {a k : Nat} (ha : a < 2 ^ k) (h : 2 * k ≤ w) : a * a < 2 ^ w :=
  mul_lt_two_pow ha ha (by omega)

/-- A sum of two numbers below `2^k` is below `2^w` when `k < w`. -/
theorem add_lt_two_pow {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) (h : k < w) : a + b < 2 ^ w := by
  have : 2 ^ (k + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) h
  rw [Nat.pow_succ] at this
  omega

/-- A number below `2^k` is below `2^w` when `k ≤ w`. -/
theorem lt_two_pow_of_le {a k : Nat} (ha : a < 2 ^ k) (h : k ≤ w) : a < 2 ^ w :=
  Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) h)

/-- Word multiplication is exact when the values are below `2^m` and `2^n` with `m + n ≤ w`. -/
theorem toNat_mul_of_lt_two_pow {x y : BitVec w} {m n : Nat} (hx : x.toNat < 2 ^ m) (hy : y.toNat < 2 ^ n)
    (h : m + n ≤ w) : (x * y).toNat = x.toNat * y.toNat :=
  toNat_mul_of_lt' (mul_lt_two_pow hx hy h)

/-- Word addition is exact when both values are below `2^k` with `k < w`. -/
theorem toNat_add_of_lt_two_pow {x y : BitVec w} {k : Nat} (hx : x.toNat < 2 ^ k) (hy : y.toNat < 2 ^ k)
    (h : k < w) : (x + y).toNat = x.toNat + y.toNat :=
  toNat_add_of_lt' (add_lt_two_pow hx hy h)

/-- The value of a word of positive width has its base-2 logarithm below the width. -/
theorem log2_toNat_lt (hw : 0 < w) (x : BitVec w) : Nat.log2 x.toNat < w := by
  rcases Nat.eq_zero_or_pos x.toNat with h | h
  · rw [h]; exact hw
  · exact (Nat.log2_lt (by omega)).mpr x.isLt

/-- The value of a word of width at most `k` is below `2^k`. -/
theorem toNat_lt_two_pow_of_le {k : Nat} (x : BitVec w) (h : w ≤ k) : x.toNat < 2 ^ k :=
  lt_two_pow_of_le x.isLt h

/-! ## Literals -/

/-- A literal below `2^w` keeps its value. -/
theorem toNat_ofNat_of_lt' {n : Nat} (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The word `1` has value `1` at positive width. -/
theorem toNat_one' (hw : 0 < w) : (1 : BitVec w).toNat = 1 := BitVec.toNat_one hw

/-- The word `0` has value `0`. -/
theorem toNat_zero' : (0 : BitVec w).toNat = 0 := BitVec.toNat_ofNat 0 w ▸ Nat.zero_mod _

/-! ## Iterations on words as iterations on values -/

/-- `Nat.repeat g (k + 1) b` is also `k` repetitions from `g b`. -/
theorem repeat_succ' {β : Type _} (g : β → β) (k : Nat) (b : β) :
    Nat.repeat g k (g b) = Nat.repeat g (k + 1) b := by
  induction k with
  | zero => rfl
  | succ k ih => show g (Nat.repeat g k (g b)) = g (Nat.repeat g (k + 1) b); rw [ih]

/-- An iteration `it` defined by `it 0 x = x` and `it (k + 1) x = it k (f x)` (the first step
first) also satisfies `it (k + 1) x = f (it k x)` (the last step last). -/
theorem iter_succ_of_eqns {α : Type _} (it : Nat → α → α) (f : α → α) (h0 : ∀ x, it 0 x = x)
    (hs : ∀ k x, it (k + 1) x = it k (f x)) (k : Nat) (x : α) : it (k + 1) x = f (it k x) := by
  induction k generalizing x with
  | zero => rw [hs, h0, h0]
  | succ k ih => rw [hs, ih, hs]

/-- Simulation of an iteration through a map `φ` (for example `BitVec.toNat`): if `f` acts as `g`
on every value satisfying an invariant `P` that `g` preserves, then `k` steps of `f` act as `k`
repetitions of `g`, for an iteration `it` with `it 0 x = x` and `it (k + 1) x = it k (f x)`. -/
theorem iter_map_of_sim {α β : Type _} (it : Nat → α → α) (f : α → α) (h0 : ∀ x, it 0 x = x)
    (hs : ∀ k x, it (k + 1) x = it k (f x)) (φ : α → β) (g : β → β) (P : β → Prop)
    (hf : ∀ y, P (φ y) → φ (f y) = g (φ y)) (hP : ∀ b, P b → P (g b)) (k : Nat) (x : α)
    (hx : P (φ x)) : φ (it k x) = Nat.repeat g k (φ x) := by
  induction k generalizing x with
  | zero => rw [h0]; rfl
  | succ k ih =>
    rw [hs, ih (f x) (by rw [hf x hx]; exact hP _ hx), hf x hx, repeat_succ']

/-- Under the hypotheses of `iter_map_of_sim`, every iterate satisfies the invariant. -/
theorem iter_map_invariant {α β : Type _} (it : Nat → α → α) (f : α → α) (h0 : ∀ x, it 0 x = x)
    (hs : ∀ k x, it (k + 1) x = it k (f x)) (φ : α → β) (g : β → β) (P : β → Prop)
    (hf : ∀ y, P (φ y) → φ (f y) = g (φ y)) (hP : ∀ b, P b → P (g b)) (k : Nat) (x : α)
    (hx : P (φ x)) : P (φ (it k x)) := by
  induction k generalizing x with
  | zero => rw [h0]; exact hx
  | succ k ih => rw [hs]; exact ih (f x) (by rw [hf x hx]; exact hP _ hx)

end ProofForgeFin.WordBridge

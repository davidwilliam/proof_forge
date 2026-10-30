import ProofForgeFin.Evm.Uint
/-!
# Bit operations: checked shifts, most significant bit, base-2 logarithm

* Left shifts with overflow detection. `checkedShl x k` returns `x <<< k` when no bit is shifted
  out and reverts otherwise. Three tests found in deployed code are proved equivalent to the
  exact condition `x * 2^k < 2^w`: comparing with a mask (`x < 1 << (w - k)`, Cetus
  `checked_shlw` after pull request 7), testing the high bits (`x >> (w - k) == 0`), and shifting
  back (`(x << k) >> k == x`). This generalizes `Word.mul_two_pow_lt_iff` to every shift amount.
* `mostSignificantBit`: a port of Uniswap v3 `BitMath.mostSignificantBit`, proved equal to
  `Nat.log2` on every nonzero `uint256`.
* `log2Ceil`: the base-2 logarithm rounded up (OpenZeppelin `Math.log2(x, Rounding.Ceil)`), with
  two-sided bounds for both roundings.
* `trailingZeros`: the exponent of the largest power of two dividing a number (the `twos` factor
  of `FullMath.mulDiv`).
-/

namespace ProofForgeFin.Evm

variable {w : Nat}

/-! ## Shift overflow -/

/-- `a * 2^k` fits in `w` bits exactly when `a` fits in `w - k` bits, for every shift amount `k`
(for `k > w` both sides say `a = 0`). -/
theorem mul_two_pow_lt_iff' {a k w : Nat} : a * 2 ^ k < 2 ^ w ↔ a < 2 ^ (w - k) := by
  by_cases hk : k ≤ w
  · exact mul_two_pow_lt_iff hk
  · have hw : w - k = 0 := by omega
    rw [hw, Nat.pow_zero]
    have hlt : 2 ^ w < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
    constructor
    · intro h
      refine Nat.lt_of_not_le fun ha => ?_
      have : 2 ^ k ≤ a * 2 ^ k := Nat.le_mul_of_pos_left _ ha
      omega
    · intro h
      have : a = 0 := by omega
      subst this; simp [Nat.two_pow_pos]

/-- A left shift that reverts when a bit would be shifted out (Cetus `checked_shlw` for
`k = 64`, Solidity code that tests a shift before performing it). -/
def checkedShl (x : BitVec w) (k : Nat) : Option (BitVec w) :=
  if x.toNat * 2 ^ k < 2 ^ w then some (x <<< k) else none

/-- A checked shift is the exact product `x * 2^k`, if it fits. -/
theorem checkedShl_eq_fit (x : BitVec w) (k : Nat) : checkedShl x k = fit w (x.toNat * 2 ^ k) := by
  unfold checkedShl fit
  by_cases h : x.toNat * 2 ^ k < 2 ^ w
  · simp only [h, ite_true, Option.some.injEq]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shiftLeft_of_lt x k h, toNat_ofNat_of_lt h]
  · simp [h]

/-- `checkedShl x k = some z` exactly when `x < 2^(w - k)` and `z` is `x * 2^k`. -/
theorem checkedShl_eq_some_iff {x z : BitVec w} {k : Nat} :
    checkedShl x k = some z ↔ x.toNat < 2 ^ (w - k) ∧ z.toNat = x.toNat * 2 ^ k := by
  rw [checkedShl_eq_fit, fit_eq_some_iff, mul_two_pow_lt_iff']

/-- A checked shift reverts exactly when `x ≥ 2^(w - k)`. -/
@[simp] theorem checkedShl_eq_none_iff {x : BitVec w} {k : Nat} :
    checkedShl x k = none ↔ 2 ^ (w - k) ≤ x.toNat := by
  rw [checkedShl_eq_fit, fit_eq_none_iff]
  have := (mul_two_pow_lt_iff' (a := x.toNat) (k := k) (w := w))
  omega

/-- A wrapping left shift loses no bit exactly when `x < 2^(w - k)`, and is then exact. -/
theorem toNat_shiftLeft_eq_iff {x : BitVec w} {k : Nat} :
    (x <<< k).toNat = x.toNat * 2 ^ k ↔ x.toNat < 2 ^ (w - k) := by
  rw [← mul_two_pow_lt_iff', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  constructor
  · intro h; rw [← h]; exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · exact Nat.mod_eq_of_lt

/-- The shift-back test, `(x << k) >> k == x`: true exactly when no bit is lost. -/
theorem shiftLeft_ushiftRight_eq_iff {x : BitVec w} {k : Nat} :
    (x <<< k) >>> k = x ↔ x.toNat < 2 ^ (w - k) := by
  rw [← mul_two_pow_lt_iff', BitVec.toNat_eq, toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  constructor
  · intro h
    have h1 : x.toNat * 2 ^ k % 2 ^ w / 2 ^ k * 2 ^ k ≤ x.toNat * 2 ^ k % 2 ^ w :=
      Nat.div_mul_le_self _ _
    rw [h] at h1
    exact Nat.lt_of_le_of_lt h1 (Nat.mod_lt _ (Nat.two_pow_pos w))
  · intro h
    rw [Nat.mod_eq_of_lt h, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

/-- A right shift by `j` is zero exactly when `x < 2^j` (the test `x >> (w - k) == 0` of the
fixed `checked_shlw`, with `j = w - k`). -/
theorem ushiftRight_eq_zero_iff {x : BitVec w} {j : Nat} : x >>> j = 0 ↔ x.toNat < 2 ^ j := by
  rw [eq_zero_iff_toNat, toNat_ushiftRight, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos j)]

/-- The value of the mask `1 << j` for `j < w`. -/
theorem toNat_one_shiftLeft {j : Nat} (h : j < w) : ((1 : BitVec w) <<< j).toNat = 2 ^ j := by
  have h1 : (1 : BitVec w).toNat = 1 := by
    show (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  rw [BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)

/-- The mask test `x < 1 << j` for `j < w` is `x < 2^j`. -/
theorem lt_one_shiftLeft_iff {x : BitVec w} {j : Nat} (h : j < w) :
    x < (1 : BitVec w) <<< j ↔ x.toNat < 2 ^ j := by
  rw [BitVec.lt_def, toNat_one_shiftLeft h]

/-- The mask test `x >= 1 << j` for `j < w` is `2^j ≤ x` (the overflow test of Cetus
`checked_shlw` after pull request 7, with `j = 192`). -/
theorem one_shiftLeft_le_iff {x : BitVec w} {j : Nat} (h : j < w) :
    (1 : BitVec w) <<< j ≤ x ↔ 2 ^ j ≤ x.toNat := by
  rw [BitVec.le_def, toNat_one_shiftLeft h]

/-! ## Base-2 logarithm -/

/-- `Nat.log2 n` is the unique `m` with `2^m ≤ n < 2^(m+1)`, for `n ≠ 0`. -/
theorem log2_eq_iff {n m : Nat} (hn : n ≠ 0) : Nat.log2 n = m ↔ 2 ^ m ≤ n ∧ n < 2 ^ (m + 1) := by
  rw [← Nat.le_log2 hn, ← Nat.log2_lt hn]
  omega

/-- The floor logarithm bounds: `2^(log2 n) ≤ n < 2^(log2 n + 1)` for `n ≠ 0`. -/
theorem log2_spec {n : Nat} (hn : n ≠ 0) : 2 ^ Nat.log2 n ≤ n ∧ n < 2 ^ (Nat.log2 n + 1) :=
  (log2_eq_iff hn).1 rfl

/-- `k ≤ log2 n` exactly when `2^k ≤ n`. -/
theorem le_log2_iff {n k : Nat} (hn : n ≠ 0) : k ≤ Nat.log2 n ↔ 2 ^ k ≤ n := Nat.le_log2 hn

/-- `log2 n < k` exactly when `n < 2^k`. -/
theorem log2_lt_iff {n k : Nat} (hn : n ≠ 0) : Nat.log2 n < k ↔ n < 2 ^ k := Nat.log2_lt hn

/-- Dividing by `2^k` lowers the logarithm by `k`. -/
theorem log2_div_two_pow (n k : Nat) : Nat.log2 (n / 2 ^ k) = Nat.log2 n - k := by
  by_cases h : 2 ^ k ≤ n
  · have hn : n ≠ 0 := by have := Nat.two_pow_pos k; omega
    have hq : n / 2 ^ k ≠ 0 := by
      rw [Ne, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)]; omega
    have hk : k ≤ Nat.log2 n := (Nat.le_log2 hn).2 h
    rw [log2_eq_iff hq]
    have ⟨h1, h2⟩ := log2_spec hn
    constructor
    · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k), ← Nat.pow_add]
      rw [Nat.sub_add_cancel hk]; exact h1
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add]
      have : Nat.log2 n - k + 1 + k = Nat.log2 n + 1 := by omega
      rw [this]; exact h2
  · have h0 : n / 2 ^ k = 0 := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).2 (by omega)
    rw [h0]
    by_cases hn : n = 0
    · subst hn; simp [Nat.log2_zero]
    · have : Nat.log2 n < k := (Nat.log2_lt hn).2 (by omega)
      rw [Nat.log2_zero]
      omega

/-- The logarithm is monotone. -/
theorem log2_mono {m n : Nat} (hm : m ≠ 0) (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  rw [Nat.le_log2 (by omega)]
  exact Nat.le_trans (log2_spec hm).1 h

/-- The base-2 logarithm rounded up: the least `r` with `n ≤ 2^r`. This is OpenZeppelin
`Math.log2(value, Rounding.Ceil)`: `log2(value) + (1 << log2(value) < value ? 1 : 0)`. -/
def log2Ceil (n : Nat) : Nat := if 2 ^ Nat.log2 n < n then Nat.log2 n + 1 else Nat.log2 n

/-- The ceiling logarithm covers `n`: `n ≤ 2^(log2Ceil n)`. -/
theorem le_two_pow_log2Ceil (n : Nat) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil
  by_cases hn : n = 0
  · subst hn; simp
  · have := log2_spec hn
    split <;> omega

/-- The ceiling logarithm is the least such exponent: `2^(log2Ceil n - 1) < n` when
`log2Ceil n > 0`. -/
theorem two_pow_pred_log2Ceil_lt {n : Nat} (h : 0 < log2Ceil n) : 2 ^ (log2Ceil n - 1) < n := by
  by_cases hn : n = 0
  · subst hn; exact absurd h (by decide)
  have ⟨h1, h2⟩ := log2_spec hn
  unfold log2Ceil at h ⊢
  by_cases hc : 2 ^ Nat.log2 n < n
  · rw [ite_eq_left hc] at h ⊢
    rw [Nat.add_sub_cancel]; exact hc
  · rw [ite_eq_right hc] at h ⊢
    have : 2 ^ (Nat.log2 n - 1) < 2 ^ Nat.log2 n := Nat.pow_lt_pow_right (by decide) (by omega)
    omega

/-- `log2Ceil n ≤ r` exactly when `n ≤ 2^r`. -/
theorem log2Ceil_le_iff {n r : Nat} : log2Ceil n ≤ r ↔ n ≤ 2 ^ r := by
  constructor
  · intro h; exact Nat.le_trans (le_two_pow_log2Ceil n) (Nat.pow_le_pow_right (by decide) h)
  · intro h
    refine Nat.le_of_not_lt fun hlt => ?_
    have h1 := two_pow_pred_log2Ceil_lt (Nat.lt_of_le_of_lt (Nat.zero_le r) hlt)
    have : 2 ^ r ≤ 2 ^ (log2Ceil n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Rounding the logarithm up adds at most one: `log2 n ≤ log2Ceil n ≤ log2 n + 1`, with
equality on the left exactly for powers of two (and zero). -/
theorem log2_le_log2Ceil (n : Nat) : Nat.log2 n ≤ log2Ceil n ∧ log2Ceil n ≤ Nat.log2 n + 1 := by
  unfold log2Ceil; split <;> omega

/-- The ceiling logarithm equals the floor logarithm exactly on powers of two and zero. -/
theorem log2Ceil_eq_log2_iff {n : Nat} : log2Ceil n = Nat.log2 n ↔ n ≤ 2 ^ Nat.log2 n := by
  unfold log2Ceil; split <;> omega

/-! ## `BitMath.mostSignificantBit` -/

/-- One line of `BitMath.mostSignificantBit`: `if (x >= 2^k) { x >>= k; r += k; }`. The state
is `(x, r)`. -/
def msbStep (k : Nat) (s : BitVec 256 × Nat) : BitVec 256 × Nat :=
  if BitVec.ofNat 256 (2 ^ k) ≤ s.1 then (s.1 >>> k, s.2 + k) else s

/-- Uniswap v3 `BitMath.mostSignificantBit(uint256 x) returns (uint8 r)`:

```
require(x > 0);
if (x >= 0x100000000000000000000000000000000) { x >>= 128; r += 128; }
if (x >= 0x10000000000000000) { x >>= 64; r += 64; }
if (x >= 0x100000000) { x >>= 32; r += 32; }
if (x >= 0x10000) { x >>= 16; r += 16; }
if (x >= 0x100) { x >>= 8; r += 8; }
if (x >= 0x10) { x >>= 4; r += 4; }
if (x >= 0x4) { x >>= 2; r += 2; }
if (x >= 0x2) r += 1;
```

Each line is `msbStep` with the constant `2^k` (`k` = 128, 64, ..., 1); the last line does not
shift `x`, which is not read afterwards, so `msbStep 1` computes the same `r`. The `require` is
`none`. -/
def mostSignificantBit (x : U256) : Option Nat :=
  if x = 0 then none
  else some ([128, 64, 32, 16, 8, 4, 2, 1].foldl (fun s k => msbStep k s) (x, 0)).2

/-- One step of the binary search keeps `r + log2 x` and halves the bit width bound. -/
theorem msbStep_spec {k : Nat} (hk : k < 256) {s : BitVec 256 × Nat}
    (hx : s.1.toNat ≠ 0) (hlt : s.1.toNat < 2 ^ (2 * k)) :
    (msbStep k s).1.toNat ≠ 0 ∧ (msbStep k s).1.toNat < 2 ^ k ∧
      (msbStep k s).2 + Nat.log2 (msbStep k s).1.toNat = s.2 + Nat.log2 s.1.toNat := by
  obtain ⟨x, r⟩ := s
  have hc : (BitVec.ofNat 256 (2 ^ k)).toNat = 2 ^ k :=
    toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hk)
  unfold msbStep
  by_cases h : BitVec.ofNat 256 (2 ^ k) ≤ x
  · have h' : 2 ^ k ≤ x.toNat := by rw [BitVec.le_def, hc] at h; exact h
    simp only [h, ite_true, toNat_ushiftRight]
    have hk' : k ≤ Nat.log2 x.toNat := (Nat.le_log2 hx).2 h'
    refine ⟨?_, ?_, ?_⟩
    · rw [Ne, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)]; omega
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add]
      rw [show k + k = 2 * k by omega]; exact hlt
    · rw [log2_div_two_pow]; omega
  · have h' : x.toNat < 2 ^ k := by
      rw [BitVec.le_def, hc] at h; omega
    rw [ite_eq_right h]
    exact ⟨hx, h', rfl⟩

/-- `mostSignificantBit` reverts exactly on zero. -/
@[simp] theorem mostSignificantBit_eq_none_iff {x : U256} : mostSignificantBit x = none ↔ x = 0 := by
  unfold mostSignificantBit; split <;> simp_all

/-- `BitMath.mostSignificantBit` computes the floor base-2 logarithm on every nonzero
`uint256`: `2^r ≤ x < 2^(r+1)`. -/
theorem mostSignificantBit_eq {x : U256} (hx : x ≠ 0) :
    mostSignificantBit x = some (Nat.log2 x.toNat) := by
  unfold mostSignificantBit
  rw [ite_eq_right hx]
  have h0 : x.toNat ≠ 0 := fun e => hx (eq_zero_iff_toNat.2 e)
  simp only [List.foldl_cons, List.foldl_nil, Option.some.injEq]
  obtain ⟨a1, b1, c1⟩ := msbStep_spec (k := 128) (s := (x, 0)) (by decide) h0 x.isLt
  generalize msbStep 128 (x, 0) = s1 at a1 b1 c1 ⊢
  obtain ⟨a2, b2, c2⟩ := msbStep_spec (k := 64) (s := s1) (by decide) a1 b1
  generalize msbStep 64 s1 = s2 at a2 b2 c2 ⊢
  obtain ⟨a3, b3, c3⟩ := msbStep_spec (k := 32) (s := s2) (by decide) a2 b2
  generalize msbStep 32 s2 = s3 at a3 b3 c3 ⊢
  obtain ⟨a4, b4, c4⟩ := msbStep_spec (k := 16) (s := s3) (by decide) a3 b3
  generalize msbStep 16 s3 = s4 at a4 b4 c4 ⊢
  obtain ⟨a5, b5, c5⟩ := msbStep_spec (k := 8) (s := s4) (by decide) a4 b4
  generalize msbStep 8 s4 = s5 at a5 b5 c5 ⊢
  obtain ⟨a6, b6, c6⟩ := msbStep_spec (k := 4) (s := s5) (by decide) a5 b5
  generalize msbStep 4 s5 = s6 at a6 b6 c6 ⊢
  obtain ⟨a7, b7, c7⟩ := msbStep_spec (k := 2) (s := s6) (by decide) a6 b6
  generalize msbStep 2 s6 = s7 at a7 b7 c7 ⊢
  obtain ⟨a8, b8, c8⟩ := msbStep_spec (k := 1) (s := s7) (by decide) a7 b7
  generalize msbStep 1 s7 = s8 at a8 b8 c8 ⊢
  have hone : s8.1.toNat = 1 := by have : (2 : Nat) ^ 1 = 2 := rfl; omega
  rw [hone, show Nat.log2 1 = 0 by decide] at c8
  simp only at c1
  omega

/-- The bounds of `mostSignificantBit`: `2^r ≤ x < 2^(r+1)`. -/
theorem mostSignificantBit_spec {x : U256} {r : Nat} (h : mostSignificantBit x = some r) :
    2 ^ r ≤ x.toNat ∧ x.toNat < 2 ^ (r + 1) := by
  have hx : x ≠ 0 := fun e => by rw [e] at h; exact absurd h (by simp [mostSignificantBit])
  rw [mostSignificantBit_eq hx, Option.some.injEq] at h
  subst h
  exact log2_spec fun e => hx (eq_zero_iff_toNat.2 e)

/-! ## Trailing zeros -/

/-- The number of trailing zero bits of `n`: the exponent of the largest power of two dividing
a nonzero `n` (0 for `n = 0`). -/
def trailingZeros (n : Nat) : Nat :=
  if h : n = 0 then 0 else if n % 2 = 1 then 0 else trailingZeros (n / 2) + 1
termination_by n
decreasing_by omega

/-- A nonzero `n` is `2^(trailingZeros n)` times an odd number. -/
theorem trailingZeros_spec {n : Nat} (hn : n ≠ 0) :
    n % 2 ^ trailingZeros n = 0 ∧ n / 2 ^ trailingZeros n % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [trailingZeros, dite_eq_right hn]
    by_cases h : n % 2 = 1
    · simp [h, Nat.mod_one]
    · simp only [h, ite_false]
      have h2 : n / 2 ≠ 0 := by omega
      have ⟨ih1, ih2⟩ := ih (n / 2) (by omega) h2
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      refine ⟨?_, ih2⟩
      rw [Nat.mod_mul]
      have : n % 2 = 0 := by omega
      rw [this, Nat.zero_add, ih1, Nat.mul_zero]

/-- `2^(trailingZeros n)` divides `n`. -/
theorem two_pow_trailingZeros_dvd (n : Nat) : 2 ^ trailingZeros n ∣ n := by
  by_cases hn : n = 0
  · subst hn; exact Nat.dvd_zero _
  · exact Nat.dvd_of_mod_eq_zero (trailingZeros_spec hn).1

/-- A nonzero number below `2^w` has fewer than `w` trailing zeros. -/
theorem trailingZeros_lt {n : Nat} (hn : n ≠ 0) (h : n < 2 ^ w) : trailingZeros n < w := by
  refine Nat.lt_of_not_le fun hle => ?_
  have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (two_pow_trailingZeros_dvd n)
  have : 2 ^ w ≤ 2 ^ trailingZeros n := Nat.pow_le_pow_right (by decide) hle
  omega

end ProofForgeFin.Evm

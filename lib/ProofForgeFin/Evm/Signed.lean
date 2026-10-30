import ProofForgeFin.Evm.Uint
/-!
# Signed integers: `int256` semantics and the three integer divisions

Solidity's `intN` and the EVM's `SDIV` and `SMOD` round the quotient toward zero (`Int.tdiv`)
and give the remainder the sign of the dividend (`Int.tmod`). Specifications usually need the
floor (`Int.fdiv`, which equals Lean's `/` for a positive divisor) or the ceiling (`cdiv`). This
module relates the three:

* for a positive divisor, `fdiv a b ≤ tdiv a b ≤ cdiv a b`, with `tdiv = fdiv` for `a ≥ 0` and
  `tdiv = cdiv` for `a ≤ 0`, and exact two-sided bounds for each;
* `fdiv_eq_tdiv_sub` is the floor computed from the truncated quotient as deployed code does it
  (Uniswap v3 `TickBitmap.position`'s caller `nextInitializedTickWithinOneWord`:
  `compressed = tick / tickSpacing; if (tick < 0 && tick % tickSpacing != 0) compressed--`).

A signed word of `n + 1` bits (`int256` is `BitVec 256`, `n = 255`) has the value `x.toInt` in
`[-2^n, 2^n)`. Checked signed arithmetic (Solidity 0.8) reverts exactly when the exact result
leaves that range; `checkedSDiv` also reverts on a zero divisor and for `type(int).min / -1`.
The module also gives OpenZeppelin `SafeCast.toInt256` and `SafeCast.toUint256`,
`SignedMath.abs`, and Uniswap v3 `LiquidityMath.addDelta` (a `uint128` plus an `int128`).
-/

namespace ProofForgeFin.Evm

/-! ## Floor, ceiling and truncation -/

/-- Integer division rounded up (toward positive infinity): `⌈a / b⌉ = -⌊-a / b⌋`. -/
def cdiv (a b : Int) : Int := -((-a).fdiv b)

/-- Floor division by a positive divisor is Lean's `/`. -/
theorem fdiv_eq_ediv' (a : Int) {b : Int} (hb : 0 < b) : a.fdiv b = a / b :=
  Int.fdiv_eq_ediv_of_nonneg a (Int.le_of_lt hb)

/-- Floor bounds: `fdiv a b * b ≤ a < (fdiv a b + 1) * b` for `0 < b`. -/
theorem fdiv_spec (a : Int) {b : Int} (hb : 0 < b) :
    a.fdiv b * b ≤ a ∧ a < (a.fdiv b + 1) * b := by
  rw [fdiv_eq_ediv' a hb]
  exact ⟨Int.ediv_mul_le a (Int.ne_of_gt hb), Int.lt_ediv_add_one_mul_self a hb⟩

/-- Ceiling bounds: `a ≤ cdiv a b * b < a + b` for `0 < b`. -/
theorem cdiv_spec (a : Int) {b : Int} (hb : 0 < b) : a ≤ cdiv a b * b ∧ cdiv a b * b < a + b := by
  have ⟨h1, h2⟩ := fdiv_spec (-a) hb
  unfold cdiv
  rw [Int.neg_mul]
  rw [Int.add_mul, Int.one_mul] at h2
  omega

/-- `q ≤ fdiv a b` exactly when `q * b ≤ a`, for `0 < b`. -/
theorem le_fdiv_iff {a b q : Int} (hb : 0 < b) : q ≤ a.fdiv b ↔ q * b ≤ a := by
  have ⟨h1, h2⟩ := fdiv_spec a hb
  constructor
  · intro h; exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hb)) h1
  · intro h
    refine Int.not_lt.1 fun hlt => ?_
    have : (a.fdiv b + 1) * b ≤ q * b := Int.mul_le_mul_of_nonneg_right hlt (Int.le_of_lt hb)
    omega

/-- `cdiv a b ≤ q` exactly when `a ≤ q * b`, for `0 < b`. -/
theorem cdiv_le_iff {a b q : Int} (hb : 0 < b) : cdiv a b ≤ q ↔ a ≤ q * b := by
  unfold cdiv
  have := le_fdiv_iff (a := -a) (q := -q) hb
  rw [Int.neg_mul] at this
  omega

/-- A number with the two floor bounds is the floor quotient. -/
theorem fdiv_eq_of_bounds {a b q : Int} (hb : 0 < b) (h1 : q * b ≤ a) (h2 : a < (q + 1) * b) :
    a.fdiv b = q := by
  have hle := (le_fdiv_iff hb).2 h1
  have hlt : a.fdiv b < q + 1 := by
    refine Int.not_le.1 fun h => ?_
    have := (le_fdiv_iff hb).1 h
    omega
  omega

/-- A number with the two ceiling bounds is the ceiling quotient. -/
theorem cdiv_eq_of_bounds {a b q : Int} (hb : 0 < b) (h1 : a ≤ q * b) (h2 : q * b < a + b) :
    cdiv a b = q := by
  have hle := (cdiv_le_iff hb).2 h1
  have hgt : q - 1 < cdiv a b := by
    refine Int.not_le.1 fun h => ?_
    have := (cdiv_le_iff hb).1 h
    rw [Int.sub_mul, Int.one_mul] at this
    omega
  omega

/-- For a nonnegative dividend and a positive divisor, truncation is the floor. -/
theorem tdiv_eq_fdiv_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) : a.tdiv b = a.fdiv b := by
  rw [Int.tdiv_eq_ediv_of_nonneg ha, fdiv_eq_ediv' a hb]

/-- For a nonpositive dividend and a positive divisor, truncation is the ceiling. -/
theorem tdiv_eq_cdiv_of_nonpos {a b : Int} (ha : a ≤ 0) (hb : 0 < b) : a.tdiv b = cdiv a b := by
  unfold cdiv
  have : a.tdiv b = -((-a).tdiv b) := by rw [Int.neg_tdiv, Int.neg_neg]
  rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega), fdiv_eq_ediv' _ hb]

/-- The floor is at most the ceiling, which is at most one more. -/
theorem fdiv_le_cdiv (a : Int) {b : Int} (hb : 0 < b) :
    a.fdiv b ≤ cdiv a b ∧ cdiv a b ≤ a.fdiv b + 1 := by
  have ⟨f1, f2⟩ := fdiv_spec a hb
  have ⟨c1, c2⟩ := cdiv_spec a hb
  constructor
  · exact Int.le_of_mul_le_mul_right (Int.le_trans f1 c1) hb
  · exact (cdiv_le_iff hb).2 (Int.le_of_lt f2)

/-- Truncation lies between the floor and the ceiling. -/
theorem fdiv_le_tdiv_le_cdiv (a : Int) {b : Int} (hb : 0 < b) :
    a.fdiv b ≤ a.tdiv b ∧ a.tdiv b ≤ cdiv a b := by
  have := fdiv_le_cdiv a hb
  by_cases ha : 0 ≤ a
  · rw [tdiv_eq_fdiv_of_nonneg ha hb]; omega
  · rw [tdiv_eq_cdiv_of_nonpos (by omega) hb]; omega

/-- The floor equals the ceiling exactly when the divisor divides the dividend. -/
theorem fdiv_eq_cdiv_iff (a : Int) {b : Int} (hb : 0 < b) : a.fdiv b = cdiv a b ↔ b ∣ a := by
  have ⟨f1, f2⟩ := fdiv_spec a hb
  have ⟨c1, c2⟩ := cdiv_spec a hb
  constructor
  · intro h
    refine ⟨a.fdiv b, ?_⟩
    rw [Int.mul_comm, h]; rw [h] at f1; omega
  · rintro ⟨c, rfl⟩
    rw [fdiv_eq_of_bounds hb (q := c) (by rw [Int.mul_comm]; omega)
      (by rw [Int.add_mul, Int.one_mul, Int.mul_comm]; omega),
      cdiv_eq_of_bounds hb (q := c) (by rw [Int.mul_comm]; omega) (by rw [Int.mul_comm]; omega)]

/-- The truncated remainder is zero exactly when the divisor divides the dividend. -/
theorem tmod_eq_zero_iff (a b : Int) : a.tmod b = 0 ↔ b ∣ a := by
  rw [Int.tmod_def]
  constructor
  · intro h; exact ⟨a.tdiv b, by omega⟩
  · rintro ⟨c, rfl⟩
    by_cases hb : b = 0
    · subst hb; simp
    · rw [Int.mul_tdiv_cancel_left _ hb]; simp

/-- The floor from the truncated quotient, as deployed code computes it: subtract one when the
dividend is negative and the division is inexact. -/
theorem fdiv_eq_tdiv_sub (a : Int) {b : Int} (hb : 0 < b) :
    a.fdiv b = a.tdiv b - (if a < 0 ∧ a.tmod b ≠ 0 then 1 else 0) := by
  by_cases ha : 0 ≤ a
  · rw [tdiv_eq_fdiv_of_nonneg ha hb, ite_eq_right (by omega)]; omega
  · rw [tdiv_eq_cdiv_of_nonpos (by omega) hb]
    have hd := fdiv_le_cdiv a hb
    have he := fdiv_eq_cdiv_iff a hb
    by_cases hm : a.tmod b = 0
    · rw [ite_eq_right (by omega)]
      have := he.2 ((tmod_eq_zero_iff a b).1 hm); omega
    · rw [ite_eq_left ⟨by omega, hm⟩]
      have : a.fdiv b ≠ cdiv a b := fun e => hm ((tmod_eq_zero_iff a b).2 (he.1 e))
      omega

/-- The ceiling from the truncated quotient: add one when the dividend is positive and the
division is inexact. -/
theorem cdiv_eq_tdiv_add (a : Int) {b : Int} (hb : 0 < b) :
    cdiv a b = a.tdiv b + (if 0 < a ∧ a.tmod b ≠ 0 then 1 else 0) := by
  by_cases ha : a ≤ 0
  · rw [tdiv_eq_cdiv_of_nonpos ha hb, ite_eq_right (by omega)]; omega
  · rw [tdiv_eq_fdiv_of_nonneg (by omega) hb]
    have hd := fdiv_le_cdiv a hb
    have he := fdiv_eq_cdiv_iff a hb
    by_cases hm : a.tmod b = 0
    · rw [ite_eq_right (by omega)]
      have := he.2 ((tmod_eq_zero_iff a b).1 hm); omega
    · rw [ite_eq_left ⟨by omega, hm⟩]
      have : a.fdiv b ≠ cdiv a b := fun e => hm ((tmod_eq_zero_iff a b).2 (he.1 e))
      omega

/-- Truncation never increases the magnitude: `|tdiv a b| = |a| / |b|`. -/
theorem natAbs_tdiv' (a b : Int) : (a.tdiv b).natAbs = a.natAbs / b.natAbs := Int.natAbs_tdiv a b

/-- Truncated division bounds for a positive divisor: the product `tdiv a b * b` has the sign of
`a`, is at most `|a|` in magnitude, and is within `b` of `a`. -/
theorem tdiv_spec (a : Int) {b : Int} (hb : 0 < b) :
    (0 ≤ a → a.tdiv b * b ≤ a ∧ a < a.tdiv b * b + b) ∧
      (a ≤ 0 → a ≤ a.tdiv b * b ∧ a.tdiv b * b < a + b) := by
  constructor
  · intro ha
    rw [tdiv_eq_fdiv_of_nonneg ha hb]
    have := fdiv_spec a hb; rw [Int.add_mul, Int.one_mul] at this; exact this
  · intro ha
    rw [tdiv_eq_cdiv_of_nonpos ha hb]; exact cdiv_spec a hb

/-- The truncated remainder has the sign of the dividend and is below the divisor in magnitude,
for a positive divisor. -/
theorem tmod_spec (a : Int) {b : Int} (hb : 0 < b) :
    a = a.tdiv b * b + a.tmod b ∧ (0 ≤ a → 0 ≤ a.tmod b ∧ a.tmod b < b) ∧
      (a ≤ 0 → -b < a.tmod b ∧ a.tmod b ≤ 0) := by
  have hdef := Int.tmod_def a b
  have ⟨h1, h2⟩ := tdiv_spec a hb
  rw [Int.mul_comm b] at hdef
  refine ⟨by omega, fun ha => ?_, fun ha => ?_⟩
  · have := h1 ha; omega
  · have := h2 ha; omega

/-! ## Signed words -/

/-- A Solidity `int256`. -/
abbrev I256 := BitVec 256

/-- The range of a signed `(n + 1)`-bit integer: `-2^n ≤ i < 2^n`. -/
def InRange (n : Nat) (i : Int) : Prop := -(2 ^ n : Int) ≤ i ∧ i < 2 ^ n

instance (n : Nat) (i : Int) : Decidable (InRange n i) := by unfold InRange; infer_instance

/-- The value of a signed word is in range. -/
theorem toInt_inRange {n : Nat} (x : BitVec (n + 1)) : InRange n x.toInt := by
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  simp only [Nat.add_sub_cancel] at h1 h2
  exact ⟨h1, h2⟩

/-- Reduction modulo `2^(n+1)` into the signed range leaves an in-range number unchanged. -/
theorem bmod_eq_of_inRange {n : Nat} {i : Int} (h : InRange n i) : i.bmod (2 ^ (n + 1)) = i := by
  have h2 : ((2 ^ (n + 1) : Nat) : Int) = 2 * (2 ^ n : Int) := by
    rw [Nat.pow_succ, Int.natCast_mul]; simp [Int.mul_comm]
  apply Int.bmod_eq_of_le
  · rw [h2]; have := h.1; omega
  · rw [h2]; have := h.2; omega

/-- `BitVec.ofInt` keeps an in-range value. -/
theorem toInt_ofInt_of_inRange {n : Nat} {i : Int} (h : InRange n i) :
    (BitVec.ofInt (n + 1) i).toInt = i := by
  rw [BitVec.toInt_ofInt, bmod_eq_of_inRange h]

/-- `type(intN).min`, the value `-2^n`. -/
theorem toInt_intMin' (n : Nat) : (BitVec.intMin (n + 1)).toInt = -(2 ^ n : Int) := by
  rw [BitVec.toInt_intMin, Nat.add_sub_cancel,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  simp

/-- Checked signed addition: reverts when the exact sum leaves the range. -/
def checkedSAdd {n : Nat} (x y : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if InRange n (x.toInt + y.toInt) then some (x + y) else none

/-- Checked signed subtraction. -/
def checkedSSub {n : Nat} (x y : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if InRange n (x.toInt - y.toInt) then some (x - y) else none

/-- Checked signed multiplication. -/
def checkedSMul {n : Nat} (x y : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if InRange n (x.toInt * y.toInt) then some (x * y) else none

/-- Checked negation: reverts on `type(intN).min`. -/
def checkedSNeg {n : Nat} (x : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if InRange n (-x.toInt) then some (-x) else none

/-- Solidity 0.8 signed division: `Panic(0x12)` on a zero divisor, `Panic(0x11)` for
`type(intN).min / -1`, and otherwise the EVM's `SDIV` (rounded toward zero). -/
def checkedSDiv {n : Nat} (x y : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if y.toInt = 0 ∨ (x.toInt = -(2 ^ n : Int) ∧ y.toInt = -1) then none else some (x.sdiv y)

/-- Solidity 0.8 signed remainder: reverts on a zero divisor, otherwise the EVM's `SMOD` (the
sign of the dividend). -/
def checkedSMod {n : Nat} (x y : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if y.toInt = 0 then none else some (x.srem y)

/-- `checkedSAdd x y = some z` exactly when the sum is in range and `z` is the sum. -/
theorem checkedSAdd_eq_some_iff {n : Nat} {x y z : BitVec (n + 1)} :
    checkedSAdd x y = some z ↔ InRange n (x.toInt + y.toInt) ∧ z.toInt = x.toInt + y.toInt := by
  unfold checkedSAdd
  by_cases h : InRange n (x.toInt + y.toInt)
  · rw [ite_eq_left h, Option.some.injEq, ← BitVec.toInt_inj, BitVec.toInt_add, bmod_eq_of_inRange h]
    exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩
  · simp [h]

/-- `checkedSSub x y = some z` exactly when the difference is in range and `z` is it. -/
theorem checkedSSub_eq_some_iff {n : Nat} {x y z : BitVec (n + 1)} :
    checkedSSub x y = some z ↔ InRange n (x.toInt - y.toInt) ∧ z.toInt = x.toInt - y.toInt := by
  unfold checkedSSub
  by_cases h : InRange n (x.toInt - y.toInt)
  · rw [ite_eq_left h, Option.some.injEq, ← BitVec.toInt_inj, BitVec.toInt_sub, bmod_eq_of_inRange h]
    exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩
  · simp [h]

/-- `checkedSMul x y = some z` exactly when the product is in range and `z` is it. -/
theorem checkedSMul_eq_some_iff {n : Nat} {x y z : BitVec (n + 1)} :
    checkedSMul x y = some z ↔ InRange n (x.toInt * y.toInt) ∧ z.toInt = x.toInt * y.toInt := by
  unfold checkedSMul
  by_cases h : InRange n (x.toInt * y.toInt)
  · rw [ite_eq_left h, Option.some.injEq, ← BitVec.toInt_inj, BitVec.toInt_mul, bmod_eq_of_inRange h]
    exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩
  · simp [h]

/-- `checkedSNeg x = some z` exactly when `x` is not `type(intN).min`, and then `z = -x`. -/
theorem checkedSNeg_eq_some_iff {n : Nat} {x z : BitVec (n + 1)} :
    checkedSNeg x = some z ↔ x.toInt ≠ -(2 ^ n : Int) ∧ z.toInt = -x.toInt := by
  have hr := toInt_inRange x
  unfold InRange at hr
  unfold checkedSNeg
  by_cases h : InRange n (-x.toInt)
  · rw [ite_eq_left h, Option.some.injEq, ← BitVec.toInt_inj, BitVec.toInt_neg, bmod_eq_of_inRange h]
    unfold InRange at h
    exact ⟨fun e => ⟨by omega, e.symm⟩, fun e => e.2.symm⟩
  · rw [ite_eq_right h]
    constructor
    · intro e; cases e
    · rintro ⟨hne, _⟩
      exact (h ⟨by omega, by omega⟩).elim

/-- The truncated quotient of two in-range values is in range except for `-2^n / -1`. -/
theorem tdiv_inRange {n : Nat} {a b : Int} (ha : InRange n a) (hb : b ≠ 0)
    (h : ¬ (a = -(2 ^ n : Int) ∧ b = -1)) : InRange n (a.tdiv b) := by
  unfold InRange at *
  have habs := Int.natAbs_tdiv a b
  have hb1 : 1 ≤ b.natAbs := by have := Int.natAbs_pos.2 hb; omega
  have hle : (a.tdiv b).natAbs ≤ a.natAbs := by rw [habs]; exact Nat.div_le_self _ _
  have hpow : ((2 ^ n : Nat) : Int) = (2 ^ n : Int) := by simp
  by_cases hb2 : b.natAbs = 1
  · rcases Int.natAbs_eq b with e | e <;> rw [hb2] at e
    · subst e; rw [show ((1 : Nat) : Int) = 1 from rfl, Int.tdiv_one]; exact ha
    · subst e
      rw [show (-((1 : Nat) : Int)) = -1 by rfl, Int.tdiv_neg, Int.tdiv_one]
      have : a ≠ -(2 ^ n : Int) := fun e => h ⟨e, rfl⟩
      omega
  · have h2 : 2 ≤ b.natAbs := by omega
    have hq : (a.tdiv b).natAbs ≤ a.natAbs / 2 := by
      rw [habs]; exact Nat.div_le_div_left h2 (by decide)
    have hn : a.natAbs ≤ 2 ^ n := by omega
    have : a.natAbs / 2 < 2 ^ n := by
      have := Nat.two_pow_pos n; omega
    omega

/-- `checkedSDiv` reverts exactly on a zero divisor and on `type(intN).min / -1`, and otherwise
returns the quotient rounded toward zero. -/
theorem checkedSDiv_eq_some_iff {n : Nat} {x y z : BitVec (n + 1)} :
    checkedSDiv x y = some z ↔
      (y.toInt ≠ 0 ∧ ¬ (x.toInt = -(2 ^ n : Int) ∧ y.toInt = -1)) ∧
        z.toInt = x.toInt.tdiv y.toInt := by
  unfold checkedSDiv
  by_cases h : y.toInt = 0 ∨ (x.toInt = -(2 ^ n : Int) ∧ y.toInt = -1)
  · rw [ite_eq_left h]
    constructor
    · intro e; cases e
    · rintro ⟨⟨h1, h2⟩, _⟩
      rcases h with h | h
      · exact absurd h h1
      · exact absurd h h2
  · rw [ite_eq_right h, Option.some.injEq, ← BitVec.toInt_inj, BitVec.toInt_sdiv]
    have hr := tdiv_inRange (toInt_inRange x) (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
    rw [bmod_eq_of_inRange hr]
    exact ⟨fun e => ⟨⟨fun e' => h (Or.inl e'), fun e' => h (Or.inr e')⟩, e.symm⟩,
      fun e => e.2.symm⟩

/-- Checked signed division reverts exactly when the divisor is zero or the quotient overflows. -/
theorem checkedSDiv_eq_none_iff {n : Nat} {x y : BitVec (n + 1)} :
    checkedSDiv x y = none ↔ y.toInt = 0 ∨ (x.toInt = -(2 ^ n : Int) ∧ y.toInt = -1) := by
  unfold checkedSDiv
  by_cases h : y.toInt = 0 ∨ (x.toInt = -(2 ^ n : Int) ∧ y.toInt = -1) <;> simp [h]

/-- `checkedSMod x y = some z` exactly when `y ≠ 0`, and then `z` is the truncated remainder. -/
theorem checkedSMod_eq_some_iff {n : Nat} {x y z : BitVec (n + 1)} :
    checkedSMod x y = some z ↔ y.toInt ≠ 0 ∧ z.toInt = x.toInt.tmod y.toInt := by
  unfold checkedSMod
  by_cases h : y.toInt = 0
  · simp [h]
  · rw [ite_eq_right h, Option.some.injEq, ← BitVec.toInt_inj, BitVec.toInt_srem]
    exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩

/-! ## Conversions -/

/-- The signed value of a word below `2^n` is its unsigned value. -/
theorem toInt_of_lt {n : Nat} {x : BitVec (n + 1)} (h : x.toNat < 2 ^ n) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by rw [Nat.pow_succ]; omega)]

/-- The signed value of a word at least `2^n` is its unsigned value minus `2^(n+1)`. -/
theorem toInt_of_le {n : Nat} {x : BitVec (n + 1)} (h : 2 ^ n ≤ x.toNat) :
    x.toInt = (x.toNat : Int) - ((2 ^ (n + 1) : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, ite_eq_right (by rw [Nat.pow_succ]; omega)]

/-- OpenZeppelin `SafeCast.toInt256(uint256 value)`: reverts when `value > type(int256).max`. -/
def toIntChecked {n : Nat} (x : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if x.toNat < 2 ^ n then some x else none

/-- `toIntChecked x = some z` exactly when `x < 2^n`, and then the signed value of `z` is the
unsigned value of `x`. -/
theorem toIntChecked_eq_some_iff {n : Nat} {x z : BitVec (n + 1)} :
    toIntChecked x = some z ↔ x.toNat < 2 ^ n ∧ z.toInt = (x.toNat : Int) := by
  unfold toIntChecked
  by_cases h : x.toNat < 2 ^ n
  · rw [ite_eq_left h, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨h, toInt_of_lt h⟩
    · rintro ⟨_, e⟩
      apply BitVec.eq_of_toInt_eq; rw [e, toInt_of_lt h]
  · simp [h]

/-- OpenZeppelin `SafeCast.toUint256(int256 value)`: reverts when `value < 0`. -/
def toUintChecked {n : Nat} (x : BitVec (n + 1)) : Option (BitVec (n + 1)) :=
  if x.toInt < 0 then none else some x

/-- `toUintChecked x = some z` exactly when `0 ≤ x`, and then the unsigned value of `z` is the
signed value of `x`. -/
theorem toUintChecked_eq_some_iff {n : Nat} {x z : BitVec (n + 1)} :
    toUintChecked x = some z ↔ 0 ≤ x.toInt ∧ (z.toNat : Int) = x.toInt := by
  unfold toUintChecked
  by_cases h : x.toInt < 0
  · rw [ite_eq_left h]
    constructor
    · intro e; cases e
    · rintro ⟨h', _⟩; omega
  · rw [ite_eq_right h, Option.some.injEq]
    have hx : x.toNat < 2 ^ n := by
      refine Nat.lt_of_not_le fun h' => h ?_
      rw [toInt_of_le h']; have := x.isLt; omega
    constructor
    · rintro rfl; exact ⟨by omega, (toInt_of_lt hx).symm⟩
    · rintro ⟨_, e⟩
      apply BitVec.eq_of_toNat_eq
      rw [toInt_of_lt hx] at e; omega

/-- OpenZeppelin `SignedMath.abs(int256 n)`: `unchecked { uint256(n >= 0 ? n : -n) }`. -/
def absW {n : Nat} (x : BitVec (n + 1)) : BitVec (n + 1) := if 0 ≤ x.toInt then x else -x

/-- `SignedMath.abs` returns the magnitude on every input, `type(int256).min` included (its
negation wraps to itself, whose unsigned value is `2^255`). -/
theorem toNat_absW {n : Nat} (x : BitVec (n + 1)) : (absW x).toNat = x.toInt.natAbs := by
  unfold absW
  by_cases h : 0 ≤ x.toInt
  · rw [ite_eq_left h]
    have hx : x.toNat < 2 ^ n := by
      refine Nat.lt_of_not_le fun h' => ?_
      rw [toInt_of_le h'] at h; have := x.isLt; omega
    rw [toInt_of_lt hx]; rfl
  · rw [ite_eq_right h]
    have hx : 2 ^ n ≤ x.toNat := by
      refine Nat.le_of_not_lt fun h' => h ?_
      rw [toInt_of_lt h']; omega
    have hl := x.isLt
    rw [toInt_of_le hx, BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## `LiquidityMath.addDelta` -/

/-- Uniswap v3 `LiquidityMath.addDelta(uint128 x, int128 y)`:

```
if (y < 0) { require((z = x - uint128(-y)) < x, 'LS'); }
else { require((z = x + uint128(y)) >= x, 'LA'); }
```

(Solidity 0.7: the arithmetic wraps; `uint128(-y)` reinterprets the bits.) -/
def addDelta (x : U128) (y : BitVec 128) : Option U128 :=
  if y.toInt < 0 then
    let z := x - (-y)
    if z < x then some z else none
  else
    let z := x + y
    if z ≥ x then some z else none

/-- `addDelta x y` succeeds exactly when `x + y` (signed `y`) is a valid `uint128`, and returns it. -/
theorem addDelta_eq_some_iff {x : U128} {y : BitVec 128} {z : U128} :
    addDelta x y = some z ↔
      0 ≤ (x.toNat : Int) + y.toInt ∧ (x.toNat : Int) + y.toInt < 2 ^ 128 ∧
        (z.toNat : Int) = (x.toNat : Int) + y.toInt := by
  have hx := x.isLt
  have habs := toNat_absW (n := 127) y
  unfold absW at habs
  unfold addDelta
  by_cases hy : y.toInt < 0
  · rw [ite_eq_left hy]
    rw [ite_eq_right (by omega)] at habs
    have hyn : ((-y).toNat : Int) = -y.toInt := by rw [habs]; omega
    have hpos : 0 < (-y).toNat := by omega
    dsimp only
    by_cases hlt : x - -y < x
    · rw [ite_eq_left hlt, Option.some.injEq]
      rw [BitVec.lt_def] at hlt
      have hle : (-y).toNat ≤ x.toNat := by
        refine Nat.le_of_not_lt fun h' => ?_
        rw [toNat_sub_of_lt h'] at hlt; have := (-y).isLt; omega
      have hv : (x - -y).toNat = x.toNat - (-y).toNat := toNat_sub_of_le _ _ hle
      constructor
      · rintro rfl; refine ⟨by omega, by omega, by rw [hv]; omega⟩
      · rintro ⟨_, _, e⟩
        apply BitVec.eq_of_toNat_eq; rw [hv]; omega
    · rw [ite_eq_right hlt]
      simp only [reduceCtorEq, false_iff, not_and]
      intro h1 _
      exfalso; apply hlt
      rw [BitVec.lt_def, toNat_sub_of_le _ _ (by omega)]
      omega
  · rw [ite_eq_right hy]
    rw [ite_eq_left (by omega)] at habs
    have hyn : (y.toNat : Int) = y.toInt := by rw [habs]; omega
    dsimp only
    by_cases hge : x + y ≥ x
    · rw [ite_eq_left hge, Option.some.injEq]
      rw [GE.ge, BitVec.le_def] at hge
      have hfit : x.toNat + y.toNat < 2 ^ 128 := by
        refine Nat.lt_of_not_le fun h' => ?_
        rw [toNat_add_of_le h'] at hge; have := y.isLt; have := (toInt_inRange (n := 127) y).2; omega
      have hv := toNat_add_of_lt x y hfit
      constructor
      · rintro rfl; refine ⟨by omega, by omega, by rw [hv]; omega⟩
      · rintro ⟨_, _, e⟩
        apply BitVec.eq_of_toNat_eq; rw [hv]; omega
    · rw [ite_eq_right hge]
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ h2
      exfalso; apply hge
      rw [GE.ge, BitVec.le_def, toNat_add_of_lt x y (by omega)]
      omega

end ProofForgeFin.Evm

import ProofForgeFin.Word
/-!
# Unsigned machine words: wrapping and checked arithmetic

A Solidity `uint256`, a Move `u256` or a Rust `u128` is modeled as `BitVec w`: its value is
`x.toNat`, a natural number below `2^w`.

Why `BitVec w` and not a natural number with a bound: the ports of contract code in this
repository (`rw-cetus-shlw`) are written over `BitVec`, whose `+`, `-`, `*` and `<<<` wrap modulo
`2^w` exactly as the EVM's `ADD`, `SUB`, `MUL` and `SHL` and Solidity's `unchecked` blocks do,
and whose `/` returns 0 for a zero divisor as the EVM's `DIV` does. `BitVec`'s `%` returns the
dividend for a zero divisor where the EVM's `MOD` returns 0, so ports use `evmMod` below. A port is
then a line-by-line translation. Every statement about a result is made through `toNat`, in unbounded
natural numbers, so a specification never mentions `BitVec` and the `Nat` lemmas of `Rounding`
and `FixedPoint` apply to it.

Checked arithmetic (Solidity 0.8 default, Move, Rust's `checked_*`) returns `Option`: `none` is
the revert (Solidity's `Panic(0x11)` on overflow and `Panic(0x12)` on a zero divisor, a Move
abort). Every checked operation is characterized in the same form: it returns `some z` exactly
when the exact natural-number result fits, and then `z.toNat` is that result (`fit`).

The module also proves the overflow tests deployed code uses equivalent to the overflow
condition: OpenZeppelin's `tryAdd` (`a + b < a`), `tryMul` (`(a * b) / a != b`), and the checks
the Solidity compiler emits (`x > max - y`, `x != 0 && y > max / x`).
-/

namespace ProofForgeFin.Evm

variable {w : Nat}

/-- A Solidity `uint256` or Move `u256`. -/
abbrev U256 := BitVec 256

/-- A Solidity `uint160` (the type of Uniswap v3 sqrt prices). -/
abbrev U160 := BitVec 160

/-- A Solidity `uint128` or Move `u128` (the type of Uniswap v3 liquidity). -/
abbrev U128 := BitVec 128

/-- A Solidity `uint64` or Move `u64`. -/
abbrev U64 := BitVec 64

/-! ## The exact result, if it fits -/

/-- The word with value `n`, if `n` fits in `w` bits, and `none` (a revert) otherwise. Every
checked operation of this module is `fit` of its exact natural-number result. -/
def fit (w n : Nat) : Option (BitVec w) := if n < 2 ^ w then some (BitVec.ofNat w n) else none

/-- `fit w n` succeeds exactly when `n < 2^w`, and then returns the word with value `n`. -/
theorem fit_eq_some_iff {w n : Nat} {z : BitVec w} : fit w n = some z ↔ n < 2 ^ w ∧ z.toNat = n := by
  unfold fit
  by_cases h : n < 2 ^ w
  · simp only [h, ite_true, Option.some.injEq, true_and]
    constructor
    · rintro rfl; exact toNat_ofNat_of_lt h
    · intro e; apply BitVec.eq_of_toNat_eq; rw [e, toNat_ofNat_of_lt h]
  · simp [h]

/-- `fit w n` reverts exactly when `n` does not fit. -/
@[simp] theorem fit_eq_none_iff {w n : Nat} : fit w n = none ↔ 2 ^ w ≤ n := by
  unfold fit; by_cases h : n < 2 ^ w <;> simp [h] <;> omega

/-- `fit w n` succeeds exactly when `n < 2^w`. -/
@[simp] theorem fit_isSome_iff {w n : Nat} : (fit w n).isSome ↔ n < 2 ^ w := by
  unfold fit; by_cases h : n < 2 ^ w <;> simp [h]

/-- The value of a successful `fit`. -/
theorem toNat_of_fit {w n : Nat} {z : BitVec w} (h : fit w n = some z) : z.toNat = n :=
  (fit_eq_some_iff.1 h).2

/-- The value of `fit`, through `toNat`: the exact result, or `none`. -/
theorem map_toNat_fit (w n : Nat) :
    (fit w n).map BitVec.toNat = if n < 2 ^ w then some n else none := by
  unfold fit; by_cases h : n < 2 ^ w <;> simp [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]

/-- `fit` of the value of a word is that word. -/
@[simp] theorem fit_toNat {w : Nat} (x : BitVec w) : fit w x.toNat = some x := by
  unfold fit; simp [x.isLt]

/-! ## Value range -/

/-- Every word is below `2^w`. -/
theorem toNat_lt (x : BitVec w) : x.toNat < 2 ^ w := x.isLt

/-- Every word is at most `2^w - 1` (`type(uintW).max`). -/
theorem toNat_le_max (x : BitVec w) : x.toNat ≤ 2 ^ w - 1 := by have := x.isLt; omega

/-- A word is zero exactly when its value is zero. -/
theorem eq_zero_iff_toNat {x : BitVec w} : x = 0 ↔ x.toNat = 0 := by
  rw [BitVec.toNat_eq]; simp

/-- A nonzero word has a positive value. -/
theorem toNat_pos_of_ne_zero {x : BitVec w} (h : x ≠ 0) : 0 < x.toNat :=
  Nat.pos_of_ne_zero fun e => h (eq_zero_iff_toNat.2 e)

/-- `type(uintW).max` is the all-ones word. -/
theorem toNat_allOnes' (w : Nat) : (BitVec.allOnes w).toNat = 2 ^ w - 1 := BitVec.toNat_allOnes

/-! ## Wrapping arithmetic (`unchecked`, EVM `ADD`, `SUB`, `MUL`, `DIV`, `MOD`) -/

/-- The EVM's `MOD`: the remainder, and 0 for a zero divisor (`BitVec`'s `%` returns the
dividend there). -/
def evmMod (x y : BitVec w) : BitVec w := if y = 0 then 0 else x % y

/-- The value of `MOD`: the remainder for a nonzero divisor, 0 otherwise. -/
theorem toNat_evmMod (x y : BitVec w) :
    (evmMod x y).toNat = if y.toNat = 0 then 0 else x.toNat % y.toNat := by
  unfold evmMod
  by_cases h : y = 0
  · subst h; simp
  · have : y.toNat ≠ 0 := fun e => h (eq_zero_iff_toNat.2 e)
    rw [ite_eq_right h, ite_eq_right this, BitVec.toNat_umod]

/-- The EVM's `DIV` returns 0 for a zero divisor, as `BitVec`'s `/` does. -/
theorem udiv_zero' (x : BitVec w) : (x / 0).toNat = 0 := by simp

/-- Wrapping addition without overflow is exact. -/
theorem toNat_add_of_lt' {x y : BitVec w} (h : x.toNat + y.toNat < 2 ^ w) :
    (x + y).toNat = x.toNat + y.toNat := toNat_add_of_lt x y h

/-- Wrapping addition with overflow loses exactly `2^w`. -/
theorem toNat_add_of_le {x y : BitVec w} (h : 2 ^ w ≤ x.toNat + y.toNat) :
    (x + y).toNat = x.toNat + y.toNat - 2 ^ w := by
  rw [BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

/-- Wrapping subtraction with underflow gains exactly `2^w`. -/
theorem toNat_sub_of_lt {x y : BitVec w} (h : x.toNat < y.toNat) :
    (x - y).toNat = 2 ^ w + x.toNat - y.toNat := by
  have hy := y.isLt
  rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Wrapping multiplication is the product modulo `2^w`. -/
theorem toNat_mul' (x y : BitVec w) : (x * y).toNat = x.toNat * y.toNat % 2 ^ w :=
  BitVec.toNat_mul x y

/-- The distance between two words without underflow, `x > y ? x - y : y - x` (the
`sqrt_price_diff` of Cetus `get_delta_a`, the sorted difference of Uniswap `getAmount0Delta`). -/
def absDiffW (x y : BitVec w) : BitVec w := if x > y then x - y else y - x

/-- The distance is `max - min` of the values. -/
theorem toNat_absDiffW (x y : BitVec w) :
    (absDiffW x y).toNat = max x.toNat y.toNat - min x.toNat y.toNat := by
  unfold absDiffW
  by_cases h : x > y
  · rw [ite_eq_left h]
    rw [GT.gt, BitVec.lt_def] at h
    rw [toNat_sub_of_le _ _ (Nat.le_of_lt h)]; omega
  · rw [ite_eq_right h]
    rw [GT.gt, BitVec.lt_def] at h
    rw [toNat_sub_of_le _ _ (by omega)]; omega

/-- The distance is zero exactly when the words are equal. -/
theorem absDiffW_eq_zero_iff {x y : BitVec w} : absDiffW x y = 0 ↔ x.toNat = y.toNat := by
  rw [eq_zero_iff_toNat, toNat_absDiffW]; omega

/-! ## Checked arithmetic (Solidity 0.8, Move, Rust `checked_*`) -/

/-- Checked addition: reverts (`none`) on overflow, as Solidity 0.8's `+` does
(`Panic(0x11)`). -/
def checkedAdd (x y : BitVec w) : Option (BitVec w) :=
  if x.toNat + y.toNat < 2 ^ w then some (x + y) else none

/-- Checked subtraction: reverts on underflow. -/
def checkedSub (x y : BitVec w) : Option (BitVec w) :=
  if y.toNat ≤ x.toNat then some (x - y) else none

/-- Checked multiplication: reverts on overflow. -/
def checkedMul (x y : BitVec w) : Option (BitVec w) :=
  if x.toNat * y.toNat < 2 ^ w then some (x * y) else none

/-- Checked division: reverts on a zero divisor (`Panic(0x12)`); otherwise the floor quotient. -/
def checkedDiv (x y : BitVec w) : Option (BitVec w) := if y = 0 then none else some (x / y)

/-- Checked remainder: reverts on a zero divisor. -/
def checkedMod (x y : BitVec w) : Option (BitVec w) := if y = 0 then none else some (x % y)

/-- Checked exponentiation `x ** n`: reverts when `x^n` does not fit. -/
def checkedPow (x : BitVec w) (n : Nat) : Option (BitVec w) := fit w (x.toNat ^ n)

/-- Checked narrowing conversion (OpenZeppelin `SafeCast.toUint128`, Move `(x as u64)`): reverts
when the value does not fit in `v` bits. -/
def checkedCast (v : Nat) (x : BitVec w) : Option (BitVec v) :=
  if x.toNat < 2 ^ v then some (x.setWidth v) else none

/-- Checked addition is the exact sum, if it fits. -/
theorem checkedAdd_eq_fit (x y : BitVec w) : checkedAdd x y = fit w (x.toNat + y.toNat) := by
  unfold checkedAdd fit
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · simp only [h, ite_true, Option.some.injEq]
    apply BitVec.eq_of_toNat_eq; rw [toNat_add_of_lt x y h, toNat_ofNat_of_lt h]
  · simp [h]

/-- Checked subtraction is the exact difference, if there is no underflow. -/
theorem checkedSub_eq (x y : BitVec w) :
    checkedSub x y = if y.toNat ≤ x.toNat then fit w (x.toNat - y.toNat) else none := by
  unfold checkedSub fit
  by_cases h : y.toNat ≤ x.toNat
  · have : x.toNat - y.toNat < 2 ^ w := by have := x.isLt; omega
    simp only [h, ite_true, this, Option.some.injEq]
    apply BitVec.eq_of_toNat_eq; rw [toNat_sub_of_le x y h, toNat_ofNat_of_lt this]
  · simp [h]

/-- Checked multiplication is the exact product, if it fits. -/
theorem checkedMul_eq_fit (x y : BitVec w) : checkedMul x y = fit w (x.toNat * y.toNat) := by
  unfold checkedMul fit
  by_cases h : x.toNat * y.toNat < 2 ^ w
  · simp only [h, ite_true, Option.some.injEq]
    apply BitVec.eq_of_toNat_eq; rw [toNat_mul_of_lt x y h, toNat_ofNat_of_lt h]
  · simp [h]

/-- `checkedAdd x y = some z` exactly when the sum fits and `z` is the sum. -/
theorem checkedAdd_eq_some_iff {x y z : BitVec w} :
    checkedAdd x y = some z ↔ x.toNat + y.toNat < 2 ^ w ∧ z.toNat = x.toNat + y.toNat := by
  rw [checkedAdd_eq_fit]; exact fit_eq_some_iff

/-- `checkedSub x y = some z` exactly when `y ≤ x` and `z` is the difference. -/
theorem checkedSub_eq_some_iff {x y z : BitVec w} :
    checkedSub x y = some z ↔ y.toNat ≤ x.toNat ∧ z.toNat = x.toNat - y.toNat := by
  rw [checkedSub_eq]
  by_cases h : y.toNat ≤ x.toNat
  · have : x.toNat - y.toNat < 2 ^ w := by have := x.isLt; omega
    simp only [h, ite_true, true_and, fit_eq_some_iff, this]
  · simp [h]

/-- `checkedMul x y = some z` exactly when the product fits and `z` is the product. -/
theorem checkedMul_eq_some_iff {x y z : BitVec w} :
    checkedMul x y = some z ↔ x.toNat * y.toNat < 2 ^ w ∧ z.toNat = x.toNat * y.toNat := by
  rw [checkedMul_eq_fit]; exact fit_eq_some_iff

/-- `checkedDiv x y = some z` exactly when `y ≠ 0` and `z` is the floor quotient. -/
theorem checkedDiv_eq_some_iff {x y z : BitVec w} :
    checkedDiv x y = some z ↔ y.toNat ≠ 0 ∧ z.toNat = x.toNat / y.toNat := by
  unfold checkedDiv
  by_cases h : y = 0
  · simp [h]
  · have : y.toNat ≠ 0 := fun e => h (eq_zero_iff_toNat.2 e)
    simp only [h, ite_false, Option.some.injEq, ne_eq, this, not_false_eq_true, true_and]
    rw [← BitVec.toNat_udiv, eq_comm, BitVec.toNat_eq]

/-- `checkedMod x y = some z` exactly when `y ≠ 0` and `z` is the remainder. -/
theorem checkedMod_eq_some_iff {x y z : BitVec w} :
    checkedMod x y = some z ↔ y.toNat ≠ 0 ∧ z.toNat = x.toNat % y.toNat := by
  unfold checkedMod
  by_cases h : y = 0
  · simp [h]
  · have : y.toNat ≠ 0 := fun e => h (eq_zero_iff_toNat.2 e)
    simp only [h, ite_false, Option.some.injEq, ne_eq, this, not_false_eq_true, true_and]
    rw [← BitVec.toNat_umod, eq_comm, BitVec.toNat_eq]

/-- `checkedPow x n = some z` exactly when `x^n` fits and `z` is `x^n`. -/
theorem checkedPow_eq_some_iff {x z : BitVec w} {n : Nat} :
    checkedPow x n = some z ↔ x.toNat ^ n < 2 ^ w ∧ z.toNat = x.toNat ^ n := fit_eq_some_iff

/-- `checkedCast v x = some z` exactly when the value fits in `v` bits and is kept. -/
theorem checkedCast_eq_some_iff {v : Nat} {x : BitVec w} {z : BitVec v} :
    checkedCast v x = some z ↔ x.toNat < 2 ^ v ∧ z.toNat = x.toNat := by
  unfold checkedCast
  by_cases h : x.toNat < 2 ^ v
  · simp only [h, ite_true, Option.some.injEq, true_and]
    rw [eq_comm, BitVec.toNat_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]
  · simp [h]

/-- Checked addition reverts exactly on overflow. -/
@[simp] theorem checkedAdd_eq_none_iff {x y : BitVec w} :
    checkedAdd x y = none ↔ 2 ^ w ≤ x.toNat + y.toNat := by
  rw [checkedAdd_eq_fit]; exact fit_eq_none_iff

/-- Checked subtraction reverts exactly on underflow. -/
@[simp] theorem checkedSub_eq_none_iff {x y : BitVec w} :
    checkedSub x y = none ↔ x.toNat < y.toNat := by
  unfold checkedSub; by_cases h : y.toNat ≤ x.toNat <;> simp [h] <;> omega

/-- Checked multiplication reverts exactly on overflow. -/
@[simp] theorem checkedMul_eq_none_iff {x y : BitVec w} :
    checkedMul x y = none ↔ 2 ^ w ≤ x.toNat * y.toNat := by
  rw [checkedMul_eq_fit]; exact fit_eq_none_iff

/-- Checked division reverts exactly on a zero divisor. -/
@[simp] theorem checkedDiv_eq_none_iff {x y : BitVec w} : checkedDiv x y = none ↔ y = 0 := by
  unfold checkedDiv; by_cases h : y = 0 <;> simp [h]

/-- Checked remainder reverts exactly on a zero divisor. -/
@[simp] theorem checkedMod_eq_none_iff {x y : BitVec w} : checkedMod x y = none ↔ y = 0 := by
  unfold checkedMod; by_cases h : y = 0 <;> simp [h]

/-- Checked exponentiation reverts exactly when `x^n` does not fit. -/
@[simp] theorem checkedPow_eq_none_iff {x : BitVec w} {n : Nat} :
    checkedPow x n = none ↔ 2 ^ w ≤ x.toNat ^ n := fit_eq_none_iff

/-- A checked narrowing conversion reverts exactly when the value does not fit. -/
@[simp] theorem checkedCast_eq_none_iff {v : Nat} {x : BitVec w} :
    checkedCast v x = none ↔ 2 ^ v ≤ x.toNat := by
  unfold checkedCast; by_cases h : x.toNat < 2 ^ v <;> simp [h] <;> omega

/-- The value of a successful checked addition is the exact sum. -/
theorem toNat_of_checkedAdd {x y z : BitVec w} (h : checkedAdd x y = some z) :
    z.toNat = x.toNat + y.toNat := (checkedAdd_eq_some_iff.1 h).2

/-- The value of a successful checked subtraction is the exact difference. -/
theorem toNat_of_checkedSub {x y z : BitVec w} (h : checkedSub x y = some z) :
    z.toNat = x.toNat - y.toNat := (checkedSub_eq_some_iff.1 h).2

/-- The value of a successful checked multiplication is the exact product. -/
theorem toNat_of_checkedMul {x y z : BitVec w} (h : checkedMul x y = some z) :
    z.toNat = x.toNat * y.toNat := (checkedMul_eq_some_iff.1 h).2

/-- The value of a successful checked division is the floor quotient. -/
theorem toNat_of_checkedDiv {x y z : BitVec w} (h : checkedDiv x y = some z) :
    z.toNat = x.toNat / y.toNat := (checkedDiv_eq_some_iff.1 h).2

/-- A checked addition that fits returns the wrapping sum. -/
theorem checkedAdd_of_lt {x y : BitVec w} (h : x.toNat + y.toNat < 2 ^ w) :
    checkedAdd x y = some (x + y) := by unfold checkedAdd; simp [h]

/-- A checked subtraction without underflow returns the wrapping difference. -/
theorem checkedSub_of_le {x y : BitVec w} (h : y.toNat ≤ x.toNat) :
    checkedSub x y = some (x - y) := by unfold checkedSub; simp [h]

/-- A checked multiplication that fits returns the wrapping product. -/
theorem checkedMul_of_lt {x y : BitVec w} (h : x.toNat * y.toNat < 2 ^ w) :
    checkedMul x y = some (x * y) := by unfold checkedMul; simp [h]

/-- A checked division by a nonzero word returns the quotient. -/
theorem checkedDiv_of_ne {x y : BitVec w} (h : y ≠ 0) : checkedDiv x y = some (x / y) := by
  unfold checkedDiv; rw [ite_eq_right h]

/-- Checked addition is commutative. -/
theorem checkedAdd_comm (x y : BitVec w) : checkedAdd x y = checkedAdd y x := by
  rw [checkedAdd_eq_fit, checkedAdd_eq_fit, Nat.add_comm]

/-- Checked multiplication is commutative. -/
theorem checkedMul_comm (x y : BitVec w) : checkedMul x y = checkedMul y x := by
  rw [checkedMul_eq_fit, checkedMul_eq_fit, Nat.mul_comm]

/-- A checked addition that succeeds is at least each summand: `x ≤ x + y`. -/
theorem le_of_checkedAdd {x y z : BitVec w} (h : checkedAdd x y = some z) : x.toNat ≤ z.toNat := by
  rw [toNat_of_checkedAdd h]; omega

/-- A checked subtraction that succeeds is at most the minuend. -/
theorem le_of_checkedSub {x y z : BitVec w} (h : checkedSub x y = some z) : z.toNat ≤ x.toNat := by
  rw [toNat_of_checkedSub h]; omega

/-! ## Overflow tests in deployed code -/

/-- OpenZeppelin `Math.tryAdd`, SafeMath `add` and the Solidity 0.8.x compiler's `checked_add`
(`sum := add(x, y); if gt(x, sum) { panic }`): the wrapped sum is below a summand exactly on
overflow. -/
theorem add_lt_left_iff {x y : BitVec w} : x + y < x ↔ 2 ^ w ≤ x.toNat + y.toNat := by
  rw [BitVec.lt_def]
  constructor
  · intro h
    refine Nat.le_of_not_lt fun h' => ?_
    rw [toNat_add_of_lt x y h'] at h; omega
  · intro h
    rw [toNat_add_of_le h]; have := y.isLt; omega

/-- The same test against the other summand. -/
theorem add_lt_right_iff {x y : BitVec w} : x + y < y ↔ 2 ^ w ≤ x.toNat + y.toNat := by
  rw [BitVec.add_comm, add_lt_left_iff, Nat.add_comm]

/-- The check of older Solidity compilers, `if gt(x, sub(max, y)) { panic }`: `max - y < x`
exactly on overflow (`max - y` never underflows). -/
theorem allOnes_sub_lt_iff {x y : BitVec w} :
    BitVec.allOnes w - y < x ↔ 2 ^ w ≤ x.toNat + y.toNat := by
  rw [BitVec.lt_def, toNat_sub_of_le _ _ (by rw [BitVec.toNat_allOnes]; exact toNat_le_max y),
    BitVec.toNat_allOnes]
  have := y.isLt; have := x.isLt
  omega

/-- OpenZeppelin `Math.trySub`, SafeMath `sub` and the compiler's `checked_sub`
(`if lt(x, y) { panic }`). -/
theorem lt_iff_checkedSub_eq_none {x y : BitVec w} : x < y ↔ checkedSub x y = none := by
  rw [BitVec.lt_def, checkedSub_eq_none_iff]

/-- OpenZeppelin `Math.tryMul`, SafeMath `mul` and the Solidity 0.8.x compiler's `checked_mul`
(`product := mul(x, y); if iszero(or(iszero(x), eq(y, div(product, x)))) { panic }`): for a
nonzero `x`, dividing the wrapped product by `x` fails to return `y` exactly on overflow. -/
theorem mul_div_ne_iff {x y : BitVec w} (hx : x ≠ 0) :
    x * y / x ≠ y ↔ 2 ^ w ≤ x.toNat * y.toNat := by
  have hx0 := toNat_pos_of_ne_zero hx
  rw [ne_eq, BitVec.toNat_eq, BitVec.toNat_udiv, BitVec.toNat_mul]
  constructor
  · intro h
    refine Nat.le_of_not_lt fun h' => h ?_
    rw [Nat.mod_eq_of_lt h', Nat.mul_comm, Nat.mul_div_cancel _ hx0]
  · intro h e
    have h1 : x.toNat * y.toNat % 2 ^ w / x.toNat * x.toNat ≤ x.toNat * y.toNat % 2 ^ w :=
      Nat.div_mul_le_self _ _
    rw [e] at h1
    have h2 := Nat.mod_lt (x.toNat * y.toNat) (Nat.two_pow_pos w)
    rw [Nat.mul_comm] at h1
    omega

/-- The check of older Solidity compilers for multiplication,
`if and(iszero(iszero(x)), gt(y, div(max, x))) { panic }`: exactly on overflow. -/
theorem allOnes_div_lt_iff {x y : BitVec w} :
    (x ≠ 0 ∧ BitVec.allOnes w / x < y) ↔ 2 ^ w ≤ x.toNat * y.toNat := by
  rw [BitVec.lt_def, BitVec.toNat_udiv, BitVec.toNat_allOnes]
  constructor
  · rintro ⟨hx, h⟩
    have hx0 := toNat_pos_of_ne_zero hx
    have := (Nat.div_lt_iff_lt_mul hx0).1 h
    rw [Nat.mul_comm] at this
    omega
  · intro h
    have hx : x ≠ 0 := by
      intro e
      rw [eq_zero_iff_toNat.1 e, Nat.zero_mul] at h
      exact absurd h (Nat.not_le_of_lt (Nat.two_pow_pos w))
    refine ⟨hx, (Nat.div_lt_iff_lt_mul (toNat_pos_of_ne_zero hx)).2 ?_⟩
    have := Nat.two_pow_pos w
    rw [Nat.mul_comm]; omega

/-- Overflow of `x * y` in terms of a quotient on natural numbers, for a positive `x`:
`2^w ≤ x * y` exactly when `(2^w - 1) / x < y`. -/
theorem two_pow_le_mul_iff {x y w : Nat} (hx : 0 < x) :
    2 ^ w ≤ x * y ↔ (2 ^ w - 1) / x < y := by
  rw [Nat.div_lt_iff_lt_mul hx, Nat.mul_comm y x]
  have := Nat.two_pow_pos w
  omega

end ProofForgeFin.Evm

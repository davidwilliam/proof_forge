import ProofForgeFin.Evm
/-!
# Demonstration: the five requirements of `rw-cetus-shlw` with the library

The definitions below are copied without change from
`realworld/tasks/rw-cetus-shlw/spec/ClmmMath/Spec.lean` (the Move routines `checked_shlw`,
`div_round`, `full_mul` and `get_delta_a`, and the five requirements), and the two shift
routines from `reference/SolutionA.lean` (the port of pull request 7, `n >= 1 << 192`) and
`reference/SolutionB.lean` (`n >> 192 == 0`).

The task proves the three requirements on `get_delta_a` for each reference routine with seven
helper lemmas of `spec/ClmmMath/Lemmas.lean` (the value of `fullMul` and `absDiff`, the floor and
ceiling bounds of `divRound`, a case analysis of `getDeltaA`) and per-routine lemmas on the flag
and the shifted value. Here:

* `fullMul`, `absDiff` and `divRound` are library operations: `Word.toNat_fullMul`,
  `Evm.absDiffW` and `Evm.divRound` (equal by `rfl`), whose values are `Evm.toNat_absDiffW` and
  `Evm.divRound_eq_some_iff`; the final `(q as u64)` is `Evm.checkedCast 64`;
* `deltaA_of_exact` proves REQ-DELTA-A-COVERS, REQ-DELTA-A-TIGHT and REQ-DELTA-A-FLOOR at once for
  every shift routine that meets REQ-SHLW-EXACT, from `Rounding.ceilDiv_spec` and
  `Rounding.floor_spec`;
* the shift requirements of both routines follow from `Evm.one_shiftLeft_le_iff`,
  `Evm.ushiftRight_eq_zero_iff` and `Evm.toNat_shiftLeft_eq_iff`.
-/

namespace ProofForgeFinDemo.Evm.Cetus

open ProofForgeFin ProofForgeFin.Evm

/-! ## Copied from `spec/ClmmMath/Spec.lean` -/

/-- A port of `checked_shlw(n: u256): (u256, bool)`: the shifted value and the overflow flag. -/
abbrev Shlw := BitVec 256 → BitVec 256 × Bool

/-- `integer_mate::full_math_u128::full_mul(num1: u128, num2: u128): u256`, which is
`(num1 as u256) * (num2 as u256)`. The product of two values below `2^128` is below `2^256`,
so this multiplication never aborts in Move and never wraps here. -/
def fullMul (a b : BitVec 128) : BitVec 256 :=
  a.setWidth 256 * b.setWidth 256

/-- `integer_mate::math_u256::div_round(num, denom, round_up)`:
`let p = num / denom; if (round_up && ((p * denom) != num)) { p + 1 } else { p }`.
Move's `/` aborts when `denom = 0` (`none`). Neither `p * denom` (at most `num`) nor `p + 1`
(reached only when `p * denom < num`, so `p < 2^256 - 1`) can overflow, so `BitVec`'s
wrapping operations agree with Move's aborting ones on every input. -/
def divRound (num denom : BitVec 256) (roundUp : Bool) : Option (BitVec 256) :=
  if denom = 0 then none
  else
    let p := num / denom
    if roundUp && p * denom != num then some (p + 1) else some p

/-- `sqrt_price_diff` in `get_delta_a`: `if (sqrt_price_0 > sqrt_price_1) { sqrt_price_0 -
sqrt_price_1 } else { sqrt_price_1 - sqrt_price_0 }`; neither subtraction underflows. -/
def absDiff (sqrtPrice0 sqrtPrice1 : BitVec 128) : BitVec 128 :=
  if sqrtPrice0 > sqrtPrice1 then sqrtPrice0 - sqrtPrice1 else sqrtPrice1 - sqrtPrice0

/-- `cetusclmm::clmm_math::get_delta_a`, with the shift routine as a parameter. -/
def getDeltaA (shlw : Shlw) (sqrtPrice0 sqrtPrice1 liquidity : BitVec 128) (roundUp : Bool) :
    Option (BitVec 64) :=
  let diff := absDiff sqrtPrice0 sqrtPrice1
  if diff = 0 ∨ liquidity = 0 then some 0
  else
    let r := shlw (fullMul liquidity diff)
    if r.2 then none
    else
      match divRound r.1 (fullMul sqrtPrice0 sqrtPrice1) roundUp with
      | none => none
      | some q => if q.toNat < 2 ^ 64 then some (q.setWidth 64) else none

/-- `|sqrt_price_1 - sqrt_price_0|` as a natural number. -/
def priceDiff (sqrtPrice0 sqrtPrice1 : BitVec 128) : Nat :=
  if sqrtPrice1.toNat ≤ sqrtPrice0.toNat then sqrtPrice0.toNat - sqrtPrice1.toNat
  else sqrtPrice1.toNat - sqrtPrice0.toNat

/-- The exact token-A amount times the denominator: `liquidity * |sqrt_price_1 - sqrt_price_0| * 2^64`.
The exact amount owed is this divided by `sqrt_price_0 * sqrt_price_1`. -/
def exactNumerator (sqrtPrice0 sqrtPrice1 liquidity : BitVec 128) : Nat :=
  liquidity.toNat * priceDiff sqrtPrice0 sqrtPrice1 * 2 ^ 64

/-- The denominator `sqrt_price_0 * sqrt_price_1` as a natural number. -/
def denominator (sqrtPrice0 sqrtPrice1 : BitVec 128) : Nat :=
  sqrtPrice0.toNat * sqrtPrice1.toNat

/-- REQ-SHLW-EXACT: when the shift reports no overflow, its result is exactly `n * 2^64`:
no bit is lost. -/
def ShlwExact (shlw : Shlw) : Prop :=
  ∀ n : BitVec 256, (shlw n).2 = false → (shlw n).1.toNat = n.toNat * 2 ^ 64

/-- REQ-SHLW-COMPLETE: when `n * 2^64` fits in 256 bits, the shift does not report overflow,
so no valid position is refused. -/
def ShlwComplete (shlw : Shlw) : Prop :=
  ∀ n : BitVec 256, n.toNat * 2 ^ 64 < 2 ^ 256 → (shlw n).2 = false

/-- REQ-DELTA-A-COVERS: rounding up (a deposit), the amount returned is at least the exact
amount owed for the liquidity. -/
def DeltaACovers (shlw : Shlw) : Prop :=
  ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64,
    getDeltaA shlw sp0 sp1 liquidity true = some amount →
    exactNumerator sp0 sp1 liquidity ≤ amount.toNat * denominator sp0 sp1

/-- REQ-DELTA-A-TIGHT: rounding up, the amount is less than one unit above the exact amount:
one unit less would not cover it. -/
def DeltaATight (shlw : Shlw) : Prop :=
  ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64,
    getDeltaA shlw sp0 sp1 liquidity true = some amount → 0 < amount.toNat →
    (amount.toNat - 1) * denominator sp0 sp1 < exactNumerator sp0 sp1 liquidity

/-- REQ-DELTA-A-FLOOR: rounding down (the pool pays), the amount returned is at most the exact
amount. -/
def DeltaAFloor (shlw : Shlw) : Prop :=
  ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64,
    getDeltaA shlw sp0 sp1 liquidity false = some amount →
    amount.toNat * denominator sp0 sp1 ≤ exactNumerator sp0 sp1 liquidity

/-! ## The task's operations are library operations -/

theorem divRound_eq : divRound = Evm.divRound := rfl

theorem absDiff_eq : absDiff = absDiffW := rfl

theorem toNat_fullMul' (a b : BitVec 128) : (fullMul a b).toNat = a.toNat * b.toNat :=
  toNat_fullMul a b

theorem toNat_absDiff (a b : BitVec 128) : (absDiff a b).toNat = priceDiff a b := by
  rw [absDiff_eq, toNat_absDiffW]; unfold priceDiff; split <;> omega

/-! ## The requirements on `get_delta_a`, for every exact shift routine -/

/-- The amount `get_delta_a` returns with an exact shift routine: zero when the exact amount is
zero, and otherwise the exact amount rounded in the requested direction. -/
theorem getDeltaA_value {shlw : Shlw} (hexact : ShlwExact shlw) {sp0 sp1 L : BitVec 128}
    {up : Bool} {amount : BitVec 64} (h : getDeltaA shlw sp0 sp1 L up = some amount) :
    exactNumerator sp0 sp1 L = 0 ∧ amount.toNat = 0 ∨
      0 < denominator sp0 sp1 ∧ amount.toNat = if up then
        ceilDiv (exactNumerator sp0 sp1 L) (denominator sp0 sp1)
        else exactNumerator sp0 sp1 L / denominator sp0 sp1 := by
  unfold getDeltaA at h
  dsimp only at h
  split at h
  · rename_i hz
    cases h
    left
    refine ⟨?_, rfl⟩
    unfold exactNumerator
    rcases hz with hz | hz
    · rw [← toNat_absDiff, hz]; simp
    · rw [hz]; simp
  · split at h
    · cases h
    · rename_i hf
      rw [Bool.not_eq_true] at hf
      rw [divRound_eq] at h
      split at h
      · cases h
      · rename_i q hq
        have hc : checkedCast 64 q = some amount := h
        have ⟨_, ha⟩ := checkedCast_eq_some_iff.1 hc
        have ⟨hd, hv⟩ := divRound_eq_some_iff.1 hq
        rw [hexact _ hf, toNat_fullMul', toNat_absDiff, toNat_fullMul'] at hv
        rw [toNat_fullMul'] at hd
        exact Or.inr ⟨hd, by rw [ha, hv]; rfl⟩

/-- REQ-DELTA-A-COVERS, REQ-DELTA-A-TIGHT and REQ-DELTA-A-FLOOR hold for every shift routine
that meets REQ-SHLW-EXACT. -/
theorem deltaA_of_exact {shlw : Shlw} (hexact : ShlwExact shlw) :
    DeltaACovers shlw ∧ DeltaATight shlw ∧ DeltaAFloor shlw := by
  refine ⟨fun sp0 sp1 L amount h => ?_, fun sp0 sp1 L amount h hpos => ?_,
    fun sp0 sp1 L amount h => ?_⟩
  · rcases getDeltaA_value hexact h with ⟨h0, _⟩ | ⟨hd, hv⟩
    · rw [h0]; exact Nat.zero_le _
    · rw [hv]; exact (ceilDiv_spec _ _ hd).1
  · rcases getDeltaA_value hexact h with ⟨_, h0⟩ | ⟨hd, hv⟩
    · omega
    · rw [ite_eq_left rfl] at hv
      have := (ceilDiv_spec (exactNumerator sp0 sp1 L) _ hd).2
      rw [← hv] at this
      have := Nat.le_mul_of_pos_left (denominator sp0 sp1) hpos
      rw [Nat.sub_mul, Nat.one_mul]; omega
  · rcases getDeltaA_value hexact h with ⟨h0, ha⟩ | ⟨hd, hv⟩
    · rw [h0, ha]; simp
    · rw [hv]; exact (floor_spec _ _ hd).1

/-! ## Copied from `reference/SolutionA.lean` (pull request 7) -/

namespace SolutionA

def checkedShlw : Shlw := fun n =>
  let mask : BitVec 256 := (1 : BitVec 256) <<< 192
  if n ≥ mask then (0, true) else (n <<< 64, false)

theorem eq_ite (n : BitVec 256) : checkedShlw n =
    if (1 : BitVec 256) <<< 192 ≤ n then ((0 : BitVec 256), true) else (n <<< 64, false) := rfl

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n h
  rw [eq_ite] at *
  have hc : ¬ (1 : BitVec 256) <<< 192 ≤ n := fun hc => by rw [ite_eq_left hc] at h; simp at h
  rw [ite_eq_right hc]
  rw [one_shiftLeft_le_iff (by decide)] at hc
  exact toNat_shiftLeft_eq_iff.2 (by omega)

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n h
  rw [eq_ite, ite_eq_right (by rw [one_shiftLeft_le_iff (by decide)]; rw [mul_two_pow_lt_iff'] at h; omega)]

theorem req_delta_a_covers : DeltaACovers checkedShlw := (deltaA_of_exact req_shlw_exact).1
theorem req_delta_a_tight : DeltaATight checkedShlw := (deltaA_of_exact req_shlw_exact).2.1
theorem req_delta_a_floor : DeltaAFloor checkedShlw := (deltaA_of_exact req_shlw_exact).2.2

end SolutionA

/-! ## Copied from `reference/SolutionB.lean` (`n >> 192 == 0`) -/

namespace SolutionB

def checkedShlw : Shlw := fun n =>
  if n >>> 192 = 0 then (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false) else (0, true)

theorem eq_ite (n : BitVec 256) : checkedShlw n =
    if n >>> 192 = 0 then (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false)
    else ((0 : BitVec 256), true) := rfl

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n h
  rw [eq_ite] at *
  have hc : n >>> 192 = 0 := Classical.byContradiction fun hc => by
    rw [ite_eq_right hc] at h; simp at h
  rw [ite_eq_left hc]
  rw [ushiftRight_eq_zero_iff] at hc
  exact toNat_ofNat_of_lt (by omega)

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n h
  rw [eq_ite, ite_eq_left (ushiftRight_eq_zero_iff.2 (by rw [mul_two_pow_lt_iff'] at h; exact h))]

theorem req_delta_a_covers : DeltaACovers checkedShlw := (deltaA_of_exact req_shlw_exact).1
theorem req_delta_a_tight : DeltaATight checkedShlw := (deltaA_of_exact req_shlw_exact).2.1
theorem req_delta_a_floor : DeltaAFloor checkedShlw := (deltaA_of_exact req_shlw_exact).2.2

end SolutionB

end ProofForgeFinDemo.Evm.Cetus

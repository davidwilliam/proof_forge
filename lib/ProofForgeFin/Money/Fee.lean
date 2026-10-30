import ProofForgeFin.FixedPoint
/-!
# Percentage fees, caps and minimums

A percentage fee on an amount `a` at rate `r` out of `scale` (basis points: `scale = 10000`;
percent: `100`; parts per million: `10^6`) is `a * r / scale` rounded down (`feeDown`, in the
payer's favour) or up (`feeUp`, in the collector's favour). Amounts are natural numbers of
minor units.

* Bounds: `feeDown_spec`, `feeUp_spec`; `feeDown_le_feeUp`, `feeUp_le_feeDown_add_one`.
* Fee plus net equals gross (`feeDown_add_net`, `feeUp_add_net`) for a rate at most the scale,
  and the net amount is itself a rounded percentage of the gross: after a fee rounded down the
  net is `ceilDiv (a * (scale - r)) scale` (`net_feeDown`), after a fee rounded up it is
  `a * (scale - r) / scale` (`net_feeUp`). So the net is monotone in the gross.
* Splitting a payment in two changes the fee by at most one unit (`feeDown_add_le`,
  `le_feeDown_add`, `feeUp_add_le`, `le_feeUp_add`).
* Caps and minimums (`clampFee lo hi f a`, the fee `f` raised to `lo`, capped at `hi` and never
  above the amount): bounds, monotonicity, and the net amount after a clamped percentage fee
  is monotone in the gross (`net_clampFeeDown_mono`).
* Gross-up: the least gross amount whose net after the fee is at least `n`
  (`le_net_feeUp_iff`, `le_net_feeDown_iff`).

Recurs in: `tasks/payouts-fee-*` (`feeOf bps amount = amount * bps / 10000`, `netOf`,
`feeCredit`).
-/

namespace ProofForgeFin.Money

/-- A fee of `r` out of `scale` on `a`, rounded down: `a * r / scale`. -/
def feeDown (scale r a : Nat) : Nat := a * r / scale

/-- A fee of `r` out of `scale` on `a`, rounded up. -/
def feeUp (scale r a : Nat) : Nat := ceilDiv (a * r) scale

/-- A fee in basis points, rounded down: `a * bps / 10000`. -/
abbrev bpsFee (bps a : Nat) : Nat := feeDown 10000 bps a

/-- The rounded-down fee is within one unit below the exact fee. -/
theorem feeDown_spec (scale r a : Nat) (hs : 0 < scale) :
    feeDown scale r a * scale ≤ a * r ∧ a * r < (feeDown scale r a + 1) * scale :=
  floor_spec _ _ hs

/-- The rounded-up fee is within one unit above the exact fee. -/
theorem feeUp_spec (scale r a : Nat) (hs : 0 < scale) :
    a * r ≤ feeUp scale r a * scale ∧ feeUp scale r a * scale < a * r + scale :=
  ceilDiv_spec _ _ hs

/-- Rounding the fee down never exceeds rounding it up. -/
theorem feeDown_le_feeUp (scale r a : Nat) : feeDown scale r a ≤ feeUp scale r a :=
  div_le_ceilDiv _ _

/-- Rounding the fee up adds at most one unit. -/
theorem feeUp_le_feeDown_add_one (scale r a : Nat) : feeUp scale r a ≤ feeDown scale r a + 1 :=
  ceilDiv_le_div_add_one _ _

/-- A fee at a rate at most the scale is at most the amount. -/
theorem feeDown_le (scale : Nat) {r : Nat} (a : Nat) (h : r ≤ scale) : feeDown scale r a ≤ a := by
  unfold feeDown
  rcases Nat.eq_zero_or_pos scale with hs | hs
  · subst hs; simp
  · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm scale a]; exact Nat.mul_le_mul_left a h)

/-- A fee rounded up at a rate at most the scale is at most the amount. -/
theorem feeUp_le {scale r : Nat} (a : Nat) (hs : 0 < scale) (h : r ≤ scale) : feeUp scale r a ≤ a :=
  (ceilDiv_le_iff hs).2 (Nat.mul_le_mul_left a h)

/-- Fee plus net equals gross. -/
theorem feeDown_add_net (scale : Nat) {r : Nat} (a : Nat) (h : r ≤ scale) :
    feeDown scale r a + (a - feeDown scale r a) = a := by
  have := feeDown_le scale a h; omega

/-- Fee plus net equals gross, for a fee rounded up. -/
theorem feeUp_add_net {scale r : Nat} (a : Nat) (hs : 0 < scale) (h : r ≤ scale) :
    feeUp scale r a + (a - feeUp scale r a) = a := by
  have := feeUp_le a hs h; omega

/-- After a fee rounded down, the net is the remaining percentage rounded up. -/
theorem net_feeDown {scale r : Nat} (a : Nat) (hs : 0 < scale) (h : r ≤ scale) :
    a - feeDown scale r a = ceilDiv (a * (scale - r)) scale := by
  obtain ⟨h1, h2⟩ := feeDown_spec scale r a hs
  rw [Nat.add_mul, Nat.one_mul] at h2
  have e : a * (scale - r) + a * r = a * scale := by rw [← Nat.mul_add, Nat.sub_add_cancel h]
  have hf : feeDown scale r a * scale ≤ a * scale := Nat.mul_le_mul_right _ (feeDown_le scale a h)
  refine (ceilDiv_eq_of_bounds hs ?_ ?_).symm <;> rw [Nat.sub_mul] <;> omega

/-- After a fee rounded up, the net is the remaining percentage rounded down. -/
theorem net_feeUp {scale r : Nat} (a : Nat) (hs : 0 < scale) (h : r ≤ scale) :
    a - feeUp scale r a = a * (scale - r) / scale := by
  obtain ⟨h1, h2⟩ := feeUp_spec scale r a hs
  have e : a * (scale - r) + a * r = a * scale := by rw [← Nat.mul_add, Nat.sub_add_cancel h]
  have hf : feeUp scale r a * scale ≤ a * scale := Nat.mul_le_mul_right _ (feeUp_le a hs h)
  refine (div_eq_of_bounds ?_ ?_).symm
  · rw [Nat.sub_mul]; omega
  · rw [Nat.add_mul, Nat.one_mul, Nat.sub_mul]; omega

/-- The fee is monotone in the amount and the rate. -/
theorem feeDown_mono (scale : Nat) {r r' a a' : Nat} (hr : r ≤ r') (ha : a ≤ a') :
    feeDown scale r a ≤ feeDown scale r' a' :=
  div_mono_left _ (Nat.mul_le_mul ha hr)

/-- The rounded-up fee is monotone in the amount and the rate. -/
theorem feeUp_mono (scale : Nat) {r r' a a' : Nat} (hr : r ≤ r') (ha : a ≤ a') :
    feeUp scale r a ≤ feeUp scale r' a' :=
  ceilDiv_mono_left _ (Nat.mul_le_mul ha hr)

/-- The net after a fee rounded down is monotone in the gross. -/
theorem net_feeDown_mono {scale r a a' : Nat} (hs : 0 < scale) (h : r ≤ scale) (ha : a ≤ a') :
    a - feeDown scale r a ≤ a' - feeDown scale r a' := by
  rw [net_feeDown a hs h, net_feeDown a' hs h]
  exact ceilDiv_mono_left _ (Nat.mul_le_mul_right _ ha)

/-- The net after a fee rounded up is monotone in the gross. -/
theorem net_feeUp_mono {scale r a a' : Nat} (hs : 0 < scale) (h : r ≤ scale) (ha : a ≤ a') :
    a - feeUp scale r a ≤ a' - feeUp scale r a' := by
  rw [net_feeUp a hs h, net_feeUp a' hs h]
  exact div_mono_left _ (Nat.mul_le_mul_right _ ha)

/-- Splitting a payment in two never raises the fee rounded down. -/
theorem feeDown_add_le (scale r a b : Nat) :
    feeDown scale r a + feeDown scale r b ≤ feeDown scale r (a + b) := by
  unfold feeDown; rw [Nat.add_mul]; exact div_add_div_le _ _ _

/-- Splitting a payment in two lowers the fee rounded down by at most one unit. -/
theorem le_feeDown_add (scale r a b : Nat) :
    feeDown scale r (a + b) ≤ feeDown scale r a + feeDown scale r b + 1 := by
  unfold feeDown; rw [Nat.add_mul]; exact div_add_le_div_add_div_add_one _ _ _

/-- Splitting a payment in two never lowers the fee rounded up. -/
theorem feeUp_add_le {scale : Nat} (r a b : Nat) (hs : 0 < scale) :
    feeUp scale r (a + b) ≤ feeUp scale r a + feeUp scale r b := by
  unfold feeUp
  apply (ceilDiv_le_iff hs).2
  rw [Nat.add_mul, Nat.add_mul]
  exact Nat.add_le_add (le_ceilDiv_mul _ _ hs) (le_ceilDiv_mul _ _ hs)

/-- Splitting a payment in two raises the fee rounded up by at most one unit. -/
theorem le_feeUp_add {scale : Nat} (r a b : Nat) (hs : 0 < scale) :
    feeUp scale r a + feeUp scale r b ≤ feeUp scale r (a + b) + 1 := by
  have h1 := ceilDiv_mul_lt (a * r) scale hs
  have h2 := ceilDiv_mul_lt (b * r) scale hs
  have h3 := le_ceilDiv_mul ((a + b) * r) scale hs
  have e : (a + b) * r = a * r + b * r := Nat.add_mul _ _ _
  unfold feeUp
  have : (ceilDiv (a * r) scale + ceilDiv (b * r) scale) * scale <
      (ceilDiv ((a + b) * r) scale + 1 + 1) * scale := by
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
  have := Nat.lt_of_mul_lt_mul_right this
  omega

/-- The fee rounded down rises by at most the rise of the amount when the rate is at most the
scale. -/
theorem feeDown_le_add (scale : Nat) {r : Nat} (a d : Nat) (h : r ≤ scale) :
    feeDown scale r (a + d) ≤ feeDown scale r a + d := by
  unfold feeDown
  rcases Nat.eq_zero_or_pos scale with hs | hs
  · subst hs; simp
  · have : (a + d) * r ≤ a * r + d * scale := by
      rw [Nat.add_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_left d h) _
    calc (a + d) * r / scale ≤ (a * r + d * scale) / scale := Nat.div_le_div_right this
      _ = a * r / scale + d := Nat.add_mul_div_right _ _ hs

/-! ## Caps and minimums -/

/-- A fee `f` raised to the minimum `lo`, capped at `hi`, and never above the amount `a`. -/
def clampFee (lo hi f a : Nat) : Nat := min a (min hi (max lo f))

/-- A clamped fee never exceeds the amount. -/
theorem clampFee_le_amount (lo hi f a : Nat) : clampFee lo hi f a ≤ a := Nat.min_le_left _ _

/-- A clamped fee never exceeds the cap. -/
theorem clampFee_le_cap (lo hi f a : Nat) : clampFee lo hi f a ≤ hi := by
  unfold clampFee; omega

/-- A clamped fee is at least the minimum when the minimum is below the cap and the amount. -/
theorem le_clampFee {lo hi : Nat} (f : Nat) {a : Nat} (h1 : lo ≤ hi) (h2 : lo ≤ a) :
    lo ≤ clampFee lo hi f a := by
  unfold clampFee; omega

/-- A fee between the minimum, the cap and the amount is not changed. -/
theorem clampFee_of_le {lo hi f a : Nat} (h1 : lo ≤ f) (h2 : f ≤ hi) (h3 : f ≤ a) :
    clampFee lo hi f a = f := by
  unfold clampFee; omega

/-- A clamped fee is monotone in the fee and the amount. -/
theorem clampFee_mono (lo hi : Nat) {f f' a a' : Nat} (hf : f ≤ f') (ha : a ≤ a') :
    clampFee lo hi f a ≤ clampFee lo hi f' a' := by
  unfold clampFee; omega

/-- Fee plus net equals gross for a clamped fee. -/
theorem clampFee_add_net (lo hi f a : Nat) : clampFee lo hi f a + (a - clampFee lo hi f a) = a := by
  have := clampFee_le_amount lo hi f a; omega

/-- The net after a clamped percentage fee rounded down is monotone in the gross: a larger
payment never nets less. -/
theorem net_clampFeeDown_mono (scale lo hi : Nat) {r a a' : Nat} (h : r ≤ scale) (ha : a ≤ a') :
    a - clampFee lo hi (feeDown scale r a) a ≤ a' - clampFee lo hi (feeDown scale r a') a' := by
  have h1 := feeDown_mono scale (Nat.le_refl r) ha
  have h2 := feeDown_le_add scale a (a' - a) h
  rw [Nat.add_sub_cancel' ha] at h2
  unfold clampFee
  omega

/-! ## Gross-up -/

/-- The least gross amount whose net after a fee of `r` out of `scale` rounded up is at least
`n`: `ceilDiv (n * scale) (scale - r)`. -/
def grossUpFeeUp (scale r n : Nat) : Nat := ceilDiv (n * scale) (scale - r)

/-- The net after a fee rounded up is at least `n` exactly when the gross is at least
`grossUpFeeUp scale r n`. -/
theorem le_net_feeUp_iff {scale r : Nat} (n a : Nat) (hs : 0 < scale) (h : r < scale) :
    n ≤ a - feeUp scale r a ↔ grossUpFeeUp scale r n ≤ a := by
  rw [net_feeUp a hs (Nat.le_of_lt h), le_div_iff hs, grossUpFeeUp, ceilDiv_le_iff (by omega)]

/-- The least gross amount whose net after a fee of `r` out of `scale` rounded down is at
least `n`: `0` for `n = 0`, else `(n - 1) * scale / (scale - r) + 1`. -/
def grossUpFeeDown (scale r n : Nat) : Nat := if n = 0 then 0 else (n - 1) * scale / (scale - r) + 1

/-- The net after a fee rounded down is at least `n` exactly when the gross is at least
`grossUpFeeDown scale r n`. -/
theorem le_net_feeDown_iff {scale r : Nat} (n a : Nat) (hs : 0 < scale) (h : r < scale) :
    n ≤ a - feeDown scale r a ↔ grossUpFeeDown scale r n ≤ a := by
  rw [net_feeDown a hs (Nat.le_of_lt h), grossUpFeeDown]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : n ≠ 0 := by omega
    simp only [hn', ↓reduceIte]
    rw [show n ≤ ceilDiv (a * (scale - r)) scale ↔ n - 1 < ceilDiv (a * (scale - r)) scale by omega,
      lt_ceilDiv_iff hs,
      show (n - 1) * scale / (scale - r) + 1 ≤ a ↔ (n - 1) * scale / (scale - r) < a by omega,
      div_lt_iff (by omega)]

/-- On a 10000-unit payment at 2.9% (290 basis points), the fee is 290 units; the fee is
rounded down on 1 unit to 0. -/
theorem bpsFee_example : bpsFee 290 10000 = 290 ∧ bpsFee 290 1 = 0 ∧ feeUp 10000 290 1 = 1 := by
  decide

end ProofForgeFin.Money

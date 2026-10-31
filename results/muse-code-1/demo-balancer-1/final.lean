import BalancerSwap.Spec
import ProofForgeFin.Rounding
import ProofForgeFin.FixedPoint
namespace BalancerSwap

/-! ## FixedPoint -/

/-- `FixedPoint.mulDown`. -/
def mulDown (a b : Nat) : Nat := a * b / ONE

/-- `FixedPoint.mulUp`. -/
def mulUp (a b : Nat) : Nat := if a * b = 0 then 0 else (a * b - 1) / ONE + 1

/-- `FixedPoint.divDown`: reverts on division by zero. -/
def divDown (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some (a * ONE / b)

/-- `FixedPoint.divUp`: reverts on division by zero. -/
def divUp (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)

/-- `FixedPoint.complement`. -/
def complement (x : Nat) : Nat := if x < ONE then ONE - x else 0

/-! ## BasePool -/

/-- `_upscale`: `FixedPoint.mulDown(amount, scalingFactor)`. -/
def upscale (amount scalingFactor : Nat) : Nat := mulDown amount scalingFactor

/-- `_upscaleArray` over the pool's balances. -/
def upscaleArray (p : Pool) : Nat → Nat := fun k => mulDown (p.balance k) (p.rate k)

/-- `_downscaleDown`. -/
def downscaleDown (amount scalingFactor : Nat) : Option Nat := divDown amount scalingFactor

/-- `_downscaleUp`. -/
def downscaleUp (amount scalingFactor : Nat) : Option Nat := divUp amount scalingFactor

/-- `_subtractSwapFeeAmount`: `amount.sub(amount.mulUp(fee))`. -/
def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none

/-- `_addSwapFeeAmount`: `amount.divUp(fee.complement())`. -/
def addSwapFeeAmount (amount fee : Nat) : Option Nat := divUp amount (complement fee)

/-! ## BaseGeneralPool -/

/-- `_swapGivenIn`. -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  match subtractSwapFeeAmount s.amount p.fee with
  | none => none
  | some net =>
    downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale net (p.rate s.tokenIn))) (p.rate s.tokenOut)

/-- Local upscale rounded up (equals `scaleUp`). -/
def upscaleUp (amount scalingFactor : Nat) : Nat := mulUp amount scalingFactor

/-- `_swapGivenOut` (fixed: upscales the amount out rounded UP and requires it
strictly below the scaled balance). -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut then
    match downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none => none
    | some amountIn => addSwapFeeAmount amountIn p.fee
  else none

/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

/-! ## Helpers -/

theorem one_pos : 0 < ONE := by decide

theorem mulUp_eq_ceil (a b : Nat) : mulUp a b = ProofForgeFin.ceilDiv (a * b) ONE := by
  unfold mulUp
  rw [ProofForgeFin.ceilDiv_eq_ite _ _ one_pos]

theorem upscaleUp_eq_scaleUp (a r : Nat) : upscaleUp a r = scaleUp a r := by
  unfold upscaleUp scaleUp
  rw [mulUp_eq_ceil]
  rw [ProofForgeFin.ceilDiv_eq_add_pred _ _ one_pos]

theorem divUp_eq_ceil (a b : Nat) :
    divUp a b = if b = 0 then none else some (ProofForgeFin.ceilDiv (a * ONE) b) := by
  unfold divUp
  by_cases hb : b = 0 <;> simp [hb]
  by_cases ha : a = 0
  · simp [ha, ProofForgeFin.ceilDiv_zero_left]
  · have h2 : a * ONE ≠ 0 := Nat.mul_ne_zero ha (Nat.ne_of_gt one_pos)
    simp [ha, h2, ProofForgeFin.ceilDiv_eq_ite _ _ (by omega : 0 < b)]

theorem complement_eq (fee : Nat) (hf : fee < ONE) : complement fee = ONE - fee := by
  unfold complement; simp [hf]

theorem complement_pos (fee : Nat) (hf : fee < ONE) : 0 < complement fee := by
  rw [complement_eq fee hf]; omega

theorem mulUp_le_of_fee_lt (amount fee : Nat) (hf : fee < ONE) :
    mulUp amount fee ≤ amount := by
  rw [mulUp_eq_ceil]
  apply (ProofForgeFin.ceilDiv_le_iff one_pos).2
  exact Nat.mul_le_mul_left amount (Nat.le_of_lt hf)

theorem sub_fee_some (amount fee : Nat) (hf : fee < ONE) :
    subtractSwapFeeAmount amount fee = some (amount - mulUp amount fee) := by
  unfold subtractSwapFeeAmount
  simp [mulUp_le_of_fee_lt amount fee hf]

theorem upscale_eq (a r : Nat) : upscale a r = a * r / ONE := rfl

theorem upscaleArray_eq (p : Pool) (k : Nat) :
    upscaleArray p k = scaleDown (p.balance k) (p.rate k) := rfl

theorem downscaleDown_eq (a r : Nat) :
    downscaleDown a r = if r = 0 then none else some (if a = 0 then 0 else a * ONE / r) := by
  unfold downscaleDown divDown
  by_cases hr : r = 0 <;> simp [hr]
  by_cases ha : a = 0 <;> simp [ha]

theorem downscaleUp_eq (a r : Nat) :
    downscaleUp a r = if r = 0 then none else some (ProofForgeFin.ceilDiv (a * ONE) r) := by
  unfold downscaleUp
  exact divUp_eq_ceil a r

theorem addFee_eq (a fee : Nat) :
    addSwapFeeAmount a fee = divUp a (complement fee) := rfl

theorem divDown_some_of_pos (a r : Nat) (hr : 0 < r) :
    ∃ y, divDown a r = some y := by
  unfold divDown
  simp [Nat.ne_of_gt hr]
  by_cases ha : a = 0 <;> simp [ha]

theorem divUp_some_of_pos (a r : Nat) (hr : 0 < r) :
    ∃ y, divUp a r = some y := by
  rw [divUp_eq_ceil]
  simp [Nat.ne_of_gt hr]

theorem downscaleDown_some_of_pos (a r : Nat) (hr : 0 < r) :
    ∃ y, downscaleDown a r = some y := by
  unfold downscaleDown
  exact divDown_some_of_pos a r hr

theorem downscaleUp_some_of_pos (a r : Nat) (hr : 0 < r) :
    ∃ y, downscaleUp a r = some y := by
  unfold downscaleUp
  exact divUp_some_of_pos a r hr

theorem addFee_some_of_lt (a fee : Nat) (hf : fee < ONE) :
    ∃ y, addSwapFeeAmount a fee = some y := by
  unfold addSwapFeeAmount
  exact divUp_some_of_pos a (complement fee) (complement_pos fee hf)

/-- The scaled quote of a given-in swap is below the raw balance. -/
theorem downscale_le_balance (y_math rateOut bal : Nat)
    (hle : y_math * ONE ≤ bal * rateOut) :
    (if y_math = 0 then 0 else y_math * ONE / rateOut) ≤ bal := by
  by_cases hy : y_math = 0
  · simp [hy]
  · simp [hy]
    rcases Nat.eq_zero_or_pos rateOut with hr | hr
    · subst hr
      simpa using (Nat.zero_le bal)
    · have hle' : y_math * ONE ≤ rateOut * bal := by
        rw [Nat.mul_comm bal rateOut] at hle; exact hle
      exact Nat.div_le_of_le_mul hle'

theorem downscaleDown_le_of_some (ymath rate bal y : Nat)
    (hy : downscaleDown ymath rate = some y)
    (hle : ymath * ONE ≤ bal * rate) : y ≤ bal := by
  unfold downscaleDown divDown at hy
  by_cases hr : rate = 0
  · simp [hr] at hy
  · simp [hr] at hy
    by_cases ha : ymath = 0
    · simp [ha] at hy
      rw [← hy]
      exact Nat.zero_le _
    · simp [ha] at hy
      rw [← hy]
      have hle2 := downscale_le_balance ymath rate bal hle
      simp [ha] at hle2
      exact hle2

theorem downscaleDown_mul_le_of_some (ymath rate y : Nat)
    (hy : downscaleDown ymath rate = some y) : y * rate ≤ ymath * ONE := by
  unfold downscaleDown divDown at hy
  by_cases hr : rate = 0
  · simp [hr] at hy
  · simp [hr] at hy
    by_cases ha : ymath = 0
    · simp [ha] at hy
      rw [← hy]
      simp [ha]
    · simp [ha] at hy
      rw [← hy]
      exact Nat.div_mul_le_self _ _

theorem net_mul_le_of_sub (amount fee : Nat) (h : mulUp amount fee ≤ amount) :
    (amount - mulUp amount fee) * ONE ≤ amount * (ONE - fee) := by
  have h1 : amount * fee ≤ ProofForgeFin.ceilDiv (amount * fee) ONE * ONE :=
    ProofForgeFin.le_ceilDiv_mul _ _ one_pos
  have h2 : ProofForgeFin.ceilDiv (amount * fee) ONE * ONE ≤ mulUp amount fee * ONE := by
    rw [← mulUp_eq_ceil]
    exact Nat.le_refl _
  have hceil : amount * fee ≤ mulUp amount fee * ONE := Nat.le_trans h1 h2
  rcases Nat.eq_zero_or_pos amount with ha | ha
  · subst ha
    simp [mulUp]
  · have hpos : 0 < amount := ha
    have hfee_mul : amount * fee ≤ amount * ONE :=
      Nat.le_trans hceil (Nat.mul_le_mul_right ONE h)
    have hfee_le : fee ≤ ONE := Nat.le_of_mul_le_mul_left hfee_mul hpos
    have e1 : (amount - mulUp amount fee) * ONE =
        amount * ONE - mulUp amount fee * ONE := Nat.sub_mul _ _ _
    have e2 : amount * (ONE - fee) = amount * ONE - amount * fee := Nat.mul_sub _ _ _
    rw [e1, e2]
    exact Nat.sub_le_sub_left hceil _

theorem upscale_net_le_netInDown (amount fee rateIn : Nat)
    (h : mulUp amount fee ≤ amount) :
    upscale (amount - mulUp amount fee) rateIn ≤
      amount * (ONE - fee) * rateIn / (ONE * ONE) := by
  have hnet := net_mul_le_of_sub amount fee h
  have hpos1 : 0 < ONE := one_pos
  have hpos2 : 0 < ONE * ONE := Nat.mul_pos one_pos one_pos
  apply ProofForgeFin.div_le_div_of_mul_le hpos1 hpos2
  -- goal: (amount - mulUp ..) * rateIn * (ONE * ONE) ≤ amount*(ONE-fee)*rateIn * ONE
  have h1 : (amount - mulUp amount fee) * ONE * rateIn ≤
      amount * (ONE - fee) * rateIn :=
    Nat.mul_le_mul_right rateIn hnet
  have e : (amount - mulUp amount fee) * rateIn * (ONE * ONE) =
      ((amount - mulUp amount fee) * ONE * rateIn) * ONE := by
    ac_rfl
  have e2 : amount * (ONE - fee) * rateIn * ONE =
      (amount * (ONE - fee) * rateIn) * ONE := by
    ac_rfl
  rw [e, e2]
  exact Nat.mul_le_mul_right ONE h1

theorem downscaleDown_lt_of_some (ymath rate y : Nat)
    (hy : downscaleDown ymath rate = some y) : ymath * ONE < (y + 1) * rate := by
  unfold downscaleDown divDown at hy
  by_cases hr : rate = 0
  · simp [hr] at hy
  · simp [hr] at hy
    have hpos : 0 < rate := Nat.pos_of_ne_zero hr
    by_cases ha : ymath = 0
    · simp [ha] at hy
      rw [← hy]
      simp [ha]
      exact hpos
    · simp [ha] at hy
      -- y = floor, so ymath*ONE < (y+1)*rate
      have hlt : ymath * ONE < (ymath * ONE / rate + 1) * rate :=
        ProofForgeFin.lt_div_add_one_mul _ _ hpos
      rw [hy] at hlt
      exact hlt

theorem mulUp_mul_lt_of_pos (amount fee : Nat) (hpos : 0 < amount) :
    mulUp amount fee * ONE < amount * fee + ONE := by
  have h1 : ProofForgeFin.ceilDiv (amount * fee) ONE * ONE < amount * fee + ONE :=
    ProofForgeFin.ceilDiv_mul_lt _ _ one_pos
  rw [← mulUp_eq_ceil] at h1
  exact h1

theorem netLessOne_core_le (amount fee : Nat) (h : mulUp amount fee ≤ amount) :
    amount * (ONE - fee) - ONE ≤ (amount - mulUp amount fee) * ONE := by
  rcases Nat.eq_zero_or_pos amount with ha | ha
  · subst ha
    simp [mulUp]
  · have hpos : 0 < amount := ha
    have h1 : amount * fee ≤ ProofForgeFin.ceilDiv (amount * fee) ONE * ONE :=
      ProofForgeFin.le_ceilDiv_mul _ _ one_pos
    have h2 : ProofForgeFin.ceilDiv (amount * fee) ONE * ONE ≤ mulUp amount fee * ONE := by
      rw [← mulUp_eq_ceil]
      exact Nat.le_refl _
    have hceil_le : amount * fee ≤ mulUp amount fee * ONE := Nat.le_trans h1 h2
    have hfee_mul : amount * fee ≤ amount * ONE :=
      Nat.le_trans hceil_le (Nat.mul_le_mul_right ONE h)
    have hfee_le : fee ≤ ONE := Nat.le_of_mul_le_mul_left hfee_mul hpos
    have hlt : mulUp amount fee * ONE < amount * fee + ONE :=
      mulUp_mul_lt_of_pos amount fee hpos
    have e1 : amount * (ONE - fee) = amount * ONE - amount * fee := Nat.mul_sub _ _ _
    have e2 : (amount - mulUp amount fee) * ONE =
        amount * ONE - mulUp amount fee * ONE := Nat.sub_mul _ _ _
    rw [e1, e2]
    -- goal: (amount*ONE - amount*fee) - ONE ≤ amount*ONE - mulUp*ONE
    -- from hlt: mulUp*ONE < amount*fee + ONE, and mulUp*ONE ≤ amount*ONE, amount*fee ≤ amount*ONE
    omega

theorem netLessOne_le_upscale_net (amount fee rateIn : Nat)
    (h : mulUp amount fee ≤ amount) :
    (amount * (ONE - fee) - ONE) * rateIn / (ONE * ONE) ≤
      upscale (amount - mulUp amount fee) rateIn := by
  have hcore := netLessOne_core_le amount fee h
  have hpos1 : 0 < ONE * ONE := Nat.mul_pos one_pos one_pos
  have hpos2 : 0 < ONE := one_pos
  apply ProofForgeFin.div_le_div_of_mul_le hpos1 hpos2
  -- goal: ((amount*(ONE-fee)-ONE)*rateIn)*ONE ≤ (amount-mulUp)*rateIn*(ONE*ONE)
  have h1 : ((amount * (ONE - fee) - ONE)) * (rateIn * ONE) ≤
      ((amount - mulUp amount fee) * ONE) * (rateIn * ONE) :=
    Nat.mul_le_mul_right _ hcore
  have e : (amount * (ONE - fee) - ONE) * rateIn * ONE =
      ((amount * (ONE - fee) - ONE)) * (rateIn * ONE) := by
    simp only [Nat.mul_assoc]
  have e2 : (amount - mulUp amount fee) * rateIn * (ONE * ONE) =
      ((amount - mulUp amount fee) * ONE) * (rateIn * ONE) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  -- rearrange h1 to match goal via AC
  have h2 : (amount * (ONE - fee) - ONE) * rateIn * ONE ≤
      (amount - mulUp amount fee) * rateIn * (ONE * ONE) := by
    rw [e, e2]
    exact h1
  exact h2

theorem downscaleUp_ge_of_some (inMath rate raw : Nat)
    (hy : downscaleUp inMath rate = some raw) : inMath * ONE ≤ raw * rate := by
  have heq := downscaleUp_eq inMath rate
  rw [heq] at hy
  by_cases hr : rate = 0
  · simp [hr] at hy
  · simp [hr] at hy
    have hle := ProofForgeFin.le_ceilDiv_mul (inMath * ONE) rate
      (Nat.pos_of_ne_zero hr)
    rw [hy] at hle
    exact hle

theorem addFee_ge_of_some (raw fee c : Nat)
    (hy : addSwapFeeAmount raw fee = some c) : raw * ONE ≤ c * complement fee := by
  unfold addSwapFeeAmount at hy
  have heq := divUp_eq_ceil raw (complement fee)
  rw [heq] at hy
  by_cases hr : complement fee = 0
  · simp [hr] at hy
  · simp [hr] at hy
    have hle := ProofForgeFin.le_ceilDiv_mul (raw * ONE) (complement fee)
      (Nat.pos_of_ne_zero hr)
    rw [hy] at hle
    exact hle

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hw hk hv hrate hfee
  show (step onSwap m p s).isSome
  unfold step
  rw [if_pos hv]
  have hk2 : (onSwap m p s) = swapGivenIn m p s := by
    unfold onSwap; rw [hk]
  rw [hk2]
  unfold swapGivenIn
  have hsub : subtractSwapFeeAmount s.amount p.fee = some (s.amount - mulUp s.amount p.fee) :=
    sub_fee_some s.amount p.fee hfee
  rw [hsub]
  simp only
  obtain ⟨y, hy⟩ := downscaleDown_some_of_pos
    (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)))
    (p.rate s.tokenOut) hrate
  rw [hy]
  simp only
  have hsound := hw.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
    (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))
  have hpair := hsound hv.1 hv.2.1 hv.2.2
  obtain ⟨hle_bal, _⟩ := hpair
  have hle2 : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) * ONE ≤
      p.balance s.tokenOut * p.rate s.tokenOut := by
    have h2 : upscaleArray p s.tokenOut * ONE ≤
        p.balance s.tokenOut * p.rate s.tokenOut := Nat.div_mul_le_self _ _
    have h3 := Nat.mul_le_mul_right ONE hle_bal
    exact Nat.le_trans h3 h2
  have hle_settle : y ≤ p.balance s.tokenOut :=
    downscaleDown_le_of_some _ _ _ _ hy hle2
  unfold settle amountOut
  rw [hk]
  simp [hle_settle]

theorem le_of_scaleUp_lt_scaleDown (a b r : Nat)
    (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  apply Nat.le_of_not_gt
  intro hc
  have h1 : b * r ≤ a * r := Nat.mul_le_mul_right r (Nat.le_of_lt hc)
  have h2 : b * r / ONE * ONE ≤ b * r := Nat.div_mul_le_self _ _
  have h3 : a * r ≤ ProofForgeFin.ceilDiv (a * r) ONE * ONE :=
    ProofForgeFin.le_ceilDiv_mul _ _ one_pos
  have h4 : scaleDown b r ≤ ProofForgeFin.ceilDiv (a * r) ONE := by
    apply Nat.le_of_mul_le_mul_right _ one_pos
    calc b * r / ONE * ONE ≤ b * r := Nat.div_mul_le_self _ _
      _ ≤ a * r := h1
      _ ≤ ProofForgeFin.ceilDiv (a * r) ONE * ONE :=
        ProofForgeFin.le_ceilDiv_mul _ _ one_pos
  have h5 : ProofForgeFin.ceilDiv (a * r) ONE = scaleUp a r := by
    unfold scaleUp
    rw [ProofForgeFin.ceilDiv_eq_add_pred _ _ one_pos]
  exact absurd (h5 ▸ h4) (Nat.not_le_of_gt h)

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hw hk hv hrate hfee hlt
  show (step onSwap m p s).isSome
  unfold step
  rw [if_pos hv]
  have hk2 : onSwap m p s = swapGivenOut m p s := by
    unfold onSwap; rw [hk]
  rw [hk2]
  unfold swapGivenOut
  have hbal : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut := by
    rw [upscaleUp_eq_scaleUp]
    exact hlt
  rw [if_pos hbal]
  obtain ⟨y, hy⟩ := downscaleUp_some_of_pos
    (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut)))
    (p.rate s.tokenIn) hrate
  rw [hy]
  simp only
  obtain ⟨c, hc⟩ := addFee_some_of_lt y p.fee hfee
  simp only [hc]
  unfold settle amountOut
  rw [hk]
  simp only
  have hle : s.amount ≤ p.balance s.tokenOut :=
    le_of_scaleUp_lt_scaleDown s.amount (p.balance s.tokenOut) (p.rate s.tokenOut) hlt
  simp [hle]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hk hv hq
  have hk2 : onSwap m p s = swapGivenIn m p s := by
    unfold onSwap; rw [hk]
  rw [hk2] at hq
  unfold swapGivenIn at hq
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    rw [hsub] at hq
    simp at hq
  | some net =>
    rw [hsub] at hq
    simp only at hq
    have hmul_le : mulUp s.amount p.fee ≤ s.amount := by
      by_cases hle : mulUp s.amount p.fee ≤ s.amount
      · exact hle
      · unfold subtractSwapFeeAmount at hsub
        simp [hle] at hsub
    have hnet_eq : net = s.amount - mulUp s.amount p.fee := by
      unfold subtractSwapFeeAmount at hsub
      simp [hmul_le] at hsub
      exact hsub.symm
    rw [hnet_eq] at hq
    have hmul_bound := downscaleDown_mul_le_of_some _ _ _ hq
    have hxin_le := upscale_net_le_netInDown s.amount p.fee (p.rate s.tokenIn) hmul_le
    have hmono_le := hmono.1 (scaledBalances p) s.tokenIn s.tokenOut _ _
      (by simpa using hxin_le)
    have hle2 := Nat.mul_le_mul_right ONE hmono_le
    have htrans := Nat.le_trans hmul_bound hle2
    have heq : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) =
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
      ac_rfl
    rw [heq]
    exact htrans

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hk hv hq
  have hk2 : onSwap m p s = swapGivenIn m p s := by
    unfold onSwap; rw [hk]
  rw [hk2] at hq
  unfold swapGivenIn at hq
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    rw [hsub] at hq
    simp at hq
  | some net =>
    rw [hsub] at hq
    simp only at hq
    have hmul_le : mulUp s.amount p.fee ≤ s.amount := by
      by_cases hle : mulUp s.amount p.fee ≤ s.amount
      · exact hle
      · unfold subtractSwapFeeAmount at hsub
        simp [hle] at hsub
    have hnet_eq : net = s.amount - mulUp s.amount p.fee := by
      unfold subtractSwapFeeAmount at hsub
      simp [hmul_le] at hsub
      exact hsub.symm
    rw [hnet_eq] at hq
    have hlt := downscaleDown_lt_of_some _ _ _ hq
    have hle_net : netInLessOneDown p s ≤
        upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn) :=
      netLessOne_le_upscale_net s.amount p.fee (p.rate s.tokenIn) hmul_le
    have hmono_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s) ≤
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
          (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) :=
      hmono.1 (scaledBalances p) s.tokenIn s.tokenOut _ _ hle_net
    have hle2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s) * ONE ≤
        m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
          (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) * ONE :=
      Nat.mul_le_mul_right ONE hmono_le
    have htrans : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s) * ONE < (y + 1) * p.rate s.tokenOut :=
      Nat.lt_of_le_of_lt hle2 hlt
    have heq : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s) =
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s) * ONE := Nat.mul_comm _ _
    rw [heq]
    exact htrans

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hk hv hq
  have hk2 : onSwap m p s = swapGivenOut m p s := by
    unfold onSwap; rw [hk]
  rw [hk2] at hq
  unfold swapGivenOut at hq
  by_cases hbal : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · simp [hbal] at hq
    cases hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      rw [hdown] at hq
      simp at hq
    | some y =>
      rw [hdown] at hq
      simp only at hq
      have h_in_le := downscaleUp_ge_of_some _ _ _ hdown
      have hfee_lt : p.fee < ONE := by
        by_cases hle : p.fee < ONE
        · exact hle
        · have hne : complement p.fee ≠ 0 := by
            intro hcon
            unfold addSwapFeeAmount at hq
            rw [divUp_eq_ceil] at hq
            simp [hcon] at hq
          unfold complement at hne
          simp [hle] at hne
      have hcomp : complement p.fee = ONE - p.fee := complement_eq _ hfee_lt
      have h_fee_ge := addFee_ge_of_some _ _ _ hq
      rw [hcomp] at h_fee_ge
      have harr : upscaleArray p = scaledBalances p := rfl
      have hin_eq : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (upscaleUp s.amount (p.rate s.tokenOut)) = outPrice m p s := by
        unfold outPrice
        rw [← upscaleUp_eq_scaleUp, harr]
      have h1 : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (upscaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE ≤
          y * p.rate s.tokenIn * ONE :=
        Nat.mul_le_mul_right ONE h_in_le
      have heq_mid : y * p.rate s.tokenIn * ONE = y * ONE * p.rate s.tokenIn := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [heq_mid] at h1
      have h2 : y * ONE * p.rate s.tokenIn ≤
          c * (ONE - p.fee) * p.rate s.tokenIn := by
        have h2a : y * ONE ≤ c * (ONE - p.fee) := h_fee_ge
        exact Nat.mul_le_mul_right _ h2a
      have htrans : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (upscaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE ≤
          c * (ONE - p.fee) * p.rate s.tokenIn :=
        Nat.le_trans h1 h2
      have heq1 : ONE * ONE * outPrice m p s =
          m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE := by
        rw [hin_eq]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [heq1]
      exact htrans
  · simp [hbal] at hq

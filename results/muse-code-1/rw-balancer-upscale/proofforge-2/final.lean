import BalancerSwap.Spec
import ProofForgeFin.Rounding
/-!
Fixed swap wrapper: the given-out path now rounds the amount out *up* to whole
18-decimal units before pricing (Balancer's `_upscale` rounded it down, which let
the 17-wei exploit take 17 units of value for the price of 17 wei instead of 18).
-/
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

/-- Up-scaling rounded up (the fix): least whole 18-decimal unit at or above the exact value. -/
def upscaleUp (amount scalingFactor : Nat) : Nat := (amount * scalingFactor + (ONE - 1)) / ONE

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
  | some amount =>
    let balances := upscaleArray p
    let amount := upscale amount (p.rate s.tokenIn)
    let amountOut := m.outGivenIn balances s.tokenIn s.tokenOut amount
    downscaleDown amountOut (p.rate s.tokenOut)

/-- `_swapGivenOut` (fixed: amount up-scaled with rounding up, and strict `<` check so the
math's `x < balance` hypothesis holds whenever we proceed). -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  let balances := upscaleArray p
  let amount := upscaleUp s.amount (p.rate s.tokenOut)
  if balances s.tokenOut ≤ amount then none
  else
    match downscaleUp (m.inGivenOut balances s.tokenIn s.tokenOut amount) (p.rate s.tokenIn) with
    | none => none
    | some amountIn => addSwapFeeAmount amountIn p.fee

/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

/-! ## Basic facts about ONE and rounding -/

theorem one_pos : 0 < ONE := by unfold ONE; omega

theorem one_ne_zero : ONE ≠ 0 := by unfold ONE; omega

theorem upscale_eq_scaleDown (a r : Nat) : upscale a r = scaleDown a r := rfl

theorem upscaleUp_eq_scaleUp (a r : Nat) : upscaleUp a r = scaleUp a r := by
  unfold upscaleUp scaleUp; rfl

theorem upscaleArray_eq (p : Pool) : upscaleArray p = scaledBalances p := by
  unfold upscaleArray scaledBalances scaleDown mulDown; rfl

theorem upscaleUp_eq_ceilDiv (a r : Nat) : upscaleUp a r = ProofForgeFin.ceilDiv (a * r) ONE := by
  unfold upscaleUp
  rw [ProofForgeFin.ceilDiv_eq_add_pred _ _ one_pos]

theorem mulUp_eq_ceilDiv (a b : Nat) : mulUp a b = ProofForgeFin.ceilDiv (a * b) ONE := by
  unfold mulUp
  by_cases h : a * b = 0
  · simp [h]
  · have h2 : a * b ≠ 0 := h
    have := ProofForgeFin.ceilDiv_eq_ite (a * b) ONE one_pos
    rw [if_neg h2] at this
    rw [if_neg h]
    exact this.symm

theorem divDown_some_eq (a b y : Nat) (h : divDown a b = some y) : b ≠ 0 ∧ y = a * ONE / b := by
  unfold divDown at h
  by_cases hb0 : b = 0
  · subst hb0; simp only [if_true] at h; cases h
  · rw [if_neg hb0] at h
    refine ⟨hb0, ?_⟩
    by_cases ha0 : a = 0
    · rw [if_pos ha0] at h
      cases h; subst ha0
      simp [Nat.zero_mul]
    · rw [if_neg ha0] at h
      cases h; rfl

theorem divUp_some_eq (a b y : Nat) (h : divUp a b = some y) :
    b ≠ 0 ∧ y = ProofForgeFin.ceilDiv (a * ONE) b := by
  unfold divUp at h
  by_cases hb0 : b = 0
  · subst hb0; simp only [if_true] at h; cases h
  · rw [if_neg hb0] at h
    refine ⟨hb0, ?_⟩
    by_cases ha0 : a = 0
    · rw [if_pos ha0] at h
      cases h; subst ha0
      simp only [Nat.zero_mul, ProofForgeFin.ceilDiv_zero_left]
    · rw [if_neg ha0] at h
      cases h
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hne : a * ONE ≠ 0 := Nat.mul_ne_zero ha0 one_ne_zero
      have heq := ProofForgeFin.ceilDiv_eq_ite (a * ONE) b hbpos
      rw [if_neg hne] at heq
      exact heq.symm

theorem divDown_none_iff (a b : Nat) : divDown a b = none ↔ b = 0 := by
  unfold divDown
  by_cases hb0 : b = 0
  · simp only [hb0, if_true, iff_true]
  · rw [if_neg hb0]
    constructor
    · intro h
      by_cases ha0 : a = 0
      · rw [if_pos ha0] at h; cases h
      · rw [if_neg ha0] at h; cases h
    · intro h; cases hb0 h

theorem divUp_none_iff (a b : Nat) : divUp a b = none ↔ b = 0 := by
  unfold divUp
  by_cases hb0 : b = 0
  · simp only [hb0, if_true, iff_true]
  · rw [if_neg hb0]
    constructor
    · intro h
      by_cases ha0 : a = 0
      · rw [if_pos ha0] at h; cases h
      · rw [if_neg ha0] at h; cases h
    · intro h; cases hb0 h

theorem complement_eq (x : Nat) : complement x = if x < ONE then ONE - x else 0 := rfl

theorem complement_pos_of_lt (x : Nat) (h : x < ONE) : complement x = ONE - x := by
  simp [complement, h]

theorem complement_pos_ne_zero_of_lt (x : Nat) (h : x < ONE) : complement x ≠ 0 := by
  rw [complement_pos_of_lt _ h]; omega

theorem floor_spec' (a b : Nat) (hb : 0 < b) : a / b * b ≤ a ∧ a < (a / b + 1) * b :=
  ProofForgeFin.floor_spec a b hb

theorem ceil_spec' (a b : Nat) (hb : 0 < b) :
    a ≤ ProofForgeFin.ceilDiv a b * b ∧ ProofForgeFin.ceilDiv a b * b < a + b :=
  ProofForgeFin.ceilDiv_spec a b hb

theorem mulUp_le_of_fee_le (a fee : Nat) (h : fee ≤ ONE) : mulUp a fee ≤ a := by
  rw [mulUp_eq_ceilDiv]
  have h1 : ProofForgeFin.ceilDiv (a * fee) ONE ≤ a := by
    apply (ProofForgeFin.ceilDiv_le_iff one_pos).2
    calc a * fee ≤ a * ONE := Nat.mul_le_mul_left a h
      _ = a * ONE := rfl
  exact h1

theorem mulUp_le_of_fee_lt (a fee : Nat) (h : fee < ONE) : mulUp a fee ≤ a :=
  mulUp_le_of_fee_le a fee (Nat.le_of_lt h)

theorem sub_fee_some_of_lt (a fee : Nat) (h : fee < ONE) :
    ∃ n, subtractSwapFeeAmount a fee = some n ∧ n = a - mulUp a fee := by
  have hle : mulUp a fee ≤ a := mulUp_le_of_fee_lt a fee h
  exact ⟨a - mulUp a fee, by unfold subtractSwapFeeAmount; simp only [hle, if_true], rfl⟩

theorem add_fee_some_of_lt (amt fee : Nat) (h : fee < ONE) :
    ∃ c, addSwapFeeAmount amt fee = some c ∧
      c = ProofForgeFin.ceilDiv (amt * ONE) (ONE - fee) := by
  have hcomp : complement fee = ONE - fee := by unfold complement; simp [h]
  have hpos : 0 < ONE - fee := by omega
  have hne : (ONE - fee) ≠ 0 := by omega
  by_cases hamt : amt = 0
  · subst hamt
    refine ⟨0, ?_, by simp [Nat.zero_mul, ProofForgeFin.ceilDiv_zero_left]⟩
    unfold addSwapFeeAmount
    rw [hcomp]
    unfold divUp
    rw [if_neg hne, if_pos rfl]
  · have hne2 : amt * ONE ≠ 0 := Nat.mul_ne_zero hamt one_ne_zero
    have heq := ProofForgeFin.ceilDiv_eq_ite (amt * ONE) (ONE - fee) hpos
    rw [if_neg hne2] at heq
    refine ⟨ProofForgeFin.ceilDiv (amt * ONE) (ONE - fee), ?_, rfl⟩
    unfold addSwapFeeAmount
    rw [hcomp]
    unfold divUp
    rw [if_neg hne, if_neg hamt]
    exact congrArg some heq.symm

/-- From `scaleUp a < scaleDown b` conclude `a ≤ b` (contrapositive of monotonicity). -/
theorem le_of_scaleUp_lt_scaleDown (a b r : Nat) (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  unfold scaleUp scaleDown at h
  by_cases hle : a ≤ b
  · exact hle
  · have hlt : b < a := Nat.lt_of_not_le hle
    have hr : 0 < r := by
      by_cases hr0 : r = 0
      · subst hr0
        simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_div] at h
        have hzero : (ONE - 1) / ONE = 0 := Nat.div_eq_of_lt (by unfold ONE; omega)
        rw [hzero] at h
        exact h
      · exact Nat.pos_of_ne_zero hr0
    have hmul : b * r < a * r := Nat.mul_lt_mul_of_pos_right hlt hr
    have h1 : (b * r) / ONE * ONE ≤ b * r := Nat.div_mul_le_self _ _
    have hceil := ProofForgeFin.le_ceilDiv_mul (a * r) ONE one_pos
    have heq : ProofForgeFin.ceilDiv (a * r) ONE = ((a * r + (ONE - 1)) / ONE) := by
      rw [ProofForgeFin.ceilDiv_eq_add_pred _ _ one_pos]
    have h2 : a * r ≤ ((a * r + (ONE - 1)) / ONE) * ONE := heq ▸ hceil
    have hXY : ((a * r + (ONE - 1)) / ONE) * ONE < ((b * r) / ONE) * ONE :=
      Nat.mul_lt_mul_of_pos_right h one_pos
    omega

theorem mulUp_lower (a fee : Nat) : a * fee ≤ mulUp a fee * ONE := by
  rw [mulUp_eq_ceilDiv]
  exact ProofForgeFin.le_ceilDiv_mul _ _ one_pos

theorem mulUp_upper (a fee : Nat) : mulUp a fee * ONE < a * fee + ONE := by
  rw [mulUp_eq_ceilDiv]
  exact ProofForgeFin.ceilDiv_mul_lt _ _ one_pos

theorem upscaleUp_bounds (a r : Nat) :
    a * r ≤ upscaleUp a r * ONE ∧ upscaleUp a r * ONE < a * r + ONE := by
  have h := ProofForgeFin.ceilDiv_spec (a * r) ONE one_pos
  rw [← upscaleUp_eq_ceilDiv] at h
  exact h

theorem downscaleDown_bounds (P r y : Nat) (hr : 0 < r) (hy : y = P * ONE / r) :
    y * r ≤ P * ONE ∧ P * ONE < (y + 1) * r := by
  subst hy
  exact ProofForgeFin.floor_spec _ _ hr

theorem unscaleUp_bounds (P r y : Nat) (hr : 0 < r)
    (hy : y = ProofForgeFin.ceilDiv (P * ONE) r) :
    P * ONE ≤ y * r ∧ y * r < P * ONE + r := by
  subst hy
  exact ProofForgeFin.ceilDiv_spec _ _ hr

theorem addFee_bounds (amt fee c : Nat) (hpos : 0 < ONE - fee)
    (hc : c = ProofForgeFin.ceilDiv (amt * ONE) (ONE - fee)) :
    amt * ONE ≤ c * (ONE - fee) ∧ c * (ONE - fee) < amt * ONE + (ONE - fee) := by
  subst hc
  exact ProofForgeFin.ceilDiv_spec _ _ hpos

/-- Net amount after fee, scaled down, is at most the spec's `netInDown` (when `fee ≤ ONE`). -/
theorem netScaled_le_netInDown (a fee r n : Nat) (hfee : fee ≤ ONE)
    (hn : n = a - mulUp a fee) (hle : mulUp a fee ≤ a) :
    (n * r / ONE) ≤ (a * (ONE - fee) * r / (ONE * ONE)) := by
  have hlow := mulUp_lower a fee
  have hnadd : n + mulUp a fee = a := by rw [hn]; exact Nat.sub_add_cancel hle
  have hnONE : n * ONE + mulUp a fee * ONE = a * ONE := by
    have hcon := congrArg (· * ONE) hnadd
    simp only [Nat.add_mul] at hcon
    omega
  have h1 : n * ONE ≤ a * (ONE - fee) := by
    have hfee' : a * fee + a * (ONE - fee) = a * ONE := by
      have : fee + (ONE - fee) = ONE := Nat.add_sub_of_le hfee
      calc a * fee + a * (ONE - fee) = a * (fee + (ONE - fee)) := by rw [Nat.mul_add]
        _ = a * ONE := by rw [this]
    omega
  have hOO : 0 < ONE * ONE := Nat.mul_pos one_pos one_pos
  apply ProofForgeFin.div_le_div_of_mul_le one_pos hOO
  calc (n * r) * (ONE * ONE) = (n * ONE) * (r * ONE) := by ac_rfl
    _ ≤ (a * (ONE - fee)) * (r * ONE) := Nat.mul_le_mul_right _ h1
    _ = (a * (ONE - fee) * r) * ONE := by ac_rfl

/-- The spec's `netInLessOneDown` is at most the net amount after fee, scaled down. -/
theorem netLessOne_le_netScaled (a fee r n : Nat) (hfee : fee ≤ ONE)
    (hn : n = a - mulUp a fee) (hle : mulUp a fee ≤ a) :
    ((a * (ONE - fee) - ONE) * r / (ONE * ONE)) ≤ (n * r / ONE) := by
  have hup := mulUp_upper a fee
  have hnadd2 : n + mulUp a fee = a := by rw [hn]; exact Nat.sub_add_cancel hle
  have hnONE : n * ONE + mulUp a fee * ONE = a * ONE := by
    have hcon := congrArg (· * ONE) hnadd2
    simp only [Nat.add_mul] at hcon
    omega
  have hfee' : a * fee + a * (ONE - fee) = a * ONE := by
    have : fee + (ONE - fee) = ONE := Nat.add_sub_of_le hfee
    calc a * fee + a * (ONE - fee) = a * (fee + (ONE - fee)) := by rw [Nat.mul_add]
      _ = a * ONE := by rw [this]
  have h1 : a * (ONE - fee) ≤ n * ONE + ONE := by omega
  by_cases hE : a * (ONE - fee) ≤ ONE
  · have hzero : a * (ONE - fee) - ONE = 0 := Nat.sub_eq_zero_of_le hE
    rw [hzero, Nat.zero_mul, Nat.zero_div]
    exact Nat.zero_le _
  · have hnum : (a * (ONE - fee) - ONE) * r ≤ (n * ONE) * r := by
      have hle2 : (a * (ONE - fee) - ONE) ≤ n * ONE := by omega
      exact Nat.mul_le_mul_right r hle2
    have hsame : n * r / ONE = (n * r * ONE) / (ONE * ONE) :=
      (Nat.mul_div_mul_right _ _ one_pos).symm
    rw [hsame]
    apply Nat.div_le_div_right
    calc (a * (ONE - fee) - ONE) * r ≤ (n * ONE) * r := hnum
      _ = n * r * ONE := by ac_rfl

theorem divDown_is_some (P r : Nat) (hr : r ≠ 0) :
    divDown P r = some (P * ONE / r) := by
  unfold divDown
  rw [if_neg hr]
  by_cases ha0 : P = 0
  · rw [if_pos ha0, ha0, Nat.zero_mul, Nat.zero_div]
  · rw [if_neg ha0]

theorem mulUp_le_of_sub_some (a fee n : Nat)
    (hsub : subtractSwapFeeAmount a fee = some n) : mulUp a fee ≤ a := by
  unfold subtractSwapFeeAmount at hsub
  by_cases hle : mulUp a fee ≤ a
  · exact hle
  · simp [hle] at hsub

theorem sub_n_eq (a fee n : Nat)
    (hsub : subtractSwapFeeAmount a fee = some n) : n = a - mulUp a fee := by
  unfold subtractSwapFeeAmount at hsub
  by_cases hle : mulUp a fee ≤ a
  · simp [hle] at hsub
    cases hsub
    rfl
  · simp [hle] at hsub

theorem amount_zero_of_sub_some_gt (a fee n : Nat)
    (hsub : subtractSwapFeeAmount a fee = some n) (hgt : ¬ fee ≤ ONE) : a = 0 := by
  by_cases ha0 : a = 0
  · exact ha0
  · have hfee_gt : ONE < fee := by omega
    have hlt : a * ONE < a * fee := Nat.mul_lt_mul_of_pos_left hfee_gt (Nat.pos_of_ne_zero ha0)
    have hlow := mulUp_lower a fee
    have h1 : a * ONE < mulUp a fee * ONE := Nat.lt_of_lt_of_le hlt hlow
    have h2 : a < mulUp a fee := Nat.lt_of_mul_lt_mul_right h1
    have hnone : subtractSwapFeeAmount a fee = none := by
      unfold subtractSwapFeeAmount
      simp [Nat.not_le_of_gt h2]
    rw [hnone] at hsub
    cases hsub

theorem fee_lt_of_add_some (amt fee c : Nat)
    (h : addSwapFeeAmount amt fee = some c) : fee < ONE := by
  unfold addSwapFeeAmount at h
  by_cases hlt : fee < ONE
  · exact hlt
  · have hcomp : complement fee = 0 := by unfold complement; simp [hlt]
    rw [hcomp] at h
    unfold divUp at h
    simp at h

theorem add_some_eq_ceil (amt fee c : Nat)
    (h : addSwapFeeAmount amt fee = some c) :
    c = ProofForgeFin.ceilDiv (amt * ONE) (ONE - fee) := by
  have hlt := fee_lt_of_add_some _ _ _ h
  have hcomp : complement fee = ONE - fee := by unfold complement; simp [hlt]
  unfold addSwapFeeAmount at h
  rw [hcomp] at h
  obtain ⟨hne, heq⟩ := divUp_some_eq _ _ _ h
  exact heq

theorem divUp_is_some (P r : Nat) (hr : r ≠ 0) :
    divUp P r = some (ProofForgeFin.ceilDiv (P * ONE) r) := by
  unfold divUp
  rw [if_neg hr]
  by_cases ha0 : P = 0
  · rw [if_pos ha0]
    have : P * ONE = 0 := by rw [ha0, Nat.zero_mul]
    rw [this]
    simp [ProofForgeFin.ceilDiv_zero_left]
  · rw [if_neg ha0]
    have hbpos : 0 < r := Nat.pos_of_ne_zero hr
    have hne : P * ONE ≠ 0 := Nat.mul_ne_zero ha0 one_ne_zero
    have heq := ProofForgeFin.ceilDiv_eq_ite (P * ONE) r hbpos
    rw [if_neg hne] at heq
    rw [heq]

theorem swapGivenIn_eq (m : PoolMath) (p : Pool) (s : Swap) (n : Nat)
    (hsub : subtractSwapFeeAmount s.amount p.fee = some n) :
    swapGivenIn m p s =
      downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale n (p.rate s.tokenIn)))
        (p.rate s.tokenOut) := by
  unfold swapGivenIn
  rw [hsub]

theorem swapGivenOut_eq (m : PoolMath) (p : Pool) (s : Swap)
    (hlt : ¬ (upscaleArray p s.tokenOut ≤ upscaleUp s.amount (p.rate s.tokenOut)))
    (amt : Nat) (hup : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some amt) :
    swapGivenOut m p s = addSwapFeeAmount amt p.fee := by
  unfold swapGivenOut
  rw [if_neg hlt, hup]

theorem downscaleDown_le_balance (P bal r : Nat) (hr : 0 < r)
    (hle : P ≤ bal * r / ONE) : P * ONE / r ≤ bal := by
  have h1 : P * ONE / r * r ≤ P * ONE := Nat.div_mul_le_self _ _
  have h2 : P * ONE ≤ bal * r := by
    have h3 : P ≤ bal * r / ONE := hle
    have h4 : P * ONE ≤ (bal * r / ONE) * ONE := Nat.mul_le_mul_right ONE h3
    have h5 : (bal * r / ONE) * ONE ≤ bal * r := Nat.div_mul_le_self _ _
    omega
  have h3 : P * ONE / r * r ≤ bal * r := Nat.le_trans h1 h2
  have := Nat.le_of_mul_le_mul_right h3 hr
  exact this

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hwb hkind hvalid hrate hfee
  have hne : s.tokenIn ≠ s.tokenOut := hvalid.1
  have htin : s.tokenIn < p.n := hvalid.2.1
  have htout : s.tokenOut < p.n := hvalid.2.2
  have hratePos : 0 < p.rate s.tokenOut := hrate
  have hratene : p.rate s.tokenOut ≠ 0 := Nat.pos_iff_ne_zero.mp hratePos
  have hon : onSwap m p s = swapGivenIn m p s := by unfold onSwap; simp [hkind]
  obtain ⟨n, hsub, hn⟩ := sub_fee_some_of_lt s.amount p.fee hfee
  have hPle : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale n (p.rate s.tokenIn)) ≤ (upscaleArray p) s.tokenOut := by
    have h := hwb.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale n (p.rate s.tokenIn)) hne htin htout
    exact h.1
  have harr : (upscaleArray p) s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
  have hle : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale n (p.rate s.tokenIn)) ≤ p.balance s.tokenOut * p.rate s.tokenOut / ONE := by
    rw [← harr]; exact hPle
  have hdown : downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale n (p.rate s.tokenIn))) (p.rate s.tokenOut)
      = some (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut) :=
    divDown_is_some _ _ hratene
  have hswap : onSwap m p s = some (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale n (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut) := by
    rw [hon, swapGivenIn_eq m p s n hsub, hdown]
  have hy_le : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut
        ≤ p.balance s.tokenOut :=
    downscaleDown_le_balance _ _ _ hratePos hle
  have ham : amountOut s (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut)
      = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut := by
    unfold amountOut; simp [hkind]
  unfold step
  rw [if_pos hvalid, hswap]
  have hset : (settle p s (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale n (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut)).isSome := by
    unfold settle
    rw [ham, if_pos hy_le]
    simp
  exact hset

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hwb hkind hvalid hrate hfee hlt
  have hratePos : 0 < p.rate s.tokenIn := hrate
  have hratene : p.rate s.tokenIn ≠ 0 := Nat.pos_iff_ne_zero.mp hratePos
  have hfeeLt : p.fee < ONE := hfee
  have hon : onSwap m p s = swapGivenOut m p s := by unfold onSwap; simp [hkind]
  have hup_eq : upscaleUp s.amount (p.rate s.tokenOut) = scaleUp s.amount (p.rate s.tokenOut) :=
    upscaleUp_eq_scaleUp _ _
  have hbal_eq : (upscaleArray p) s.tokenOut
      = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
  have hnotlt : ¬ (upscaleArray p s.tokenOut ≤ upscaleUp s.amount (p.rate s.tokenOut)) := by
    rw [hup_eq, hbal_eq]
    omega
  have hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn)
      = some (ProofForgeFin.ceilDiv (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn)) :=
    divUp_is_some _ _ hratene
  obtain ⟨c, hadd, hc_eq⟩ := add_fee_some_of_lt
    (ProofForgeFin.ceilDiv (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn)) p.fee hfeeLt
  have hswap : onSwap m p s = some c := by
    rw [hon, swapGivenOut_eq m p s hnotlt _ hdown, hadd]
  have ham_le : s.amount ≤ p.balance s.tokenOut := by
    have h2 : scaleUp s.amount (p.rate s.tokenOut)
        < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := by
      rw [← hup_eq, ← hbal_eq]; exact hlt
    exact le_of_scaleUp_lt_scaleDown _ _ _ h2
  have ham : amountOut s c = s.amount := by unfold amountOut; simp [hkind]
  unfold step
  rw [if_pos hvalid, hswap]
  have hset : (settle p s c).isSome := by
    unfold settle
    rw [ham, if_pos ham_le]
    simp
  exact hset

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hkind hvalid hswap
  have hon : onSwap m p s = swapGivenIn m p s := by unfold onSwap; simp [hkind]
  rw [hon] at hswap
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    have hnone : swapGivenIn m p s = none := by unfold swapGivenIn; simp [hsub]
    rw [hnone] at hswap; cases hswap
  | some n =>
    have hswap2 : downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn))) (p.rate s.tokenOut) = some y := by
      have heq := swapGivenIn_eq m p s n hsub
      unfold swapGivenIn at hswap
      simp [hsub] at hswap
      exact hswap
    obtain ⟨hrne, hy_eq⟩ := divDown_some_eq _ _ _ hswap2
    have hrpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrne
    have hfloor : y * p.rate s.tokenOut
        ≤ m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
          (upscale n (p.rate s.tokenIn)) * ONE := by
      have hf := (ProofForgeFin.floor_spec (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn)) * ONE) (p.rate s.tokenOut) hrpos).1
      rw [hy_eq]
      exact hf
    have hn_eq := sub_n_eq _ _ _ hsub
    have hle_mu := mulUp_le_of_sub_some _ _ _ hsub
    by_cases hfee_le : p.fee ≤ ONE
    · have hnet_le : (upscale n (p.rate s.tokenIn)) ≤ netInDown p s := by
        have h1 := netScaled_le_netInDown s.amount p.fee (p.rate s.tokenIn) n hfee_le hn_eq hle_mu
        have e1 : upscale n (p.rate s.tokenIn) = n * p.rate s.tokenIn / ONE := rfl
        have e2 : netInDown p s
            = s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE) := rfl
        rw [e1, e2]; exact h1
      have hmono_le := (hmono.1 (scaledBalances p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn)) (netInDown p s) hnet_le)
      have harr : upscaleArray p = scaledBalances p := upscaleArray_eq p
      have hP_le : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
          (upscale n (p.rate s.tokenIn))
          ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
        rw [← harr] at hmono_le ⊢
        exact hmono_le
      calc y * p.rate s.tokenOut
          ≤ m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
              (upscale n (p.rate s.tokenIn)) * ONE := hfloor
        _ ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
            have h3 : ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                (upscale n (p.rate s.tokenIn))
                ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
              Nat.mul_le_mul_left ONE hP_le
            calc m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)) * ONE
                = ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)) := Nat.mul_comm _ _
              _ ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := h3
    · have ha0 : s.amount = 0 := amount_zero_of_sub_some_gt _ _ _ hsub hfee_le
      have hn0 : n = 0 := by rw [hn_eq, ha0]; simp [mulUp]
      subst hn0
      have hup0 : upscale 0 (p.rate s.tokenIn) = 0 := by unfold upscale mulDown; simp
      have hnet0 : netInDown p s = 0 := by
        unfold netInDown; rw [ha0]; simp
      have hfloor0 : y * p.rate s.tokenOut
          ≤ m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale 0 (p.rate s.tokenIn)) * ONE :=
        hfloor
      rw [hup0] at hfloor0
      rw [hnet0]
      have harr : upscaleArray p = scaledBalances p := upscaleArray_eq p
      have hP_le : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0
          ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut 0 := by
        have hm := (hmono.1 (scaledBalances p) s.tokenIn s.tokenOut 0 0 (Nat.le_refl _))
        rw [← harr] at hm ⊢
        exact hm
      calc y * p.rate s.tokenOut ≤ m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0 * ONE := hfloor0
        _ ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut 0 := by
            have h3 : ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0
                ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut 0 :=
              Nat.mul_le_mul_left ONE hP_le
            calc m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0 * ONE
                = ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0 := Nat.mul_comm _ _
              _ ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut 0 := h3

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hkind hvalid hswap
  have hon : onSwap m p s = swapGivenIn m p s := by unfold onSwap; simp [hkind]
  rw [hon] at hswap
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    have hnone : swapGivenIn m p s = none := by unfold swapGivenIn; simp [hsub]
    rw [hnone] at hswap; cases hswap
  | some n =>
    have hswap2 : downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn))) (p.rate s.tokenOut) = some y := by
      unfold swapGivenIn at hswap
      simp [hsub] at hswap
      exact hswap
    obtain ⟨hrne, hy_eq⟩ := divDown_some_eq _ _ _ hswap2
    have hrpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrne
    have hceil_lt : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
          (upscale n (p.rate s.tokenIn)) * ONE
        < (y + 1) * p.rate s.tokenOut := by
      have hf := (ProofForgeFin.floor_spec (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale n (p.rate s.tokenIn)) * ONE) (p.rate s.tokenOut) hrpos).2
      rw [hy_eq]
      exact hf
    have hn_eq := sub_n_eq _ _ _ hsub
    have hle_mu := mulUp_le_of_sub_some _ _ _ hsub
    by_cases hfee_le : p.fee ≤ ONE
    · have hnet_ge : netInLessOneDown p s ≤ (upscale n (p.rate s.tokenIn)) := by
        have h1 := netLessOne_le_netScaled s.amount p.fee (p.rate s.tokenIn) n hfee_le hn_eq hle_mu
        have e1 : upscale n (p.rate s.tokenIn) = n * p.rate s.tokenIn / ONE := rfl
        have e2 : netInLessOneDown p s
            = (s.amount * (ONE - p.fee) - ONE) * p.rate s.tokenIn / (ONE * ONE) := rfl
        rw [e1, e2]; exact h1
      have hmono_le := (hmono.1 (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s) (upscale n (p.rate s.tokenIn)) hnet_ge)
      have harr : upscaleArray p = scaledBalances p := upscaleArray_eq p
      have hP_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
          ≤ m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
            (upscale n (p.rate s.tokenIn)) := by
        rw [← harr] at hmono_le ⊢
        exact hmono_le
      calc ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
          ≤ (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
              (upscale n (p.rate s.tokenIn))) * ONE := by
            have h3 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
                ≤ ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)) :=
              Nat.mul_le_mul_left ONE hP_le
            calc ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
                ≤ ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)) := h3
              _ = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)) * ONE := Nat.mul_comm _ _
        _ < (y + 1) * p.rate s.tokenOut := hceil_lt
    · have ha0 : s.amount = 0 := amount_zero_of_sub_some_gt _ _ _ hsub hfee_le
      have hn0 : n = 0 := by rw [hn_eq, ha0]; simp [mulUp]
      subst hn0
      have hup0 : upscale 0 (p.rate s.tokenIn) = 0 := by unfold upscale mulDown; simp
      have hnet0 : netInLessOneDown p s = 0 := by
        unfold netInLessOneDown
        rw [ha0]; simp
      have hceil0 : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
          (upscale 0 (p.rate s.tokenIn)) * ONE < (y + 1) * p.rate s.tokenOut := hceil_lt
      rw [hup0] at hceil0
      rw [hnet0]
      have harr : upscaleArray p = scaledBalances p := upscaleArray_eq p
      have hP_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut 0
          ≤ m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0 := by
        have hm := (hmono.1 (scaledBalances p) s.tokenIn s.tokenOut 0 0 (Nat.le_refl _))
        rw [← harr] at hm ⊢
        exact hm
      calc ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut 0
          ≤ m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0 * ONE := by
            calc ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut 0
                ≤ ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0 :=
                  Nat.mul_le_mul_left ONE hP_le
              _ = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut 0 * ONE := Nat.mul_comm _ _
        _ < (y + 1) * p.rate s.tokenOut := hceil0

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hkind hvalid hswap
  have hon : onSwap m p s = swapGivenOut m p s := by unfold onSwap; simp [hkind]
  rw [hon] at hswap
  unfold swapGivenOut at hswap
  by_cases hlt : (upscaleArray p) s.tokenOut ≤ upscaleUp s.amount (p.rate s.tokenOut)
  · rw [if_pos hlt] at hswap
    cases hswap
  · rw [if_neg hlt] at hswap
    cases hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      have hnone : (match (none : Option Nat) with
          | none => none | some amt => addSwapFeeAmount amt p.fee) = none := rfl
      rw [hdown] at hswap
      simp at hswap
    | some amt =>
      rw [hdown] at hswap
      simp only at hswap
      have hadd : addSwapFeeAmount amt p.fee = some c := hswap
      have hfee_lt := fee_lt_of_add_some _ _ _ hadd
      have hc_eq := add_some_eq_ceil _ _ _ hadd
      have hamt_eq : amt
          = ProofForgeFin.ceilDiv (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) := by
        have h := divUp_some_eq _ _ _ hdown
        exact h.2
      have hrate_ne : p.rate s.tokenIn ≠ 0 := by
        have h := divUp_some_eq _ _ _ hdown
        exact h.1
      have hrate_pos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrate_ne
      have hfee_pos : 0 < ONE - p.fee := by omega
      -- lower bounds
      have hup := (upscaleUp_bounds s.amount (p.rate s.tokenOut))
      have hamt_low := (ProofForgeFin.ceilDiv_spec (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) hrate_pos).1
      rw [← hamt_eq] at hamt_low
      have hc_low := (ProofForgeFin.ceilDiv_spec (amt * ONE) (ONE - p.fee) hfee_pos).1
      rw [← hc_eq] at hc_low
      -- `outPrice` equals `P` since `upscaleUp = scaleUp`
      have hP_eq : outPrice m p s
          = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) := by
        unfold outPrice
        have harr : upscaleArray p = scaledBalances p := upscaleArray_eq p
        have hup2 : upscaleUp s.amount (p.rate s.tokenOut)
            = scaleUp s.amount (p.rate s.tokenOut) := upscaleUp_eq_scaleUp _ _
        rw [harr, hup2]
      -- chain
      have hchain : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE
          ≤ c * (ONE - p.fee) * p.rate s.tokenIn := by
        calc m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
              (upscaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE
            = (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
              (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE := by ac_rfl
          _ ≤ (amt * p.rate s.tokenIn) * ONE :=
              Nat.mul_le_mul_right ONE hamt_low
          _ = (amt * ONE) * p.rate s.tokenIn := by ac_rfl
          _ ≤ (c * (ONE - p.fee)) * p.rate s.tokenIn :=
              Nat.mul_le_mul_right (p.rate s.tokenIn) hc_low
          _ = c * (ONE - p.fee) * p.rate s.tokenIn := by ac_rfl
      have hgoal : ONE * ONE * outPrice m p s ≤ c * (ONE - p.fee) * p.rate s.tokenIn := by
        rw [hP_eq]
        calc ONE * ONE * m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
              (upscaleUp s.amount (p.rate s.tokenOut))
            = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
              (upscaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE := by ac_rfl
          _ ≤ c * (ONE - p.fee) * p.rate s.tokenIn := hchain
      exact hgoal

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c hmono hkind hvalid hswap
  have hon : onSwap m p s = swapGivenOut m p s := by unfold onSwap; simp [hkind]
  rw [hon] at hswap
  unfold swapGivenOut at hswap
  by_cases hlt : (upscaleArray p) s.tokenOut ≤ upscaleUp s.amount (p.rate s.tokenOut)
  · rw [if_pos hlt] at hswap
    cases hswap
  · rw [if_neg hlt] at hswap
    cases hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      rw [hdown] at hswap
      simp at hswap
    | some amt =>
      rw [hdown] at hswap
      simp only at hswap
      have hadd : addSwapFeeAmount amt p.fee = some c := hswap
      have hfee_lt := fee_lt_of_add_some _ _ _ hadd
      have hc_eq := add_some_eq_ceil _ _ _ hadd
      have hamt_eq : amt
          = ProofForgeFin.ceilDiv (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) := by
        have h := divUp_some_eq _ _ _ hdown
        exact h.2
      have hrate_ne : p.rate s.tokenIn ≠ 0 := (divUp_some_eq _ _ _ hdown).1
      have hrate_pos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrate_ne
      have hfee_pos : 0 < ONE - p.fee := by omega
      have hP_eq : outPrice m p s
          = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) := by
        unfold outPrice
        have harr : upscaleArray p = scaledBalances p := upscaleArray_eq p
        have hup2 : upscaleUp s.amount (p.rate s.tokenOut)
            = scaleUp s.amount (p.rate s.tokenOut) := upscaleUp_eq_scaleUp _ _
        rw [harr, hup2]
      have hamt_up : amt * p.rate s.tokenIn
          < m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn := by
        have h := (ProofForgeFin.ceilDiv_spec (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) hrate_pos).2
        rw [← hamt_eq] at h
        exact h
      have hc_up : c * (ONE - p.fee) < amt * ONE + (ONE - p.fee) := by
        have h := (ProofForgeFin.ceilDiv_spec (amt * ONE) (ONE - p.fee) hfee_pos).2
        rw [← hc_eq] at h
        exact h
      by_cases hc0 : c = 0
      · subst hc0
        simp only [Nat.zero_sub, Nat.zero_mul]
        have hinner : 0 < ONE * outPrice m p s + p.rate s.tokenIn := by omega
        have hpos : 0 < ONE * (ONE * outPrice m p s + p.rate s.tokenIn) :=
          Nat.mul_pos one_pos hinner
        exact hpos
      · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
        have hpred : c - 1 + 1 = c := Nat.succ_pred_eq_of_pos hc_pos
        have hdecomp : (c - 1) * (ONE - p.fee) + (ONE - p.fee)
            = c * (ONE - p.fee) := by
          have h1 : (c - 1) * (ONE - p.fee) + 1 * (ONE - p.fee)
              = (c - 1 + 1) * (ONE - p.fee) := (Nat.add_mul _ _ _).symm
          have h2 : (1 : Nat) * (ONE - p.fee) = (ONE - p.fee) := Nat.one_mul _
          rw [h2] at h1
          rw [hpred] at h1
          exact h1
        have hlt1 : (c - 1) * (ONE - p.fee) < amt * ONE := by omega
        have hlt2 : (c - 1) * (ONE - p.fee) * p.rate s.tokenIn
            < amt * ONE * p.rate s.tokenIn :=
          Nat.mul_lt_mul_of_pos_right hlt1 hrate_pos
        have hlt3 : amt * ONE * p.rate s.tokenIn
            < (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
              (upscaleUp s.amount (p.rate s.tokenOut)) * ONE
              + p.rate s.tokenIn) * ONE := by
          have hle : amt * p.rate s.tokenIn
              < m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
                (upscaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn := hamt_up
          have hmul := Nat.mul_lt_mul_of_pos_right hle one_pos
          calc amt * ONE * p.rate s.tokenIn
              = (amt * p.rate s.tokenIn) * ONE := by ac_rfl
            _ < (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
                (upscaleUp s.amount (p.rate s.tokenOut)) * ONE
                + p.rate s.tokenIn) * ONE := hmul
        have hlt4 : (c - 1) * (ONE - p.fee) * p.rate s.tokenIn
            < (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
              (upscaleUp s.amount (p.rate s.tokenOut)) * ONE
              + p.rate s.tokenIn) * ONE :=
          Nat.lt_of_lt_of_le hlt2 (Nat.le_of_lt hlt3)
        rw [← hP_eq] at hlt4
        calc (c - 1) * (ONE - p.fee) * p.rate s.tokenIn
            < (outPrice m p s * ONE + p.rate s.tokenIn) * ONE := hlt4
          _ = ONE * (ONE * outPrice m p s + p.rate s.tokenIn) := by ac_rfl

theorem givenIn_BIn_ge (bIn amt n r : Nat) (hn_le : n ≤ amt) :
    bIn * r / ONE + n * r / ONE ≤ (bIn + amt) * r / ONE := by
  have h1 : bIn * r / ONE + n * r / ONE ≤ (bIn * r + n * r) / ONE :=
    ProofForgeFin.div_add_div_le _ _ _
  have h2 : bIn * r + n * r ≤ (bIn + amt) * r := by
    have e1 : (bIn + amt) * r = bIn * r + amt * r := Nat.add_mul _ _ _
    have hle : n * r ≤ amt * r := Nat.mul_le_mul_right r hn_le
    omega
  have h3 : (bIn * r + n * r) / ONE ≤ (bIn + amt) * r / ONE :=
    Nat.div_le_div_right h2
  exact Nat.le_trans h1 h3

theorem givenOut_BIn_ge (bIn c amt P r : Nat)
    (hamt_le_c : amt ≤ c) (hP_amt : P * ONE ≤ amt * r) :
    bIn * r / ONE + P ≤ (bIn + c) * r / ONE := by
  have hPc : P ≤ c * r / ONE := by
    have h1 : P * ONE ≤ c * r := by
      calc P * ONE ≤ amt * r := hP_amt
        _ ≤ c * r := Nat.mul_le_mul_right r hamt_le_c
    exact (Nat.le_div_iff_mul_le one_pos).2 h1
  have h1 : bIn * r / ONE + c * r / ONE ≤ (bIn * r + c * r) / ONE :=
    ProofForgeFin.div_add_div_le _ _ _
  have h2 : bIn * r + c * r = (bIn + c) * r := (Nat.add_mul _ _ _).symm
  have h3 : bIn * r / ONE + c * r / ONE ≤ (bIn + c) * r / ONE := by
    rw [h2] at h1
    exact h1
  calc bIn * r / ONE + P ≤ bIn * r / ONE + c * r / ONE :=
        Nat.add_le_add_left hPc _
    _ ≤ (bIn + c) * r / ONE := h3

theorem givenIn_BOut_ge (bOut y P r : Nat) (hy : y ≤ bOut) (hPle : P ≤ bOut * r / ONE)
    (hy_eq : y = P * ONE / r) (hr : 0 < r) :
    bOut * r / ONE - P ≤ (bOut - y) * r / ONE := by
  have hPB : P * ONE ≤ (bOut * r / ONE) * ONE := Nat.mul_le_mul_right ONE hPle
  have hBle : (bOut * r / ONE) * ONE ≤ bOut * r := Nat.div_mul_le_self _ _
  have hyR : y * r ≤ P * ONE := by
    have hf := (ProofForgeFin.floor_spec (P * ONE) r hr).1
    rw [hy_eq]
    exact hf
  have hsub1 : ((bOut * r / ONE) - P) * ONE
      = (bOut * r / ONE) * ONE - P * ONE := Nat.sub_mul _ _ _
  have hsub2 : (bOut - y) * r = bOut * r - y * r := Nat.sub_mul _ _ _
  have hstep1 : (bOut * r / ONE) * ONE - P * ONE ≤ bOut * r - P * ONE :=
    Nat.sub_le_sub_right hBle (P * ONE)
  have hstep2 : bOut * r - P * ONE ≤ bOut * r - y * r :=
    Nat.sub_le_sub_left hyR (bOut * r)
  have hle : ((bOut * r / ONE) - P) * ONE ≤ (bOut - y) * r := by
    rw [hsub1, hsub2]
    exact Nat.le_trans hstep1 hstep2
  exact (Nat.le_div_iff_mul_le one_pos).2 hle

theorem givenOut_BOut_ge (bOut a r : Nat) (ha : a ≤ bOut)
    (hup_le : ProofForgeFin.ceilDiv (a * r) ONE ≤ bOut * r / ONE) :
    bOut * r / ONE - ProofForgeFin.ceilDiv (a * r) ONE ≤ (bOut - a) * r / ONE := by
  have hBone : (bOut * r / ONE) * ONE ≤ bOut * r := Nat.div_mul_le_self _ _
  have hUone : a * r ≤ ProofForgeFin.ceilDiv (a * r) ONE * ONE :=
    ProofForgeFin.le_ceilDiv_mul _ _ one_pos
  have hsub1 : ((bOut * r / ONE) - ProofForgeFin.ceilDiv (a * r) ONE) * ONE
      = (bOut * r / ONE) * ONE - ProofForgeFin.ceilDiv (a * r) ONE * ONE :=
    Nat.sub_mul _ _ _
  have hsub2 : (bOut - a) * r = bOut * r - a * r := Nat.sub_mul _ _ _
  have hstep1 : (bOut * r / ONE) * ONE - ProofForgeFin.ceilDiv (a * r) ONE * ONE
      ≤ bOut * r - ProofForgeFin.ceilDiv (a * r) ONE * ONE :=
    Nat.sub_le_sub_right hBone (ProofForgeFin.ceilDiv (a * r) ONE * ONE)
  have hstep2 : bOut * r - ProofForgeFin.ceilDiv (a * r) ONE * ONE
      ≤ bOut * r - a * r :=
    Nat.sub_le_sub_left hUone (bOut * r)
  have hle : ((bOut * r / ONE) - ProofForgeFin.ceilDiv (a * r) ONE) * ONE
      ≤ (bOut - a) * r := by
    rw [hsub1, hsub2]
    exact Nat.le_trans hstep1 hstep2
  exact (Nat.le_div_iff_mul_le one_pos).2 hle

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hwb hstep
  unfold step at hstep
  by_cases hvalid : Valid p s
  · rw [if_pos hvalid] at hstep
    have hne : s.tokenIn ≠ s.tokenOut := hvalid.1
    have htin : s.tokenIn < p.n := hvalid.2.1
    have htout : s.tokenOut < p.n := hvalid.2.2
    cases hkind : s.kind with
    | givenIn =>
      have hon : onSwap m p s = swapGivenIn m p s := by unfold onSwap; simp [hkind]
      rw [hon] at hstep
      cases hsub : subtractSwapFeeAmount s.amount p.fee with
      | none =>
        have hnone : swapGivenIn m p s = none := by unfold swapGivenIn; simp [hsub]
        rw [hnone] at hstep
        cases hstep
      | some n =>
        have heq := swapGivenIn_eq m p s n hsub
        rw [heq] at hstep
        cases hdown : downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
            (upscale n (p.rate s.tokenIn))) (p.rate s.tokenOut) with
        | none =>
          simp [hdown] at hstep
        | some y =>
          simp [hdown] at hstep
          have hset_eq : settle p s y = some p' := hstep
          unfold settle at hset_eq
          have ham : amountOut s y = y := by unfold amountOut; simp [hkind]
          rw [ham] at hset_eq
          by_cases hle : y ≤ p.balance s.tokenOut
          · rw [if_pos hle] at hset_eq
            cases hset_eq
            have hn_eq := sub_n_eq _ _ _ hsub
            have hle_mu := mulUp_le_of_sub_some _ _ _ hsub
            have hn_le : n ≤ s.amount := by rw [hn_eq]; exact Nat.sub_le _ _
            have hdown_eq := divDown_some_eq _ _ _ hdown
            have hrate_pos : 0 < p.rate s.tokenOut :=
              Nat.pos_of_ne_zero hdown_eq.1
            have hy_eq : y
                = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut := hdown_eq.2
            have hsound := hwb.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
              (upscale n (p.rate s.tokenIn)) hne htin htout
            have hPle : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                (upscale n (p.rate s.tokenIn)) ≤ (upscaleArray p) s.tokenOut := hsound.1
            have hBarr : upscaleArray p = scaledBalances p := upscaleArray_eq p
            have hBin : (upscaleArray p) s.tokenIn
                + upscale n (p.rate s.tokenIn)
                ≤ scaledBalances
                  { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s y) s.tokenOut (p.balance s.tokenOut - amountOut s y) } s.tokenIn := by
              have h1 : (upscaleArray p) s.tokenIn
                  = p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
              have h2 : upscale n (p.rate s.tokenIn)
                  = n * p.rate s.tokenIn / ONE := rfl
              have h3 : scaledBalances
                  { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s y) s.tokenOut (p.balance s.tokenOut - amountOut s y) } s.tokenIn
                  = (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE := by
                unfold scaledBalances scaleDown update2
                simp [hkind]
                unfold amountIn
                simp [hkind]
              rw [h1, h2, h3]
              exact givenIn_BIn_ge _ _ _ _ hn_le
            have hBout : (upscaleArray p) s.tokenOut
                - m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn))
                ≤ scaledBalances
                  { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s y) s.tokenOut (p.balance s.tokenOut - amountOut s y) } s.tokenOut := by
              have h1 : (upscaleArray p) s.tokenOut
                  = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
              have h2 : scaledBalances
                  { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s y) s.tokenOut (p.balance s.tokenOut - amountOut s y) } s.tokenOut
                  = (p.balance s.tokenOut - y) * p.rate s.tokenOut / ONE := by
                unfold scaledBalances scaleDown update2
                have hji : s.tokenOut ≠ s.tokenIn := Ne.symm hne
                simp [hji]
                unfold amountOut
                simp [hkind]
              rw [h1, h2]
              exact givenIn_BOut_ge _ _ _ _ hle hPle hy_eq hrate_pos
            have hmid_le : m.invariant (update2 (upscaleArray p) s.tokenIn
                ((upscaleArray p) s.tokenIn + upscale n (p.rate s.tokenIn)) s.tokenOut
                ((upscaleArray p) s.tokenOut - m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn))))
                ≤ m.invariant (scaledBalances
                { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s y) s.tokenOut (p.balance s.tokenOut - amountOut s y) }) := by
              apply hwb.monotone
              intro k hk
              by_cases hi : k = s.tokenIn
              · subst hi
                unfold update2
                simp only [if_pos rfl]
                exact hBin
              · by_cases hj : k = s.tokenOut
                · subst hj
                  unfold update2
                  simp [hi]
                  exact hBout
                · unfold update2
                  simp [hi, hj]
                  unfold scaledBalances scaleDown
                  simp [hi, hj]
            have hsound_le : m.invariant (upscaleArray p) ≤ m.invariant (update2 (upscaleArray p) s.tokenIn
                ((upscaleArray p) s.tokenIn + upscale n (p.rate s.tokenIn)) s.tokenOut
                ((upscaleArray p) s.tokenOut - m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)))) := hsound.2
            have hval : value m p = m.invariant (upscaleArray p) := by
              unfold value
              rw [hBarr]
            calc value m p = m.invariant (upscaleArray p) := hval
              _ ≤ m.invariant (update2 (upscaleArray p) s.tokenIn
                ((upscaleArray p) s.tokenIn + upscale n (p.rate s.tokenIn)) s.tokenOut
                ((upscaleArray p) s.tokenOut - m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
                  (upscale n (p.rate s.tokenIn)))) := hsound_le
              _ ≤ m.invariant (scaledBalances
                  { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s y) s.tokenOut (p.balance s.tokenOut - amountOut s y) }) := hmid_le
          · rw [if_neg hle] at hset_eq
            cases hset_eq
    | givenOut =>
      have hon : onSwap m p s = swapGivenOut m p s := by unfold onSwap; simp [hkind]
      rw [hon] at hstep
      unfold swapGivenOut at hstep
      by_cases hlt : (upscaleArray p) s.tokenOut ≤ upscaleUp s.amount (p.rate s.tokenOut)
      · rw [if_pos hlt] at hstep
        cases hstep
      · rw [if_neg hlt] at hstep
        cases hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
        | none =>
          simp [hdown] at hstep
        | some amt =>
          simp [hdown] at hstep
          cases hadd : addSwapFeeAmount amt p.fee with
          | none =>
            simp [hadd] at hstep
          | some c =>
            simp [hadd] at hstep
            have hset_eq : settle p s c = some p' := hstep
            unfold settle at hset_eq
            have ham : amountOut s c = s.amount := by unfold amountOut; simp [hkind]
            rw [ham] at hset_eq
            by_cases hle : s.amount ≤ p.balance s.tokenOut
            · rw [if_pos hle] at hset_eq
              cases hset_eq
              sorry
            · rw [if_neg hle] at hset_eq
              cases hset_eq
  · rw [if_neg hvalid] at hstep
    cases hstep

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' hwb hstep
  sorry

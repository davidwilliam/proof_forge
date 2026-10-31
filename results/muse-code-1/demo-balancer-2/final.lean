import BalancerSwap.Spec
import ProofForgeFin
/-!
Fixed regular-swap path of Balancer V2's Composable Stable Pool (osETH/WETH pool
0xDACf5Fa19b1f720111609043ac67A9818262850c).

Fix for the November 2025 drain: `_swapGivenOut` upscaled the requested amount out with
`mulDown` (rounding down). A request for 17 wei of osETH is worth 17.988 of the pool's
18-decimal units, but the pool math was asked to price 17 units, so the trader was charged
far too little. The fix upscales the amount out with rounding up (`scaleUp`), so the math
prices at least the exact amount out, and refuses the swap unless the rounded-up amount is
strictly below the pool's scaled balance (the math's contract only covers that case).
Every other rounding already favours the pool: the amount in is priced from the rounded-down
net amount, the result is converted back down (given-in) or up (given-out), and the fee is
added up.
-/
namespace BalancerSwap

/-- `ONE` is positive. -/
theorem one_pos : 0 < ONE := by decide

/-- `a * ONE / r`: a scaled amount back in raw units, rounded down (`_downscaleDown`). -/
def downDown (a r : Nat) : Nat := a * ONE / r

/-- `⌈a * ONE / r⌉`: a scaled amount back in raw units, rounded up (`_downscaleUp`). -/
def downUp (a r : Nat) : Nat := ProofForgeFin.ceilDiv (a * ONE) r

/-- `_swapGivenIn`: price the fee-adjusted amount in (rounded down) and convert back down. -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if p.rate s.tokenOut = 0 then none
  else some (downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut))

/-- `_swapGivenOut`: price the amount out rounded up and convert back up, adding the fee up. -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut then
    if p.rate s.tokenIn = 0 then none
    else if p.fee < ONE then
      some (downUp (downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn)) (ONE - p.fee))
    else none
  else none

/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

/-! ## Rounding bridges -/

theorem scaleUp_eq_ceil (a r : Nat) : scaleUp a r = ProofForgeFin.ceilDiv (a * r) ONE := by
  unfold scaleUp
  rw [ProofForgeFin.ceilDiv_eq_add_pred _ _ one_pos]

theorem scaleUp_lower (a r : Nat) : a * r ≤ scaleUp a r * ONE := by
  rw [scaleUp_eq_ceil]
  exact (ProofForgeFin.ceilDiv_spec _ _ one_pos).1

theorem scaleUp_upper (a r : Nat) : scaleUp a r * ONE < a * r + ONE := by
  rw [scaleUp_eq_ceil]
  exact (ProofForgeFin.ceilDiv_spec _ _ one_pos).2

theorem scaleDown_upper (a r : Nat) : scaleDown a r * ONE ≤ a * r := by
  unfold scaleDown
  exact Nat.div_mul_le_self _ _

theorem netIn_spec (p : Pool) (s : Swap) :
    netInDown p s * (ONE * ONE) ≤ s.amount * (ONE - p.fee) * p.rate s.tokenIn := by
  unfold netInDown
  exact Nat.div_mul_le_self _ _

theorem netInLessOne_le (p : Pool) (s : Swap) : netInLessOneDown p s ≤ netInDown p s := by
  unfold netInLessOneDown netInDown
  apply ProofForgeFin.div_mono_left
  exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem downDown_upper (y r : Nat) : downDown y r * r ≤ y * ONE := by
  unfold downDown
  exact Nat.div_mul_le_self _ _

theorem downDown_lower (y r : Nat) (hr : 0 < r) : y * ONE < (downDown y r + 1) * r := by
  unfold downDown
  exact ProofForgeFin.lt_div_add_one_mul _ _ hr

theorem downUp_lower (a r : Nat) (hr : 0 < r) : a * ONE ≤ downUp a r * r := by
  unfold downUp
  exact (ProofForgeFin.ceilDiv_spec _ _ hr).1

theorem downUp_upper (a r : Nat) (hr : 0 < r) : downUp a r * r < a * ONE + r := by
  unfold downUp
  exact (ProofForgeFin.ceilDiv_spec _ _ hr).2

/-! ## Balance updates -/

theorem update2_same (b : Nat → Nat) (i x j y : Nat) : update2 b i x j y i = x := by
  unfold update2
  simp

theorem update2_second (b : Nat → Nat) (i x j y : Nat) (h : j ≠ i) :
    update2 b i x j y j = y := by
  unfold update2
  simp [h]

theorem update2_other (b : Nat → Nat) (i x j y k : Nat) (h1 : k ≠ i) (h2 : k ≠ j) :
    update2 b i x j y k = b k := by
  unfold update2
  simp [h1, h2]

theorem onSwap_givenIn (m : PoolMath) (p : Pool) (s : Swap) (hkind : s.kind = Kind.givenIn) :
    onSwap m p s = swapGivenIn m p s := by
  unfold onSwap
  rw [hkind]

theorem onSwap_givenOut (m : PoolMath) (p : Pool) (s : Swap) (hkind : s.kind = Kind.givenOut) :
    onSwap m p s = swapGivenOut m p s := by
  unfold onSwap
  rw [hkind]

theorem kind_cases (s : Swap) : s.kind = Kind.givenIn ∨ s.kind = Kind.givenOut := by
  cases s.kind <;> simp

/-! ## What a successful quote looks like -/

theorem swapGivenIn_some (m : PoolMath) (p : Pool) (s : Swap) (q : Nat)
    (hq : swapGivenIn m p s = some q) :
    p.rate s.tokenOut ≠ 0 ∧
    q = downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := by
  unfold swapGivenIn at hq
  by_cases hr0 : p.rate s.tokenOut = 0
  · rw [if_pos hr0] at hq
    simp at hq
  · rw [if_neg hr0] at hq
    exact ⟨hr0, (Option.some_inj.mp hq).symm⟩

theorem swapGivenOut_some (m : PoolMath) (p : Pool) (s : Swap) (c : Nat)
    (hq : swapGivenOut m p s = some c) :
    scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut ∧
    p.rate s.tokenIn ≠ 0 ∧ p.fee < ONE ∧
    c = downUp (downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn)) (ONE - p.fee) := by
  unfold swapGivenOut at hq
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
  · rw [if_pos hlt] at hq
    by_cases hr0 : p.rate s.tokenIn = 0
    · rw [if_pos hr0] at hq
      simp at hq
    · rw [if_neg hr0] at hq
      by_cases hf : p.fee < ONE
      · rw [if_pos hf] at hq
        exact ⟨hlt, hr0, hf, (Option.some_inj.mp hq).symm⟩
      · rw [if_neg hf] at hq
        simp at hq
  · rw [if_neg hlt] at hq
    simp at hq

theorem step_some (m : PoolMath) (p : Pool) (s : Swap) (mid : Pool)
    (h : step onSwap m p s = some mid) :
    Valid p s ∧ ∃ c, onSwap m p s = some c ∧ settle p s c = some mid := by
  unfold step at h
  by_cases hV : Valid p s
  · rw [if_pos hV] at h
    cases ho : onSwap m p s
    case none => simp [ho] at h
    case some c => simp [ho] at h; exact ⟨hV, c, rfl, h⟩
  · rw [if_neg hV] at h
    simp at h

theorem settle_some (p : Pool) (s : Swap) (q : Nat) (mid : Pool)
    (h : settle p s q = some mid) :
    amountOut s q ≤ p.balance s.tokenOut ∧
    mid = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s q) s.tokenOut (p.balance s.tokenOut - amountOut s q) } := by
  unfold settle at h
  by_cases hle : amountOut s q ≤ p.balance s.tokenOut
  · rw [if_pos hle] at h
    exact ⟨hle, (Option.some_inj.mp h).symm⟩
  · rw [if_neg hle] at h
    simp at h

/-! ## Raw-balance bounds -/

theorem rateOut_pos_of_lt (p : Pool) (s : Swap)
    (h : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut) :
    0 < p.rate s.tokenOut := by
  rcases Nat.eq_zero_or_pos (p.rate s.tokenOut) with hz | hp
  · exfalso
    have e1 : scaleUp s.amount 0 = 0 := by
      unfold scaleUp
      have h1 : s.amount * 0 + (ONE - 1) = ONE - 1 := by simp
      rw [h1]
      have h2 : ONE - 1 < ONE := by
        have := one_pos
        omega
      exact Nat.div_eq_of_lt h2
    have e2 : scaledBalances p s.tokenOut = 0 := by
      unfold scaledBalances scaleDown
      rw [hz, Nat.mul_zero]
      exact Nat.zero_div _
    rw [hz] at h
    rw [e1, e2] at h
    omega
  · exact hp

theorem givenOut_raw_le_bal (p : Pool) (s : Swap)
    (h : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut) :
    s.amount ≤ p.balance s.tokenOut := by
  have hr := rateOut_pos_of_lt p s h
  have e1 : s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE :=
    scaleUp_lower _ _
  have e2 : scaledBalances p s.tokenOut * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
    unfold scaledBalances scaleDown
    exact Nat.div_mul_le_self _ _
  have e3 : scaleUp s.amount (p.rate s.tokenOut) * ONE < scaledBalances p s.tokenOut * ONE :=
    Nat.mul_lt_mul_of_pos_right h one_pos
  have hlt : s.amount * p.rate s.tokenOut < p.balance s.tokenOut * p.rate s.tokenOut := by
    omega
  rcases Nat.le_total s.amount (p.balance s.tokenOut) with hle | hge
  · exact hle
  · have g : p.balance s.tokenOut * p.rate s.tokenOut ≤ s.amount * p.rate s.tokenOut :=
      Nat.mul_le_mul_right _ hge
    omega

theorem givenIn_quote_le_bal (m : PoolMath) (p : Pool) (s : Swap) (W : WellBehaved m p.n)
    (hne : s.tokenIn ≠ s.tokenOut) (hlt1 : s.tokenIn < p.n) (hlt2 : s.tokenOut < p.n) :
    downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut)
      ≤ p.balance s.tokenOut := by
  have hS := W.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hne hlt1 hlt2
  have e1 : downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut)
      * p.rate s.tokenOut
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    downDown_upper _ _
  have e2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
    have f1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
        ≤ scaledBalances p s.tokenOut := hS.1
    have f2 : scaledBalances p s.tokenOut * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
      unfold scaledBalances scaleDown
      exact Nat.div_mul_le_self _ _
    have g1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
        ≤ scaledBalances p s.tokenOut * ONE :=
      Nat.mul_le_mul_right _ f1
    omega
  unfold downDown
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm (p.rate s.tokenOut) (p.balance s.tokenOut)]
  exact e2

/-! ## The wrapper goes through and prices in the pool's favour -/

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s W hkind hV hr _hfee
  have hV' : s.tokenIn ≠ s.tokenOut ∧ s.tokenIn < p.n ∧ s.tokenOut < p.n := hV
  obtain ⟨hne, hlt1, hlt2⟩ := hV'
  have hrne : p.rate s.tokenOut ≠ 0 := Nat.pos_iff_ne_zero.mp hr
  have hq : swapGivenIn m p s
      = some (downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut)) := by
    unfold swapGivenIn
    rw [if_neg hrne]
  have hset : amountOut s (downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut))
      ≤ p.balance s.tokenOut := by
    unfold amountOut
    rw [hkind]
    show downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut)
      ≤ p.balance s.tokenOut
    exact givenIn_quote_le_bal m p s W hne hlt1 hlt2
  have hon : onSwap m p s = swapGivenIn m p s := onSwap_givenIn m p s hkind
  unfold step
  rw [if_pos hV, hon, hq]
  show (settle p s (downDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut))).isSome
  simp [settle, if_pos hset]

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s _W hkind hV hr hfee hscale
  have hrne : p.rate s.tokenIn ≠ 0 := Nat.pos_iff_ne_zero.mp hr
  have hscale' : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := hscale
  have hq : swapGivenOut m p s = some (downUp (downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn)) (ONE - p.fee)) := by
    unfold swapGivenOut
    rw [if_pos hscale', if_neg hrne, if_pos hfee]
  have hset : amountOut s (downUp (downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn)) (ONE - p.fee))
      ≤ p.balance s.tokenOut := by
    unfold amountOut
    rw [hkind]
    show s.amount ≤ p.balance s.tokenOut
    exact givenOut_raw_le_bal p s hscale
  have hon : onSwap m p s = swapGivenOut m p s := onSwap_givenOut m p s hkind
  unfold step
  rw [if_pos hV, hon, hq]
  show (settle p s (downUp (downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn)) (ONE - p.fee))).isSome
  simp [settle, if_pos hset]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y _hmono hkind _hV hq
  have hon : onSwap m p s = swapGivenIn m p s := onSwap_givenIn m p s hkind
  rw [hon] at hq
  obtain ⟨_hrne, hqy⟩ := swapGivenIn_some m p s y hq
  rw [hqy]
  unfold downDown
  have e : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut
      * p.rate s.tokenOut
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    Nat.div_mul_le_self _ _
  have e2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
    ac_rfl
  omega

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hkind _hV hq
  have hm' : (∀ (b : Nat → Nat) (i j x y : Nat),
      x ≤ y → m.outGivenIn b i j x ≤ m.outGivenIn b i j y)
    ∧ (∀ (b : Nat → Nat) (i j x y : Nat),
      x ≤ y → m.inGivenOut b i j x ≤ m.inGivenOut b i j y) := hmono
  obtain ⟨hmo1, _hmo2⟩ := hm'
  have hon : onSwap m p s = swapGivenIn m p s := onSwap_givenIn m p s hkind
  rw [hon] at hq
  obtain ⟨hrne, hqy⟩ := swapGivenIn_some m p s y hq
  have hr : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrne
  have hle : netInLessOneDown p s ≤ netInDown p s := netInLessOne_le p s
  have hm := hmo1 (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) (netInDown p s) hle
  rw [hqy]
  unfold downDown
  have e1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      < (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1)
        * p.rate s.tokenOut :=
    ProofForgeFin.lt_div_add_one_mul _ _ hr
  have e2 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
      ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
    Nat.mul_le_mul_left _ hm
  have e3 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
      = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
    ac_rfl
  omega
theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c _hmono hkind _hV hq
  have hon : onSwap m p s = swapGivenOut m p s := onSwap_givenOut m p s hkind
  rw [hon] at hq
  obtain ⟨_hlt, hrne, _hfee, hqc⟩ := swapGivenOut_some m p s c hq
  have hr : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
  have hD : 0 < ONE - p.fee := by omega
  have hprice : outPrice m p s
      = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := rfl
  rw [hprice]
  have e1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE
      ≤ downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn :=
    downUp_lower _ _ hr
  have e2 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE
      ≤ c * (ONE - p.fee) := by
    rw [hqc]
    exact downUp_lower _ _ hD
  have g1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE
      ≤ downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn * ONE :=
    Nat.mul_le_mul_right _ e1
  have g2 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn
      ≤ c * (ONE - p.fee) * p.rate s.tokenIn :=
    Nat.mul_le_mul_right _ e2
  have g3 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn * ONE
      = downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn := by
    ac_rfl
  have g0 : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))
      = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE := by
    ac_rfl
  rw [g0]
  omega

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c _hmono hkind _hV hq
  have hon : onSwap m p s = swapGivenOut m p s := onSwap_givenOut m p s hkind
  rw [hon] at hq
  obtain ⟨_hlt, hrne, _hfee, hqc⟩ := swapGivenOut_some m p s c hq
  have hr : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
  have hD : 0 < ONE - p.fee := by omega
  have hprice : outPrice m p s
      = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := rfl
  rw [hprice]
  have e1 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn
      < m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn :=
    downUp_upper _ _ hr
  have e2 : c * (ONE - p.fee)
      < downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE + (ONE - p.fee) := by
    rw [hqc]
    exact downUp_upper _ _ hD
  by_cases hc : c = 0
  · subst hc
    have hpos : 0 < ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) := by
      apply Nat.mul_pos one_pos
      omega
    have h00 : (0 - 1 : Nat) = 0 := by omega
    simp only [h00, Nat.zero_mul]
    exact hpos
  · have hc1 : 1 ≤ c := by omega
    have hcc : (c - 1) * (ONE - p.fee) + 1 * (ONE - p.fee) = c * (ONE - p.fee) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hc1]
    have h1d : 1 * (ONE - p.fee) = ONE - p.fee := Nat.one_mul _
    have d1 : (c - 1) * (ONE - p.fee)
        < downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE := by
      omega
    have f1 : (c - 1) * (ONE - p.fee) * p.rate s.tokenIn
        < downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn :=
      Nat.mul_lt_mul_of_pos_right d1 hr
    have f2 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn
        = downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn * ONE := by
      ac_rfl
    have f3 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn * ONE
        < (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
      Nat.mul_lt_mul_of_pos_right e1 one_pos
    have g0 : ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn)
        = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE := by
      ac_rfl
    rw [g0]
    omega
/-! ## Single swaps and batches keep the pool's value -/

theorem step_preserves_n (m : PoolMath) (p : Pool) (s : Swap) (mid : Pool)
    (h : step onSwap m p s = some mid) : mid.n = p.n := by
  obtain ⟨_hV, _c, _hq, hset⟩ := step_some m p s mid h
  obtain ⟨_hraw, hmid⟩ := settle_some p s _ mid hset
  rw [hmid]

theorem step_value_mono (m : PoolMath) (p : Pool) (s : Swap) (mid : Pool)
    (W : WellBehaved m p.n) (h : step onSwap m p s = some mid) :
    value m p ≤ value m mid := by
  obtain ⟨hV, c, hq, hset⟩ := step_some m p s mid h
  have hV' : s.tokenIn ≠ s.tokenOut ∧ s.tokenIn < p.n ∧ s.tokenOut < p.n := hV
  obtain ⟨hne, hlt1, hlt2⟩ := hV'
  obtain ⟨_hraw, hmid⟩ := settle_some p s c mid hset
  rcases kind_cases s with hkind | hkind
  · -- givenIn: the scaled balances grow by at least the net amount in, minus the payout.
    have hon : onSwap m p s = swapGivenIn m p s := onSwap_givenIn m p s hkind
    rw [hon] at hq
    obtain ⟨hrne, hqc⟩ := swapGivenIn_some m p s c hq
    have hr : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrne
    have eIn : amountIn s c = s.amount := by unfold amountIn; rw [hkind]
    have eOut : amountOut s c = c := by unfold amountOut; rw [hkind]
    have hbal : ∀ k, mid.balance k
        = update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - c) k := by
      intro k
      rw [hmid]
      show update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) k = _
      rw [eIn, eOut]
    have hrate : ∀ k, mid.rate k = p.rate k := by
      intro k
      rw [hmid]
    have hn : mid.n = p.n := by rw [hmid]
    have hS := W.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hne hlt1 hlt2
    have eX : netInDown p s * ONE ≤ s.amount * p.rate s.tokenIn := by
      have f0 : netInDown p s * (ONE * ONE)
          ≤ s.amount * (ONE - p.fee) * p.rate s.tokenIn := netIn_spec p s
      have f1 : s.amount * (ONE - p.fee) * p.rate s.tokenIn
          ≤ (s.amount * p.rate s.tokenIn) * ONE := by
        have g : s.amount * (ONE - p.fee) ≤ s.amount * ONE :=
          Nat.mul_le_mul_left _ (Nat.sub_le ONE p.fee)
        have g2 : s.amount * (ONE - p.fee) * p.rate s.tokenIn
            ≤ s.amount * ONE * p.rate s.tokenIn :=
          Nat.mul_le_mul_right _ g
        have e : s.amount * ONE * p.rate s.tokenIn
            = (s.amount * p.rate s.tokenIn) * ONE := by ac_rfl
        omega
      have e : netInDown p s * (ONE * ONE) = netInDown p s * ONE * ONE := by ac_rfl
      have f2 : netInDown p s * ONE * ONE ≤ (s.amount * p.rate s.tokenIn) * ONE := by omega
      exact Nat.le_of_mul_le_mul_right f2 one_pos
    have hpt : ∀ k, k < p.n →
        update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s)
          s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k
        ≤ scaledBalances mid k := by
      intro k hk
      by_cases hki : k = s.tokenIn
      · subst hki
        rw [update2_same]
        have hBB : scaledBalances mid s.tokenIn
            = (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE := by
          unfold scaledBalances scaleDown
          rw [hbal s.tokenIn, update2_same, hrate s.tokenIn]
        rw [hBB]
        apply (ProofForgeFin.le_div_iff one_pos).2
        have eB : scaledBalances p s.tokenIn * ONE
            ≤ p.balance s.tokenIn * p.rate s.tokenIn :=
          scaleDown_upper _ _
        have t1 : (scaledBalances p s.tokenIn + netInDown p s) * ONE
            = scaledBalances p s.tokenIn * ONE + netInDown p s * ONE :=
          Nat.add_mul _ _ _
        have t2 : (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn
            = p.balance s.tokenIn * p.rate s.tokenIn + s.amount * p.rate s.tokenIn :=
          Nat.add_mul _ _ _
        omega
      · by_cases hkj : k = s.tokenOut
        · subst hkj
          rw [update2_second _ _ _ _ _ (Ne.symm hne)]
          have hBB : scaledBalances mid s.tokenOut
              = (p.balance s.tokenOut - c) * p.rate s.tokenOut / ONE := by
            unfold scaledBalances scaleDown
            rw [hbal s.tokenOut, update2_second _ _ _ _ _ (Ne.symm hne), hrate s.tokenOut]
          rw [hBB]
          apply (ProofForgeFin.le_div_iff one_pos).2
          have eB : scaledBalances p s.tokenOut * ONE
              ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
            scaleDown_upper _ _
          have eq : c * p.rate s.tokenOut
              ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
            rw [hqc]
            unfold downDown
            exact Nat.div_mul_le_self _ _
          have t1 : (scaledBalances p s.tokenOut
              - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) * ONE
              = scaledBalances p s.tokenOut * ONE
              - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
            Nat.sub_mul _ _ _
          have t2 : (p.balance s.tokenOut - c) * p.rate s.tokenOut
              = p.balance s.tokenOut * p.rate s.tokenOut - c * p.rate s.tokenOut :=
            Nat.sub_mul _ _ _
          omega
        · have hkk : scaledBalances mid k = scaledBalances p k := by
            unfold scaledBalances scaleDown
            rw [hbal k, update2_other _ _ _ _ _ _ hki hkj, hrate k]
          rw [update2_other _ _ _ _ _ _ hki hkj, hkk]
          exact Nat.le_refl _
    have hmono := W.monotone _ _ hpt
    unfold value
    exact Nat.le_trans hS.2 hmono
  · -- givenOut: the scaled balances grow by at least the price, minus the rounded-up amount.
    have hon : onSwap m p s = swapGivenOut m p s := onSwap_givenOut m p s hkind
    rw [hon] at hq
    obtain ⟨hlt, hrne, hfee, hqc⟩ := swapGivenOut_some m p s c hq
    have hr : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
    have hD : 0 < ONE - p.fee := by omega
    have eIn : amountIn s c = c := by unfold amountIn; rw [hkind]
    have eOut : amountOut s c = s.amount := by unfold amountOut; rw [hkind]
    have hbal : ∀ k, mid.balance k
        = update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) k := by
      intro k
      rw [hmid]
      show update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) k = _
      rw [eIn, eOut]
    have hrate : ∀ k, mid.rate k = p.rate k := by
      intro k
      rw [hmid]
    have hn : mid.n = p.n := by rw [hmid]
    have hS := W.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) hne hlt1 hlt2 hlt
    have e1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE
        ≤ downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn :=
      downUp_lower _ _ hr
    have e2 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE
        ≤ c * (ONE - p.fee) := by
      rw [hqc]
      exact downUp_lower _ _ hD
    have eprice : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE
        ≤ c * p.rate s.tokenIn := by
      have g1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE
          ≤ downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn * ONE :=
        Nat.mul_le_mul_right _ e1
      have g2 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn
          ≤ c * (ONE - p.fee) * p.rate s.tokenIn :=
        Nat.mul_le_mul_right _ e2
      have g3 : downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * p.rate s.tokenIn * ONE
          = downUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn := by
        ac_rfl
      have g4 : c * (ONE - p.fee) * p.rate s.tokenIn ≤ c * p.rate s.tokenIn * ONE := by
        have gd : c * (ONE - p.fee) ≤ c * ONE := Nat.mul_le_mul_left _ (Nat.sub_le ONE p.fee)
        have gd2 : c * (ONE - p.fee) * p.rate s.tokenIn ≤ c * ONE * p.rate s.tokenIn :=
          Nat.mul_le_mul_right _ gd
        have eac : c * ONE * p.rate s.tokenIn = c * p.rate s.tokenIn * ONE := by ac_rfl
        omega
      have g5 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE
          ≤ c * p.rate s.tokenIn * ONE := by omega
      exact Nat.le_of_mul_le_mul_right g5 one_pos
    have hpt : ∀ k, k < p.n →
        update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)))
          s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k
        ≤ scaledBalances mid k := by
      intro k hk
      by_cases hki : k = s.tokenIn
      · subst hki
        rw [update2_same]
        have hBB : scaledBalances mid s.tokenIn
            = (p.balance s.tokenIn + c) * p.rate s.tokenIn / ONE := by
          unfold scaledBalances scaleDown
          rw [hbal s.tokenIn, update2_same, hrate s.tokenIn]
        rw [hBB]
        apply (ProofForgeFin.le_div_iff one_pos).2
        have eB : scaledBalances p s.tokenIn * ONE
            ≤ p.balance s.tokenIn * p.rate s.tokenIn :=
          scaleDown_upper _ _
        have t1 : (scaledBalances p s.tokenIn
            + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) * ONE
            = scaledBalances p s.tokenIn * ONE
            + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE :=
          Nat.add_mul _ _ _
        have t2 : (p.balance s.tokenIn + c) * p.rate s.tokenIn
            = p.balance s.tokenIn * p.rate s.tokenIn + c * p.rate s.tokenIn :=
          Nat.add_mul _ _ _
        omega
      · by_cases hkj : k = s.tokenOut
        · subst hkj
          rw [update2_second _ _ _ _ _ (Ne.symm hne)]
          have hBB : scaledBalances mid s.tokenOut
              = (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut / ONE := by
            unfold scaledBalances scaleDown
            rw [hbal s.tokenOut, update2_second _ _ _ _ _ (Ne.symm hne), hrate s.tokenOut]
          rw [hBB]
          apply (ProofForgeFin.le_div_iff one_pos).2
          have eB : scaledBalances p s.tokenOut * ONE
              ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
            scaleDown_upper _ _
          have eX : s.amount * p.rate s.tokenOut
              ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE :=
            scaleUp_lower _ _
          have t1 : (scaledBalances p s.tokenOut
              - scaleUp s.amount (p.rate s.tokenOut)) * ONE
              = scaledBalances p s.tokenOut * ONE
              - scaleUp s.amount (p.rate s.tokenOut) * ONE :=
            Nat.sub_mul _ _ _
          have t2 : (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut
              = p.balance s.tokenOut * p.rate s.tokenOut - s.amount * p.rate s.tokenOut :=
            Nat.sub_mul _ _ _
          omega
        · have hkk : scaledBalances mid k = scaledBalances p k := by
            unfold scaledBalances scaleDown
            rw [hbal k, update2_other _ _ _ _ _ _ hki hkj, hrate k]
          rw [update2_other _ _ _ _ _ _ hki hkj, hkk]
          exact Nat.le_refl _
    have hmono := W.monotone _ _ hpt
    unfold value
    exact Nat.le_trans hS hmono

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' W h
  exact step_value_mono m p s p' W h

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' W hrun
  induction ss generalizing p with
  | nil =>
    simp [run] at hrun
    cases hrun
    exact Nat.le_refl _
  | cons s ss ih =>
    unfold run at hrun
    cases hst : step onSwap m p s
    case none =>
      simp [hst] at hrun
    case some mid =>
      simp [hst] at hrun
      have hn : mid.n = p.n := step_preserves_n m p s mid hst
      have W' : WellBehaved m mid.n := hn ▸ W
      exact Nat.le_trans (step_value_mono m p s mid W hst) (ih mid W' hrun)

end BalancerSwap

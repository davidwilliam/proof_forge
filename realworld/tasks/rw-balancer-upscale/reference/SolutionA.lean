import BalancerSwap.Spec
/-!
Reference solution: the Balancer V2 swap wrapper of the port (`candidate/Solution.lean`) with
the given-out amount upscaled with `mulUp` instead of `mulDown`, and a given-out swap refused
when that amount is not below the pool's scaled balance. Everything else (the fee, the balance
upscaling, `divDown` and `divUp` back to raw units) is Balancer's code unchanged.
-/
namespace BalancerSwap

/-! ## FixedPoint (as deployed) -/

def mulDown (a b : Nat) : Nat := a * b / ONE

def mulUp (a b : Nat) : Nat := if a * b = 0 then 0 else (a * b - 1) / ONE + 1

def divDown (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some (a * ONE / b)

def divUp (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)

def complement (x : Nat) : Nat := if x < ONE then ONE - x else 0

/-! ## Scaling -/

/-- `_upscale`, used for the given-in amount (rounding down favours the pool there). -/
def upscale (amount scalingFactor : Nat) : Nat := mulDown amount scalingFactor

/-- The fix: the given-out amount is upscaled rounding up, `FixedPoint.mulUp`. -/
def upscaleUp (amount scalingFactor : Nat) : Nat := mulUp amount scalingFactor

def downscaleDown (amount scalingFactor : Nat) : Option Nat := divDown amount scalingFactor

def downscaleUp (amount scalingFactor : Nat) : Option Nat := divUp amount scalingFactor

/-! ## BasePool and BaseGeneralPool -/

def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none

def addSwapFeeAmount (amount fee : Nat) : Option Nat := divUp amount (complement fee)

def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  match subtractSwapFeeAmount s.amount p.fee with
  | none => none
  | some a =>
    downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale a (p.rate s.tokenIn)))
      (p.rate s.tokenOut)

/-- `_swapGivenOut` with `upscaleUp` for the amount out. The pool's balances are upscaled as
before (`_upscaleArray`, which is `BalancerSwap.scaledBalances`). -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if scaledBalances p s.tokenOut ≤ upscaleUp s.amount (p.rate s.tokenOut) then none
  else
    match downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none => none
    | some a => addSwapFeeAmount a p.fee

def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

/-! ## Rounding facts -/

theorem one_pos : 0 < ONE := by unfold ONE; omega

theorem mulUp_eq (a b : Nat) : mulUp a b = scaleUp a b := by
  unfold mulUp scaleUp ONE; split <;> omega

theorem scaleUp_ge (a r : Nat) : a * r ≤ scaleUp a r * ONE := by
  unfold scaleUp ONE; omega

theorem scaleUp_lt (a r : Nat) : scaleUp a r * ONE < a * r + ONE := by
  unfold scaleUp ONE; omega

theorem scaleDown_le (a r : Nat) : scaleDown a r * ONE ≤ a * r := by
  unfold scaleDown ONE; omega

theorem scaled_le (p : Pool) (k : Nat) : scaledBalances p k * ONE ≤ p.balance k * p.rate k :=
  scaleDown_le _ _

theorem mulDown_le (a r : Nat) : mulDown a r * ONE ≤ a * r := by
  unfold mulDown ONE; omega

theorem mulUp_ge (a r : Nat) : a * r ≤ mulUp a r * ONE := by
  rw [mulUp_eq]; exact scaleUp_ge a r

theorem mulUp_lt (a r : Nat) : mulUp a r * ONE < a * r + ONE := by
  rw [mulUp_eq]; exact scaleUp_lt a r

theorem divDown_spec {a r q : Nat} (h : divDown a r = some q) :
    0 < r ∧ q * r ≤ a * ONE ∧ a * ONE < (q + 1) * r := by
  unfold divDown at h
  split at h
  · contradiction
  · rename_i hr
    have hr' : 0 < r := Nat.pos_of_ne_zero hr
    split at h
    · cases h; subst_vars; simp; exact hr'
    · cases h
      refine ⟨hr', Nat.div_mul_le_self _ _, ?_⟩
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.lt_div_mul_add hr'

theorem divUp_spec {a r q : Nat} (h : divUp a r = some q) :
    0 < r ∧ a * ONE ≤ q * r ∧ q * r < a * ONE + r := by
  unfold divUp at h
  split at h
  · contradiction
  · rename_i hr
    have hr' : 0 < r := Nat.pos_of_ne_zero hr
    split at h
    · cases h; subst_vars; simp; exact hr'
    · rename_i ha
      cases h
      have hA : 0 < a * ONE := Nat.mul_pos (Nat.pos_of_ne_zero ha) one_pos
      have h1 := Nat.div_mul_le_self (a * ONE - 1) r
      have h2 := Nat.lt_div_mul_add (a := a * ONE - 1) hr'
      refine ⟨hr', ?_, ?_⟩
      · rw [Nat.add_mul, Nat.one_mul]; omega
      · rw [Nat.add_mul, Nat.one_mul]; omega

theorem divUp_some {a r : Nat} (hr : 0 < r) : ∃ q, divUp a r = some q := by
  unfold divUp
  simp only [Nat.pos_iff_ne_zero.mp hr, ite_false]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem divDown_some {a r : Nat} (hr : 0 < r) : ∃ q, divDown a r = some q := by
  unfold divDown
  simp only [Nat.pos_iff_ne_zero.mp hr, ite_false]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem complement_eq {fee : Nat} (h : fee < ONE) : complement fee = ONE - fee := by
  unfold complement; simp [h]

theorem addSwapFeeAmount_spec {a fee c : Nat} (h : addSwapFeeAmount a fee = some c) :
    fee < ONE ∧ a * ONE ≤ c * (ONE - fee) ∧ c * (ONE - fee) < a * ONE + (ONE - fee) := by
  unfold addSwapFeeAmount at h
  have hs := divUp_spec h
  have hf : fee < ONE := by
    unfold complement at hs
    split at hs
    · assumption
    · omega
  rw [complement_eq hf] at hs
  exact ⟨hf, hs.2.1, hs.2.2⟩

theorem subtractSwapFeeAmount_spec {a fee a' : Nat} (h : subtractSwapFeeAmount a fee = some a') :
    a' ≤ a ∧ a' * ONE ≤ a * (ONE - fee) ∧ a * (ONE - fee) - ONE ≤ a' * ONE := by
  unfold subtractSwapFeeAmount at h
  split at h
  · rename_i hle
    cases h
    have h1 := mulUp_ge a fee
    have h2 := mulUp_lt a fee
    refine ⟨Nat.sub_le _ _, ?_, ?_⟩
    · rw [Nat.sub_mul, Nat.mul_sub]
      have : mulUp a fee * ONE ≤ a * ONE := Nat.mul_le_mul_right ONE hle
      omega
    · rw [Nat.sub_mul, Nat.mul_sub]
      have : mulUp a fee * ONE ≤ a * ONE := Nat.mul_le_mul_right ONE hle
      omega
  · contradiction

theorem subtractSwapFeeAmount_some {a fee : Nat} (h : fee < ONE) :
    ∃ a', subtractSwapFeeAmount a fee = some a' := by
  unfold subtractSwapFeeAmount
  have h1 := mulUp_lt a fee
  have h2 : a * fee ≤ a * ONE := Nat.mul_le_mul_left a (Nat.le_of_lt h)
  have : mulUp a fee ≤ a := by
    have : mulUp a fee * ONE < (a + 1) * ONE := by rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right this)
  simp [this]

/-- `x * ONE ≤ A * r` and `A * ONE ≤ B` give `x ≤ B * r / (ONE * ONE)`. -/
theorem le_div_one_one {x A B r : Nat} (h1 : x * ONE ≤ A * r) (h2 : A * ONE ≤ B) :
    x ≤ B * r / (ONE * ONE) := by
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos one_pos one_pos)).2
  have : x * ONE * ONE ≤ A * r * ONE := Nat.mul_le_mul_right ONE h1
  have h3 : A * ONE * r ≤ B * r := Nat.mul_le_mul_right r h2
  calc x * (ONE * ONE) = x * ONE * ONE := by rw [Nat.mul_assoc]
    _ ≤ A * r * ONE := this
    _ = A * ONE * r := by ac_rfl
    _ ≤ B * r := h3

/-- `B ≤ A * ONE` gives `B * r / (ONE * ONE) ≤ A * r / ONE`. -/
theorem div_one_one_le {A B r : Nat} (h : B ≤ A * ONE) : B * r / (ONE * ONE) ≤ A * r / ONE := by
  have : B * r ≤ A * r * ONE := by
    calc B * r ≤ A * ONE * r := Nat.mul_le_mul_right r h
      _ = A * r * ONE := by ac_rfl
  calc B * r / (ONE * ONE) ≤ A * r * ONE / (ONE * ONE) := Nat.div_le_div_right this
    _ = A * r / ONE := by rw [Nat.mul_comm ONE ONE, Nat.mul_div_mul_right _ _ one_pos]

/-! ## Unfolding the implementation -/

theorem givenIn_some {m : PoolMath} {p : Pool} {s : Swap} {y : Nat} (hk : s.kind = .givenIn)
    (h : onSwap m p s = some y) :
    ∃ a', subtractSwapFeeAmount s.amount p.fee = some a' ∧
      divDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (mulDown a' (p.rate s.tokenIn)))
        (p.rate s.tokenOut) = some y := by
  simp only [onSwap, hk] at h
  unfold swapGivenIn upscale downscaleDown at h
  split at h
  · contradiction
  · rename_i a' ha'
    exact ⟨a', ha', h⟩

theorem givenOut_some {m : PoolMath} {p : Pool} {s : Swap} {c : Nat} (hk : s.kind = .givenOut)
    (h : onSwap m p s = some c) :
    ¬ scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) ∧
    ∃ a0, divUp (outPrice m p s) (p.rate s.tokenIn) = some a0 ∧ addSwapFeeAmount a0 p.fee = some c := by
  simp only [onSwap, hk] at h
  unfold swapGivenOut upscaleUp downscaleUp at h
  rw [mulUp_eq] at h
  split at h
  · contradiction
  · rename_i hb
    refine ⟨hb, ?_⟩
    split at h
    · contradiction
    · rename_i a0 ha0
      exact ⟨a0, ha0, h⟩

/-! ## Success -/

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hw hk hv hr hf
  obtain ⟨a', ha'⟩ := subtractSwapFeeAmount_some (a := s.amount) hf
  obtain ⟨y, hy⟩ := divDown_some
    (a := m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (mulDown a' (p.rate s.tokenIn))) hr
  have himpl : onSwap m p s = some y := by
    unfold onSwap; rw [hk]; unfold swapGivenIn; rw [ha']; exact hy
  have ⟨_, hy1, _⟩ := divDown_spec hy
  have hsound := (hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
    (mulDown a' (p.rate s.tokenIn)) hv.1 hv.2.1 hv.2.2).1
  have hb := scaled_le p s.tokenOut
  have hle : y ≤ p.balance s.tokenOut := by
    apply Nat.le_of_mul_le_mul_right _ hr
    have : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (mulDown a' (p.rate s.tokenIn)) * ONE ≤
        scaledBalances p s.tokenOut * ONE := Nat.mul_le_mul_right ONE hsound
    omega
  unfold step
  simp only [hv, ite_true, himpl]
  unfold settle amountOut
  simp [hk, hle]

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hw hk hv hr hf hlt
  have hx : ¬ scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := by
    unfold scaledBalances; omega
  obtain ⟨a0, ha0⟩ := divUp_some (a := outPrice m p s) hr
  have hc : 0 < complement p.fee := by rw [complement_eq hf]; omega
  obtain ⟨c, hcs⟩ := divUp_some (a := a0) hc
  have himpl : onSwap m p s = some c := by
    unfold onSwap; rw [hk]; unfold swapGivenOut upscaleUp downscaleUp; rw [mulUp_eq]
    simp only [hx, ite_false]
    unfold outPrice at ha0
    rw [ha0]; exact hcs
  have hle : s.amount ≤ p.balance s.tokenOut := by
    have h1 := scaleUp_ge s.amount (p.rate s.tokenOut)
    have h2 := scaleDown_le (p.balance s.tokenOut) (p.rate s.tokenOut)
    have h3 : (scaleUp s.amount (p.rate s.tokenOut) + 1) * ONE ≤
        scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) * ONE := Nat.mul_le_mul_right ONE hlt
    rw [Nat.add_mul, Nat.one_mul] at h3
    have : s.amount * p.rate s.tokenOut ≤ p.balance s.tokenOut * p.rate s.tokenOut := by omega
    have hpos : 0 < p.rate s.tokenOut := by
      rcases Nat.eq_zero_or_pos (p.rate s.tokenOut) with h0 | h0
      · unfold scaleDown at hlt; rw [h0, Nat.mul_zero] at hlt; unfold ONE at hlt; omega
      · exact h0
    exact Nat.le_of_mul_le_mul_right this hpos
  unfold step
  simp only [hv, ite_true, himpl]
  unfold settle amountOut
  simp [hk, hle]

/-! ## Prices -/

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hm hk _ h
  obtain ⟨a', ha', hy⟩ := givenIn_some hk h
  have ⟨_, hy1, _⟩ := divDown_spec hy
  have ⟨_, hf1, _⟩ := subtractSwapFeeAmount_spec ha'
  have hx : mulDown a' (p.rate s.tokenIn) ≤ netInDown p s := by
    unfold netInDown
    exact le_div_one_one (mulDown_le a' (p.rate s.tokenIn)) hf1
  have := hm.1 (scaledBalances p) s.tokenIn s.tokenOut _ _ hx
  have := Nat.mul_le_mul_right ONE this
  rw [Nat.mul_comm ONE]
  omega

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hm hk _ h
  obtain ⟨a', ha', hy⟩ := givenIn_some hk h
  have ⟨_, _, hy2⟩ := divDown_spec hy
  have ⟨_, _, hf2⟩ := subtractSwapFeeAmount_spec ha'
  have hx : netInLessOneDown p s ≤ mulDown a' (p.rate s.tokenIn) := by
    unfold netInLessOneDown mulDown
    exact div_one_one_le hf2
  have := hm.1 (scaledBalances p) s.tokenIn s.tokenOut _ _ hx
  have := Nat.mul_le_mul_right ONE this
  rw [Nat.mul_comm ONE]
  omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c _ hk _ h
  obtain ⟨_, a0, ha0, hc⟩ := givenOut_some hk h
  have ⟨_, h1, _⟩ := divUp_spec ha0
  have ⟨_, h2, _⟩ := addSwapFeeAmount_spec hc
  calc ONE * ONE * outPrice m p s = ONE * (outPrice m p s * ONE) := by ac_rfl
    _ ≤ ONE * (a0 * p.rate s.tokenIn) := Nat.mul_le_mul_left ONE h1
    _ = a0 * ONE * p.rate s.tokenIn := by ac_rfl
    _ ≤ c * (ONE - p.fee) * p.rate s.tokenIn := Nat.mul_le_mul_right _ h2

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c _ hk _ h
  obtain ⟨_, a0, ha0, hc⟩ := givenOut_some hk h
  have ⟨hr, _, h1⟩ := divUp_spec ha0
  have ⟨_, _, h2⟩ := addSwapFeeAmount_spec hc
  have h3 : (c - 1) * (ONE - p.fee) ≤ a0 * ONE := by rw [Nat.sub_mul, Nat.one_mul]; omega
  calc (c - 1) * (ONE - p.fee) * p.rate s.tokenIn ≤ a0 * ONE * p.rate s.tokenIn :=
        Nat.mul_le_mul_right _ h3
    _ = ONE * (a0 * p.rate s.tokenIn) := by ac_rfl
    _ < ONE * (ONE * outPrice m p s + p.rate s.tokenIn) := by
        apply Nat.mul_lt_mul_of_pos_left _ one_pos
        rw [Nat.mul_comm ONE]; exact h1

/-! ## Value -/

theorem settle_balance {p p' : Pool} {s : Swap} {c : Nat} (h : settle p s c = some p') :
    amountOut s c ≤ p.balance s.tokenOut ∧ p'.n = p.n ∧ p'.rate = p.rate ∧
    p'.balance = update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
      s.tokenOut (p.balance s.tokenOut - amountOut s c) := by
  unfold settle at h
  split at h
  · rename_i hle; cases h; exact ⟨hle, rfl, rfl, rfl⟩
  · contradiction

theorem step_some {m : PoolMath} {p p' : Pool} {s : Swap} (h : step onSwap m p s = some p') :
    Valid p s ∧ ∃ c, onSwap m p s = some c ∧ settle p s c = some p' := by
  unfold step at h
  split at h
  · rename_i hv
    refine ⟨hv, ?_⟩
    split at h
    · rename_i c hc; exact ⟨c, hc, h⟩
    · contradiction
  · contradiction

/-- The scaled balances after a swap dominate the math's post-trade balances. -/
theorem dominates {p p' : Pool} {s : Swap} {c gain loss : Nat} (_hv : Valid p s)
    (hs : settle p s c = some p')
    (hin : (scaledBalances p s.tokenIn + gain) * ONE ≤
      (p.balance s.tokenIn + amountIn s c) * p.rate s.tokenIn)
    (hout : (scaledBalances p s.tokenOut - loss) * ONE ≤
      (p.balance s.tokenOut - amountOut s c) * p.rate s.tokenOut) :
    ∀ k, k < p.n → update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + gain)
      s.tokenOut (scaledBalances p s.tokenOut - loss) k ≤ scaledBalances p' k := by
  obtain ⟨_, _, hr, hb⟩ := settle_balance hs
  intro k _
  show update2 _ _ _ _ _ k ≤ scaleDown (p'.balance k) (p'.rate k)
  rw [hb, hr]
  unfold update2
  by_cases hki : k = s.tokenIn
  · subst hki
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact (Nat.le_div_iff_mul_le one_pos).2 hin
  · by_cases hkj : k = s.tokenOut
    · subst hkj
      rw [ite_eq_right hki, ite_eq_left rfl, ite_eq_right hki, ite_eq_left rfl]
      exact (Nat.le_div_iff_mul_le one_pos).2 hout
    · rw [ite_eq_right hki, ite_eq_right hkj, ite_eq_right hki, ite_eq_right hkj]
      exact Nat.le_refl _

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hw h
  obtain ⟨hv, c, hc, hs⟩ := step_some h
  obtain ⟨hle, hn, _, _⟩ := settle_balance hs
  have hBi := scaled_le p s.tokenIn
  have hBj := scaled_le p s.tokenOut
  unfold value
  rw [← hn] at hw
  cases hk : s.kind with
  | givenIn =>
    have eIn : amountIn s c = s.amount := by simp [amountIn, hk]
    have eOut : amountOut s c = c := by simp [amountOut, hk]
    obtain ⟨a', ha', hy⟩ := givenIn_some hk hc
    have ⟨_, hy1, _⟩ := divDown_spec hy
    have ⟨ha'le, _, _⟩ := subtractSwapFeeAmount_spec ha'
    have hx := mulDown_le a' (p.rate s.tokenIn)
    generalize mulDown a' (p.rate s.tokenIn) = x at hx hy1
    have hsound := hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x hv.1
      (by rw [hn]; exact hv.2.1) (by rw [hn]; exact hv.2.2)
    generalize m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x = y at hy1 hsound
    have hai : a' * p.rate s.tokenIn ≤ s.amount * p.rate s.tokenIn := Nat.mul_le_mul_right _ ha'le
    rw [eOut] at hle
    have hcb : c * p.rate s.tokenOut ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
      Nat.mul_le_mul_right _ hle
    have hdom := dominates (gain := x) (loss := y) hv hs
      (by rw [eIn, Nat.add_mul, Nat.add_mul]; omega)
      (by rw [eOut, Nat.sub_mul, Nat.sub_mul]; omega)
    exact Nat.le_trans hsound.2 (hw.monotone _ _ (by rw [hn]; exact hdom))
  | givenOut =>
    have eIn : amountIn s c = c := by simp [amountIn, hk]
    have eOut : amountOut s c = s.amount := by simp [amountOut, hk]
    obtain ⟨hb, a0, ha0, hcs⟩ := givenOut_some hk hc
    have ⟨_, h1, _⟩ := divUp_spec ha0
    have ⟨_, h2, _⟩ := addSwapFeeAmount_spec hcs
    have hxb : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := Nat.lt_of_not_le hb
    have hsound := hw.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut _ hv.1
      (by rw [hn]; exact hv.2.1) (by rw [hn]; exact hv.2.2) hxb
    have hca : a0 ≤ c := by
      apply Nat.le_of_mul_le_mul_right _ one_pos
      have : c * (ONE - p.fee) ≤ c * ONE := Nat.mul_le_mul_left c (Nat.sub_le _ _)
      omega
    have hcr : a0 * p.rate s.tokenIn ≤ c * p.rate s.tokenIn := Nat.mul_le_mul_right _ hca
    have hxo := scaleUp_ge s.amount (p.rate s.tokenOut)
    rw [eOut] at hle
    have hab : s.amount * p.rate s.tokenOut ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
      Nat.mul_le_mul_right _ hle
    unfold outPrice at h1
    have hdom := dominates (gain := m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut))) (loss := scaleUp s.amount (p.rate s.tokenOut)) hv hs
      (by rw [eIn, Nat.add_mul, Nat.add_mul]; omega)
      (by rw [eOut, Nat.sub_mul, Nat.sub_mul]; omega)
    exact Nat.le_trans hsound (hw.monotone _ _ (by rw [hn]; exact hdom))

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss
  induction ss generalizing p with
  | nil => intro p' _ h; cases h; exact Nat.le_refl _
  | cons s ss ih =>
    intro p' hw h
    unfold run at h
    split at h
    · rename_i p1 h1
      obtain ⟨_, c, _, hs⟩ := step_some h1
      obtain ⟨_, hn, _, _⟩ := settle_balance hs
      have hw1 : WellBehaved m p1.n := by rw [hn]; exact hw
      exact Nat.le_trans (req_swap_keeps_value m p s p1 hw h1) (ih p1 p' hw1 h)
    · contradiction

end BalancerSwap

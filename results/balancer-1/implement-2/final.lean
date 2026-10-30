import BalancerSwap.Spec
namespace BalancerSwap
def cdiv (a b : Nat) : Nat := (a + b - 1) / b
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn =>
    if p.rate s.tokenOut = 0 then none
    else some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)
  | .givenOut =>
    if p.rate s.tokenIn = 0 then none
    else if ONE ≤ p.fee then none
    else if scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) then some (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee))
    else none
theorem onePos : 0 < ONE := by unfold ONE; omega
theorem ceilGe (X D : Nat) (hD : 0 < D) : X ≤ (X + D - 1) / D * D := by
  by_cases hX : X = 0
  case pos => simp [hX]
  case neg =>
    have hp : 0 < X := Nat.pos_of_ne_zero hX
    have hE := Nat.div_add_mod (X + D - 1) D
    have hm : (X + D - 1) % D < D := Nat.mod_lt _ hD
    have hc : D * ((X + D - 1) / D) = (X + D - 1) / D * D := Nat.mul_comm _ _
    omega
theorem cdiv_ge (X D : Nat) (hD : 0 < D) : X ≤ cdiv X D * D := by unfold cdiv; exact ceilGe X D hD
theorem chainLE (P R F rate c : Nat) (h1 : P * ONE ≤ R * rate) (h2 : R * ONE ≤ c * F) : ONE * ONE * P ≤ c * F * rate := by
  have a : P * ONE * ONE ≤ R * rate * ONE := Nat.mul_le_mul h1 (Nat.le_refl ONE)
  have e1 : R * rate * ONE = R * ONE * rate := by ac_rfl
  rw [e1] at a
  have b : R * ONE * rate ≤ c * F * rate := Nat.mul_le_mul h2 (Nat.le_refl rate)
  have ch : P * ONE * ONE ≤ c * F * rate := Nat.le_trans a b
  have e2 : ONE * ONE * P = P * ONE * ONE := by ac_rfl
  rw [e2]; exact ch
theorem predLt (A F : Nat) (hF : 0 < F) (hA : 0 < A) : ((A + F - 1) / F - 1) * F < A := by
  have hle : (A + F - 1) / F * F ≤ A + F - 1 := Nat.div_mul_le_self _ _
  have he : ((A + F - 1) / F - 1) * F = (A + F - 1) / F * F - F := by rw [Nat.sub_mul, Nat.one_mul]
  omega
theorem cdiv_pred_lt (A F : Nat) (hF : 0 < F) (hA : 0 < A) : (cdiv A F - 1) * F < A := by unfold cdiv; exact predLt A F hF hA
theorem amtLe (a b r : Nat) (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  by_cases hba : b ≤ a
  case pos =>
    by_cases heq : b = a
    case pos => omega
    case neg =>
      have hlt : b < a := Nat.lt_of_le_of_ne hba heq
      have hBR : b * r ≤ a * r := Nat.mul_le_mul (Nat.le_of_lt hlt) (Nat.le_refl r)
      have h1 : b * r / ONE ≤ a * r / ONE := Nat.div_le_div_right hBR
      have h2 : a * r / ONE ≤ (a * r + (ONE - 1)) / ONE := Nat.div_le_div_right (Nat.le_add_right _ _)
      have hle2 : scaleDown b r ≤ scaleUp a r := by unfold scaleDown scaleUp; exact Nat.le_trans h1 h2
      have hc : scaleDown b r < scaleDown b r := Nat.lt_of_le_of_lt hle2 h
      exact False.elim (Nat.lt_irrefl _ hc)
  case neg => omega
theorem stepN (m : PoolMath) (p mid : Pool) (s : Swap) (h : step onSwap m p s = some mid) : mid.n = p.n := by
  unfold step at h
  by_cases hV : Valid p s
  case pos =>
    rw [if_pos hV] at h
    cases hImpl : onSwap m p s with
    | none => rw [hImpl] at h; contradiction
    | some c =>
      rw [hImpl] at h
      simp only at h
      unfold settle at h
      by_cases hC : amountOut s c ≤ p.balance s.tokenOut
      case pos => rw [if_pos hC] at h; cases h; rfl
      case neg => rw [if_neg hC] at h; contradiction
  case neg => rw [if_neg hV] at h; contradiction

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hW hk hV hR hF
  have hNe : p.rate s.tokenOut ≠ 0 := Nat.ne_of_gt hR
  have hOn : onSwap m p s = some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by unfold onSwap; simp [hk, hNe]
  have hS := hW.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hV.1 hV.2.1 hV.2.2
  have hle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤ p.balance s.tokenOut * p.rate s.tokenOut / ONE := hS.left
  have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤ (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE := Nat.mul_le_mul hle (Nat.le_refl ONE)
  have h2 : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := Nat.div_mul_le_self _ _
  have h3 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := Nat.le_trans h1 h2
  have h4 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut ≤ (p.balance s.tokenOut * p.rate s.tokenOut) / p.rate s.tokenOut := Nat.div_le_div_right h3
  have h5 : (p.balance s.tokenOut * p.rate s.tokenOut) / p.rate s.tokenOut = p.balance s.tokenOut := Nat.mul_div_cancel _ hR
  rw [h5] at h4
  have hSt : step onSwap m p s = settle p s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by unfold step; simp [hV, hOn]
  rw [hSt]
  have hA : amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := by unfold amountOut; simp [hk]
  have hc : amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) ≤ p.balance s.tokenOut := by rw [hA]; exact h4
  unfold settle; simp [hc]

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hW hk hV hRI hF hLt
  have hRn : p.rate s.tokenIn ≠ 0 := Nat.ne_of_gt hRI
  have hFn : ¬ ONE ≤ p.fee := by omega
  have hAL : s.amount ≤ p.balance s.tokenOut := amtLe _ _ _ hLt
  have hOn : onSwap m p s = some (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) := by unfold onSwap; simp [hk, hRn, hFn, hLt]
  obtain ⟨c, hc⟩ : ∃ c, onSwap m p s = some c := ⟨_, hOn⟩
  have hSt : step onSwap m p s = settle p s c := by unfold step; simp [hV, hc]
  rw [hSt]
  have hO : amountOut s c = s.amount := by unfold amountOut; simp [hk]
  have hc2 : amountOut s c ≤ p.balance s.tokenOut := by rw [hO]; exact hAL
  unfold settle; simp [hc2]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hPM hk hV hS
  have hNe : p.rate s.tokenOut ≠ 0 := by
    intro hR
    have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hR]
    rw [hEq] at hS; contradiction
  have hOn : onSwap m p s = some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by unfold onSwap; simp [hk, hNe]
  have hEq : y = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := Option.some_inj.mp (hS.symm.trans hOn)
  rw [hEq]
  have h := Nat.div_mul_le_self (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) (p.rate s.tokenOut)
  calc m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := h
    _ = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := Nat.mul_comm _ _

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hPM hk hV hS
  have hNe : p.rate s.tokenOut ≠ 0 := by
    intro hR
    have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hR]
    rw [hEq] at hS; contradiction
  have hOn : onSwap m p s = some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by unfold onSwap; simp [hk, hNe]
  have hEq : y = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := Option.some_inj.mp (hS.symm.trans hOn)
  rw [hEq]
  have hr : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hNe
  have hLN : netInLessOneDown p s ≤ netInDown p s := by unfold netInLessOneDown netInDown; apply Nat.div_le_div_right; apply Nat.mul_le_mul; exact Nat.sub_le _ _; exact Nat.le_refl _
  have hOL : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := hPM.1 _ _ _ _ _ hLN
  have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) * ONE ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.mul_le_mul hOL (Nat.le_refl ONE)
  have hM : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by rw [Nat.mul_comm ONE _]; exact h1
  have hmod : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) % p.rate s.tokenOut < p.rate s.tokenOut := Nat.mod_lt _ hr
  have hE := Nat.div_add_mod (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) (p.rate s.tokenOut)
  have hE2 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut + (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) % p.rate s.tokenOut = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
    have h : p.rate s.tokenOut * (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) + (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) % p.rate s.tokenOut = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := hE
    rwa [Nat.mul_comm (p.rate s.tokenOut) _] at h
  have hRw : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1) * p.rate s.tokenOut = (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut + p.rate s.tokenOut := by rw [Nat.add_mul, Nat.one_mul]
  have hAlt : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE < (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1) * p.rate s.tokenOut := by
    rw [hRw]
    have hlt : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut + (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) % p.rate s.tokenOut < (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut + p.rate s.tokenOut := Nat.add_lt_add_left hmod _
    rwa [hE2] at hlt
  calc ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := hM
    _ < (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1) * p.rate s.tokenOut := hAlt

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hPM hk hV hS
  have hRn : p.rate s.tokenIn ≠ 0 := by
    intro hR
    have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hR]
    rw [hEq] at hS; contradiction
  have hFn : ¬ ONE ≤ p.fee := by
    intro hF
    have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hRn, hF]
    rw [hEq] at hS; contradiction
  have hLt : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := by
    by_cases hL : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
    case pos => exact hL
    case neg =>
      have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hRn, hFn, hL]
      rw [hEq] at hS; contradiction
  have hOn : onSwap m p s = some (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) := by unfold onSwap; simp [hk, hRn, hFn, hLt]
  have hEc : c = cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) := Option.some_inj.mp (hS.symm.trans hOn)
  rw [hEc]
  have hr : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hRn
  have hF : 0 < ONE - p.fee := by omega
  have g1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤ cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn := cdiv_ge _ _ hr
  have g2 : cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE ≤ cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * (ONE - p.fee) := cdiv_ge _ _ hF
  have hC := chainLE _ _ _ _ _ g1 g2
  have ho : outPrice m p s = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := rfl
  rw [ho]; exact hC

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c hPM hk hV hS
  have hRn : p.rate s.tokenIn ≠ 0 := by
    intro hR
    have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hR]
    rw [hEq] at hS; contradiction
  have hFn : ¬ ONE ≤ p.fee := by
    intro hF
    have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hRn, hF]
    rw [hEq] at hS; contradiction
  have hLt : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := by
    by_cases hL : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
    case pos => exact hL
    case neg =>
      have hEq : onSwap m p s = none := by unfold onSwap; simp [hk, hRn, hFn, hL]
      rw [hEq] at hS; contradiction
  have hOn : onSwap m p s = some (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) := by unfold onSwap; simp [hk, hRn, hFn, hLt]
  have hE : c = cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) := Option.some_inj.mp (hS.symm.trans hOn)
  have ho : outPrice m p s = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := rfl
  rw [ho]
  have hO : 0 < ONE := onePos
  have hr : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hRn
  have hF : 0 < ONE - p.fee := by omega
  rw [hE]
  by_cases hR0 : cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) = 0
  case pos =>
    have hc0 : cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) = 0 := by
      have hzz : cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE = 0 := by rw [hR0, Nat.zero_mul]
      rw [hzz]
      unfold cdiv
      apply Nat.div_eq_of_lt
      omega
    rw [hc0]; simp
    exact Nat.mul_pos hO (by omega : 0 < ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn)
  case neg =>
    have hRp : 0 < cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) := Nat.pos_of_ne_zero hR0
    have hAp : 0 < cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE := Nat.mul_pos hRp hO
    have hcl : (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) - 1) * (ONE - p.fee) < cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE := cdiv_pred_lt _ _ hF hAp
    have h1 : ((cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) - 1) * (ONE - p.fee)) * p.rate s.tokenIn < (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) * p.rate s.tokenIn := Nat.mul_lt_mul_of_pos_right hcl hr
    have hub : cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn ≤ m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1 := by
      unfold cdiv
      exact Nat.div_mul_le_self _ _
    have hRr : cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn < m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn := by omega
    have h2 : (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn) * ONE < (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE := Nat.mul_lt_mul_of_pos_right hRr hO
    have e1 : ((cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE)) * p.rate s.tokenIn = ((cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn)) * ONE := by ac_rfl
    have e2 : ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE := by ac_rfl
    rw [e1] at h1; rw [e2]; exact Nat.lt_trans h1 h2

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hW hStep
  unfold step at hStep
  by_cases hV : Valid p s
  case pos =>
    simp only [if_pos hV] at hStep
    cases hQ : onSwap m p s with
    | none => simp [hQ] at hStep
    | some q =>
      simp only [hQ] at hStep
      have hSet : settle p s q = some p' := hStep
      unfold settle at hSet
      by_cases hC : amountOut s q ≤ p.balance s.tokenOut
      case pos =>
        simp only [if_pos hC] at hSet
        obtain rfl := Option.some_inj.mp hSet
        cases hkind : s.kind with
        | givenIn =>
          have hNe : p.rate s.tokenOut ≠ 0 := by
            intro hR
            have hEq : onSwap m p s = none := by unfold onSwap; simp [hkind, hR]
            rw [hQ] at hEq; contradiction
          have hOn : onSwap m p s = some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by unfold onSwap; simp [hkind, hNe]
          have hqq : q = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := Option.some_inj.mp (hQ.symm.trans hOn)
          subst hqq
          have hYO : amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := by unfold amountOut; simp [hkind]
          have hAI : amountIn s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) = s.amount := by unfold amountIn; simp [hkind]
          rw [hYO] at hC
          have hSnd := hW.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hV.1 hV.2.1 hV.2.2
          have hInv : m.invariant (scaledBalances p) ≤ m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))) := hSnd.right
          have hMono : m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))) ≤ m.invariant (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut), rate := p.rate, fee := p.fee }) := by
            apply hW.monotone
            intro k hkn
            by_cases eI : k = s.tokenIn
            case pos =>
              subst eI
              have u1 : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) s.tokenIn = (scaledBalances p) s.tokenIn + netInDown p s := by unfold update2; simp
              have u2 : (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut), rate := p.rate, fee := p.fee }) s.tokenIn = (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE := by unfold scaledBalances scaleDown update2; simp
              rw [u1, u2]
              have hb : (scaledBalances p) s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
              rw [hb]
              have hXb : netInDown p s * (ONE * ONE) ≤ s.amount * (ONE - p.fee) * p.rate s.tokenIn := Nat.div_mul_le_self _ _
              have hFle : (ONE - p.fee) ≤ ONE := Nat.sub_le _ _
              have hNle : s.amount * (ONE - p.fee) * p.rate s.tokenIn ≤ s.amount * p.rate s.tokenIn * ONE := by
                have t : s.amount * (ONE - p.fee) ≤ s.amount * ONE := Nat.mul_le_mul (Nat.le_refl s.amount) hFle
                have t2 : s.amount * (ONE - p.fee) * p.rate s.tokenIn ≤ s.amount * ONE * p.rate s.tokenIn := Nat.mul_le_mul t (Nat.le_refl _)
                have e : s.amount * ONE * p.rate s.tokenIn = s.amount * p.rate s.tokenIn * ONE := by ac_rfl
                rw [e] at t2; exact t2
              have hXb2 : netInDown p s * (ONE * ONE) ≤ s.amount * p.rate s.tokenIn * ONE := Nat.le_trans hXb hNle
              have eX : netInDown p s * (ONE * ONE) = netInDown p s * ONE * ONE := by ac_rfl
              rw [eX] at hXb2
              have hXO : netInDown p s * ONE ≤ s.amount * p.rate s.tokenIn := Nat.le_of_mul_le_mul_right hXb2 onePos
              have hbi2 : (p.balance s.tokenIn * p.rate s.tokenIn / ONE) * ONE ≤ p.balance s.tokenIn * p.rate s.tokenIn := Nat.div_mul_le_self _ _
              have hsum : (p.balance s.tokenIn * p.rate s.tokenIn / ONE + netInDown p s) * ONE ≤ (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn := by
                have e : (p.balance s.tokenIn * p.rate s.tokenIn / ONE + netInDown p s) * ONE = (p.balance s.tokenIn * p.rate s.tokenIn / ONE) * ONE + netInDown p s * ONE := Nat.add_mul _ _ _
                rw [e]
                have e2 : (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn + s.amount * p.rate s.tokenIn := Nat.add_mul _ _ _
                rw [e2]; exact Nat.add_le_add hbi2 hXO
              exact (Nat.le_div_iff_mul_le onePos).mpr hsum
            case neg =>
              by_cases eJ : k = s.tokenOut
              case pos =>
                subst eJ
                have hjj : s.tokenOut ≠ s.tokenIn := fun he => hV.1 he.symm
                have u1 : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) s.tokenOut = (scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by unfold update2; simp [eI, hjj]
                have u2 : (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut), rate := p.rate, fee := p.fee }) s.tokenOut = (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut / ONE := by unfold scaledBalances scaleDown update2; simp [hjj]
                rw [u1, u2]
                have hbj : (scaledBalances p) s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
                rw [hbj]
                have hyr : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.div_mul_le_self _ _
                have h1 : ((p.balance s.tokenOut * p.rate s.tokenOut / ONE) - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) * ONE ≤ (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut := by
                  have a1 : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := Nat.div_mul_le_self _ _
                  have e : ((p.balance s.tokenOut * p.rate s.tokenOut / ONE) - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) * ONE = (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.sub_mul _ _ _
                  rw [e]
                  have e2 : (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut - (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut := Nat.sub_mul _ _ _
                  rw [e2]; omega
                exact (Nat.le_div_iff_mul_le onePos).mpr h1
              case neg =>
                have u1 : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k = (scaledBalances p) k := by unfold update2; simp [eI, eJ]
                have u2 : (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut), rate := p.rate, fee := p.fee }) k = (scaledBalances p) k := by unfold scaledBalances scaleDown update2; simp [eI, eJ]
                rw [u1, u2]; exact Nat.le_refl _
          show value m p ≤ value m { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)) s.tokenOut (p.balance s.tokenOut - amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)), rate := p.rate, fee := p.fee }
          simp only [hAI, hYO]
          show m.invariant (scaledBalances p) ≤ m.invariant (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut), rate := p.rate, fee := p.fee })
          exact Nat.le_trans hInv hMono
        | givenOut =>
          have hRn : p.rate s.tokenIn ≠ 0 := by
            intro hR
            have hEq : onSwap m p s = none := by unfold onSwap; simp [hkind, hR]
            rw [hQ] at hEq; contradiction
          have hFn : ¬ ONE ≤ p.fee := by
            intro hF
            have hEq : onSwap m p s = none := by unfold onSwap; simp [hkind, hRn, hF]
            rw [hQ] at hEq; contradiction
          have hLt : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := by
            by_cases hL : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
            case pos => exact hL
            case neg =>
              have hEq : onSwap m p s = none := by unfold onSwap; simp [hkind, hRn, hFn, hL]
              rw [hQ] at hEq; contradiction
          have hOn : onSwap m p s = some (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) := by unfold onSwap; simp [hkind, hRn, hFn, hLt]
          have hqq : q = cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) := Option.some_inj.mp (hQ.symm.trans hOn)
          subst hqq
          have hAo : amountOut s (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) = s.amount := by unfold amountOut; simp [hkind]
          have hAi : amountIn s (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) = cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) := by unfold amountIn; simp [hkind]
          have hLt2 : scaleUp s.amount (p.rate s.tokenOut) < (scaledBalances p) s.tokenOut := hLt
          have hInv : m.invariant (scaledBalances p) ≤ m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))) := hW.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) hV.1 hV.2.1 hV.2.2 hLt2
          have hMono : m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))) ≤ m.invariant (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) s.tokenOut (p.balance s.tokenOut - s.amount), rate := p.rate, fee := p.fee }) := by
            apply hW.monotone
            intro k hkn
            by_cases eI : k = s.tokenIn
            case pos =>
              subst eI
              have u1 : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn = (scaledBalances p) s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := by unfold update2; simp
              have u2 : (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) s.tokenOut (p.balance s.tokenOut - s.amount), rate := p.rate, fee := p.fee }) s.tokenIn = (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) * p.rate s.tokenIn / ONE := by unfold scaledBalances scaleDown update2; simp
              rw [u1, u2]
              have hb : (scaledBalances p) s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
              rw [hb]
              have hr : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hRn
              have hF : 0 < ONE - p.fee := by omega
              have g1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤ cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn := cdiv_ge _ _ hr
              have g2 : cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE ≤ cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * (ONE - p.fee) := cdiv_ge _ _ hF
              have hch := chainLE _ _ _ _ _ g1 g2
              have hFle : (ONE - p.fee) ≤ ONE := Nat.sub_le _ _
              have h1 : cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * (ONE - p.fee) * p.rate s.tokenIn ≤ cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * p.rate s.tokenIn * ONE := by
                have t : cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * (ONE - p.fee) ≤ cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * ONE := Nat.mul_le_mul (Nat.le_refl _) hFle
                have t2 : cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * (ONE - p.fee) * p.rate s.tokenIn ≤ cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * ONE * p.rate s.tokenIn := Nat.mul_le_mul t (Nat.le_refl _)
                have e : cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * ONE * p.rate s.tokenIn = cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * p.rate s.tokenIn * ONE := by ac_rfl
                rw [e] at t2; exact t2
              have hch2 : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * p.rate s.tokenIn * ONE := Nat.le_trans hch h1
              have e3 : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE := by ac_rfl
              rw [e3] at hch2
              have hprice : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤ cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * p.rate s.tokenIn := Nat.le_of_mul_le_mul_right hch2 onePos
              have hbi2 : (p.balance s.tokenIn * p.rate s.tokenIn / ONE) * ONE ≤ p.balance s.tokenIn * p.rate s.tokenIn := Nat.div_mul_le_self _ _
              have hsum : (p.balance s.tokenIn * p.rate s.tokenIn / ONE + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) * ONE ≤ (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) * p.rate s.tokenIn := by
                have e : (p.balance s.tokenIn * p.rate s.tokenIn / ONE + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) * ONE = (p.balance s.tokenIn * p.rate s.tokenIn / ONE) * ONE + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE := Nat.add_mul _ _ _
                rw [e]
                have e2 : (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) * p.rate s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * p.rate s.tokenIn := Nat.add_mul _ _ _
                rw [e2]; exact Nat.add_le_add hbi2 hprice
              exact (Nat.le_div_iff_mul_le onePos).mpr hsum
            case neg =>
              by_cases eJ : k = s.tokenOut
              case pos =>
                subst eJ
                have hjj : s.tokenOut ≠ s.tokenIn := fun he => hV.1 he.symm
                have u1 : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut = (scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by unfold update2; simp [eI, hjj]
                have u2 : (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) s.tokenOut (p.balance s.tokenOut - s.amount), rate := p.rate, fee := p.fee }) s.tokenOut = (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut / ONE := by unfold scaledBalances scaleDown update2; simp [hjj]
                rw [u1, u2]
                have hbj : (scaledBalances p) s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
                rw [hbj]
                have hau : s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE := by
                  have h := ceilGe (s.amount * p.rate s.tokenOut) ONE onePos
                  have heq : s.amount * p.rate s.tokenOut + (ONE - 1) = s.amount * p.rate s.tokenOut + ONE - 1 := by have : 1 ≤ ONE := onePos; omega
                  unfold scaleUp
                  rw [heq]
                  exact h
                have h1 : ((p.balance s.tokenOut * p.rate s.tokenOut / ONE) - scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤ (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut := by
                  have a1 : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := Nat.div_mul_le_self _ _
                  have e : ((p.balance s.tokenOut * p.rate s.tokenOut / ONE) - scaleUp s.amount (p.rate s.tokenOut)) * ONE = (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE - scaleUp s.amount (p.rate s.tokenOut) * ONE := Nat.sub_mul _ _ _
                  rw [e]
                  have e2 : (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut - s.amount * p.rate s.tokenOut := Nat.sub_mul _ _ _
                  rw [e2]; omega
                exact (Nat.le_div_iff_mul_le onePos).mpr h1
              case neg =>
                have u1 : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k = (scaledBalances p) k := by unfold update2; simp [eI, eJ]
                have u2 : (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) s.tokenOut (p.balance s.tokenOut - s.amount), rate := p.rate, fee := p.fee }) k = (scaledBalances p) k := by unfold scaledBalances scaleDown update2; simp [eI, eJ]
                rw [u1, u2]; exact Nat.le_refl _
          show value m p ≤ value m { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee))) s.tokenOut (p.balance s.tokenOut - amountOut s (cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee))), rate := p.rate, fee := p.fee }
          simp only [hAi, hAo]
          show m.invariant (scaledBalances p) ≤ m.invariant (scaledBalances { n := p.n, balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + cdiv (cdiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) s.tokenOut (p.balance s.tokenOut - s.amount), rate := p.rate, fee := p.fee })
          exact Nat.le_trans hInv hMono
      case neg =>
        simp only [if_neg hC] at hSet; contradiction
  case neg =>
    simp only [if_neg hV] at hStep; contradiction

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' hW hRun
  induction ss generalizing p p' with
  | nil => simp [run] at hRun; subst hRun; exact Nat.le_refl _
  | cons s ss ih =>
    have hUnf : run onSwap m p (s :: ss) = match step onSwap m p s with | some p1 => run onSwap m p1 ss | none => none := by rfl
    rw [hUnf] at hRun
    cases hStep : step onSwap m p s with
    | none => rw [hStep] at hRun; contradiction
    | some mid =>
      rw [hStep] at hRun; simp at hRun
      have hLe1 : value m p ≤ value m mid := req_swap_keeps_value m p s mid hW hStep
      have heq : mid.n = p.n := stepN m p mid s hStep
      have hWmid : WellBehaved m mid.n := heq.symm ▸ hW
      have hLe2 : value m mid ≤ value m p' := ih mid p' hWmid hRun
      exact Nat.le_trans hLe1 hLe2

end BalancerSwap

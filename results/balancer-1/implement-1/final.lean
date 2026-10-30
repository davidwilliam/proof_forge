import BalancerSwap.Spec

namespace BalancerSwap

def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn =>
    if p.rate s.tokenOut = 0 then none
    else some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)
  | .givenOut =>
    if p.rate s.tokenIn = 0 then none
    else if ONE ≤ p.fee then none
    else if scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) then
      some (((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn * ONE + (ONE - p.fee) - 1) / (ONE - p.fee))
    else none

theorem aux_ceil_le (N d : Nat) (hd : 0 < d) : N ≤ ((N + d - 1) / d) * d := by
  have hM : d * ((N + d - 1) / d) + (N + d - 1) % d = N + d - 1 := Nat.div_add_mod _ _
  have hmod : (N + d - 1) % d < d := Nat.mod_lt _ hd
  have hcomm : ((N + d - 1) / d) * d = d * ((N + d - 1) / d) := Nat.mul_comm _ _
  omega

theorem aux_chain (Z A c r f : Nat) (h1 : Z * ONE ≤ A * r) (h2 : A * ONE ≤ c * f) :
    ONE * ONE * Z ≤ c * f * r := by
  have s1 : (Z * ONE) * ONE ≤ (A * r) * ONE := Nat.mul_le_mul_right ONE h1
  have e1 : (A * r) * ONE = (A * ONE) * r := by ac_rfl
  have s2 : (A * ONE) * r ≤ (c * f) * r := Nat.mul_le_mul_right r h2
  have e0 : ONE * ONE * Z = (Z * ONE) * ONE := by ac_rfl
  calc ONE * ONE * Z = (Z * ONE) * ONE := e0
    _ ≤ (A * r) * ONE := s1
    _ = (A * ONE) * r := e1
    _ ≤ (c * f) * r := s2
    _ = c * f * r := rfl

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hW hkind hV hR hfee
  have hRne : p.rate s.tokenOut ≠ 0 := Nat.ne_of_gt hR
  have hOn : onSwap m p s = some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by
    unfold onSwap
    rw [hkind]
    simp [hRne]
  have hsound := hW.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hV.1 hV.2.1 hV.2.2
  obtain ⟨hle, _⟩ := hsound
  have hsb : scaledBalances p s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
  rw [hsb] at hle
  have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
    calc m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
        ≤ (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE := Nat.mul_le_mul_right ONE hle
      _ ≤ p.balance s.tokenOut * p.rate s.tokenOut := Nat.div_mul_le_self _ _
  have hle2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut ≤ p.balance s.tokenOut := by
    calc m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut
        ≤ p.balance s.tokenOut * p.rate s.tokenOut / p.rate s.tokenOut := Nat.div_le_div_right h1
      _ = p.balance s.tokenOut := Nat.mul_div_cancel _ hR
  have hAO : amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := by
    simp [amountOut, hkind]
  have hstep : step onSwap m p s = settle p s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by
    unfold step
    simp [hV, hOn]
  rw [hstep]
  unfold settle
  simp [hAO, hle2]

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hW hkind hV hR hfee hlt
  have hRne : p.rate s.tokenIn ≠ 0 := Nat.ne_of_gt hR
  have hfee2 : ¬ (ONE ≤ p.fee) := by omega
  have hEq : onSwap m p s = some (((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn * ONE + (ONE - p.fee) - 1) / (ONE - p.fee)) := by
    unfold onSwap
    rw [hkind]
    simp [hRne, hfee2, hlt]
  have hle_settle : s.amount ≤ p.balance s.tokenOut := by
    by_cases h : s.amount ≤ p.balance s.tokenOut
    · exact h
    · have hgt : p.balance s.tokenOut < s.amount := by omega
      have hmul_le : p.balance s.tokenOut * p.rate s.tokenOut ≤ s.amount * p.rate s.tokenOut :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hgt)
      have hle1 : p.balance s.tokenOut * p.rate s.tokenOut ≤ s.amount * p.rate s.tokenOut + (ONE - 1) :=
        Nat.le_trans hmul_le (Nat.le_add_right _ _)
      have hdiv_le : scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) ≤ scaleUp s.amount (p.rate s.tokenOut) := by
        unfold scaleDown scaleUp
        exact Nat.div_le_div_right hle1
      omega
  have hAO : amountOut s (((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn * ONE + (ONE - p.fee) - 1) / (ONE - p.fee)) = s.amount := by
    simp [amountOut, hkind]
  have hstep : step onSwap m p s = settle p s (((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn * ONE + (ONE - p.fee) - 1) / (ONE - p.fee)) := by
    unfold step
    simp [hV, hEq]
  rw [hstep]
  unfold settle
  simp [hAO, hle_settle]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y _ hkind hV hOn
  have h : onSwap m p s = (if p.rate s.tokenOut = 0 then (none : Option Nat) else some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)) := by
    unfold onSwap
    rw [hkind]
  rw [h] at hOn
  by_cases hR : p.rate s.tokenOut = 0
  · rw [if_pos hR] at hOn
    cases hOn
  · rw [if_neg hR] at hOn
    cases hOn
    calc (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) * p.rate s.tokenOut
        ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.div_mul_le_self _ _
      _ = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := Nat.mul_comm _ _

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hMono hkind hV hOn
  have h : onSwap m p s = (if p.rate s.tokenOut = 0 then (none : Option Nat) else some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)) := by
    unfold onSwap
    rw [hkind]
  rw [h] at hOn
  by_cases hR : p.rate s.tokenOut = 0
  · rw [if_pos hR] at hOn
    cases hOn
  · rw [if_neg hR] at hOn
    cases hOn
    have hle_net : netInLessOneDown p s ≤ netInDown p s := by
      unfold netInLessOneDown netInDown
      apply Nat.div_le_div_right
      apply Nat.mul_le_mul_right
      exact Nat.sub_le _ _
    have hYle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
        ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
      hMono.1 _ _ _ _ _ hle_net
    have hRpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hR
    have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) * ONE
        ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
      Nat.mul_le_mul_right ONE hYle
    have h2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
        < (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1) * p.rate s.tokenOut := by
      have hA := Nat.div_add_mod (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) (p.rate s.tokenOut)
      have hB := Nat.mod_lt (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) hRpos
      have hC : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1) * p.rate s.tokenOut
        = p.rate s.tokenOut * (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) + p.rate s.tokenOut := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      omega
    have heq : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
        = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) * ONE :=
      Nat.mul_comm _ _
    rw [heq]
    exact Nat.lt_of_le_of_lt h1 h2

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c _ hkind hV hOn
  have h : onSwap m p s = (if p.rate s.tokenIn = 0 then (none : Option Nat) else if ONE ≤ p.fee then none else if scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) then some (((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn * ONE + (ONE - p.fee) - 1) / (ONE - p.fee)) else none) := by
    unfold onSwap
    rw [hkind]
  rw [h] at hOn
  by_cases hR : p.rate s.tokenIn = 0
  · rw [if_pos hR] at hOn
    cases hOn
  · rw [if_neg hR] at hOn
    by_cases hfee : ONE ≤ p.fee
    · rw [if_pos hfee] at hOn
      cases hOn
    · rw [if_neg hfee] at hOn
      by_cases hx : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
      · rw [if_pos hx] at hOn
        cases hOn
        unfold outPrice
        have hRpos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hR
        have hfee_lt : p.fee < ONE := by omega
        have hFpos : 0 < ONE - p.fee := Nat.sub_pos_of_lt hfee_lt
        have h1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤ ((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn) * p.rate s.tokenIn :=
          aux_ceil_le _ _ hRpos
        have h2 : ((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn) * ONE ≤ ((((m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn - 1) / p.rate s.tokenIn) * ONE + (ONE - p.fee) - 1) / (ONE - p.fee)) * (ONE - p.fee) :=
          aux_ceil_le _ _ hFpos
        exact aux_chain _ _ _ _ _ h1 h2
      · rw [if_neg hx] at hOn
        cases hOn

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := sorry

theorem req_swap_keeps_value : SwapKeepsValue onSwap := sorry

theorem req_batch_keeps_value : BatchKeepsValue onSwap := sorry

end BalancerSwap

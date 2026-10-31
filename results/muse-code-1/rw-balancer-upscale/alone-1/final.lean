import BalancerSwap.Spec

namespace BalancerSwap

/-! ## Fixed correct wrapper -/

def givenInQuote (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut

def givenOutCharge (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  let price := m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))
  let D := (ONE - p.fee) * p.rate s.tokenIn
  (ONE * ONE * price + (D - 1)) / D

/-- `onSwap` with correct rounding (always in the pool's favour). -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn =>
    if p.rate s.tokenOut = 0 then none
    else some (givenInQuote m p s)
  | .givenOut =>
    if p.rate s.tokenIn = 0 then none
    else if ONE ≤ p.fee then none
    else if scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) then
      some (givenOutCharge m p s)
    else none

/-! ## Basic arithmetic helpers -/

theorem one_pos : 0 < ONE := by decide

theorem floor_lt_succ_mul (a b : Nat) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h1 := Nat.div_add_mod a b
  have hm : a % b < b := Nat.mod_lt a hb
  have hcomm : a / b * b + a % b = a := by
    have : b * (a / b) + a % b = a := h1
    rw [Nat.mul_comm] at this
    exact this
  have e : (a / b + 1) * b = a / b * b + b := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

theorem ceil_ge_aux (a d : Nat) (hd : 0 < d) : a ≤ (a + (d - 1)) / d * d := by
  have h1 := Nat.div_add_mod (a + (d - 1)) d
  have h2 : (a + (d - 1)) % d < d := Nat.mod_lt _ hd
  have hcomm : (a + (d - 1)) / d * d + (a + (d - 1)) % d = a + (d - 1) := by
    have : d * ((a + (d - 1)) / d) + (a + (d - 1)) % d = a + (d - 1) := h1
    rw [Nat.mul_comm] at this
    exact this
  rw [Nat.mul_comm]
  omega

theorem ceil_le_aux {a d q : Nat} (hd : 0 < d) (h : a ≤ q * d) : (a + (d - 1)) / d ≤ q := by
  have h2 : (a + (d - 1)) / d < q + 1 := by
    have hlt : a + (d - 1) < (q + 1) * d := by
      have e : (q + 1) * d = q * d + d := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    exact (Nat.div_lt_iff_lt_mul hd).2 hlt
  exact Nat.le_of_lt_succ h2

theorem ceil_pos_aux {N D : Nat} (hD : 0 < D) (hN : 0 < N) : 0 < (N + (D - 1)) / D := by
  have hle : D ≤ N + (D - 1) := by omega
  exact Nat.div_pos hle hD

theorem ceil_pred_mul_lt_aux {N D : Nat} (hD : 0 < D) (hN : 0 < N) :
    ((N + (D - 1)) / D - 1) * D < N := by
  have hle : (N + (D - 1)) / D * D ≤ N + (D - 1) := Nat.div_mul_le_self _ _
  have hqpos : 0 < (N + (D - 1)) / D := ceil_pos_aux hD hN
  have hsa : (N + (D - 1)) / D - 1 + 1 = (N + (D - 1)) / D :=
    Nat.sub_add_cancel hqpos
  have h1 : ((N + (D - 1)) / D - 1 + 1) * D = (N + (D - 1)) / D * D := by
    rw [hsa]
  have h2 : ((N + (D - 1)) / D - 1 + 1) * D =
      ((N + (D - 1)) / D - 1) * D + D := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

theorem scaleUp_ge (a r : Nat) : a * r ≤ scaleUp a r * ONE := by
  unfold scaleUp
  exact ceil_ge_aux _ _ one_pos

theorem scaleDown_mul_le (a r : Nat) : scaleDown a r * ONE ≤ a * r := by
  unfold scaleDown
  exact Nat.div_mul_le_self _ _

theorem netLess_le_net (p : Pool) (s : Swap) :
    netInLessOneDown p s ≤ netInDown p s := by
  unfold netInLessOneDown netInDown
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  omega

theorem D_pos_of (p : Pool) (s : Swap) (hfee : p.fee < ONE) (hr : 0 < p.rate s.tokenIn) :
    0 < (ONE - p.fee) * p.rate s.tokenIn := by
  exact Nat.mul_pos (by omega) hr

theorem amount_raw_le_of_scale {a b r : Nat} (hr : 0 < r)
    (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  have h1 : a * r ≤ scaleUp a r * ONE := scaleUp_ge a r
  have h2 : scaleDown b r * ONE ≤ b * r := scaleDown_mul_le b r
  have h3 : scaleUp a r * ONE < scaleDown b r * ONE :=
    (Nat.mul_lt_mul_right one_pos).2 h
  have hlt : a * r < b * r := by omega
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_lt hlt) hr

theorem quote_mul_le_aux (m : PoolMath) (p : Pool) (s : Swap) :
    givenInQuote m p s * p.rate s.tokenOut ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
  unfold givenInQuote
  exact Nat.div_mul_le_self _ _

theorem quote_lt_succ_aux (m : PoolMath) (p : Pool) (s : Swap)
    (hr : 0 < p.rate s.tokenOut) :
    m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE <
      (givenInQuote m p s + 1) * p.rate s.tokenOut := by
  have h := floor_lt_succ_mul
    (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE)
    (p.rate s.tokenOut) hr
  simpa [givenInQuote] using h

theorem charge_ge_aux (m : PoolMath) (p : Pool) (s : Swap)
    (hD : 0 < (ONE - p.fee) * p.rate s.tokenIn) :
    ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) ≤
      givenOutCharge m p s * ((ONE - p.fee) * p.rate s.tokenIn) := by
  unfold givenOutCharge
  simp only
  exact ceil_ge_aux _ _ hD

theorem charge_pred_lt_aux (m : PoolMath) (p : Pool) (s : Swap)
    (hD : 0 < (ONE - p.fee) * p.rate s.tokenIn)
    (hN : 0 < ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut))) :
    (givenOutCharge m p s - 1) * ((ONE - p.fee) * p.rate s.tokenIn) <
      ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) := by
  unfold givenOutCharge
  simp only
  exact ceil_pred_mul_lt_aux hD hN

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hkind hval hq
  have hon : onSwap m p s = some y := hq
  unfold onSwap at hon
  rw [hkind] at hon
  by_cases hr : p.rate s.tokenOut = 0
  · simp [hr] at hon
  · simp [hr] at hon
    subst hon
    simp only [givenInQuote]
    have h := Nat.div_mul_le_self
      (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE)
      (p.rate s.tokenOut)
    have hc : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE =
        ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
      rw [Nat.mul_comm]
    omega

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hkind hval hq
  have hon : onSwap m p s = some y := hq
  unfold onSwap at hon
  rw [hkind] at hon
  by_cases hr : p.rate s.tokenOut = 0
  · simp [hr] at hon
  · simp [hr] at hon
    subst hon
    have hle : netInLessOneDown p s ≤ netInDown p s := netLess_le_net p s
    have hmono1 := hmono.1 (scaledBalances p) s.tokenIn s.tokenOut
      (netInLessOneDown p s) (netInDown p s) hle
    have hlt := quote_lt_succ_aux m p s (by omega : 0 < p.rate s.tokenOut)
    have hmul : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s)) * ONE ≤
        (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) * ONE :=
      Nat.mul_le_mul_right ONE hmono1
    have hcomm : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s)) * ONE =
        ONE * (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (netInLessOneDown p s)) := by
      rw [Nat.mul_comm]
    omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hkind hval hq
  have hon : onSwap m p s = some c := hq
  unfold onSwap at hon
  rw [hkind] at hon
  by_cases hr : p.rate s.tokenIn = 0
  · simp [hr] at hon
  · simp [hr] at hon
    obtain ⟨hfee', hlt, hceq⟩ := hon
    subst hceq
    have hr' : 0 < p.rate s.tokenIn := by omega
    have hD : 0 < (ONE - p.fee) * p.rate s.tokenIn := D_pos_of p s hfee' hr'
    have hge := charge_ge_aux m p s hD
    simpa [outPrice, Nat.mul_assoc] using hge

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c hmono hkind hval hq
  have hon : onSwap m p s = some c := hq
  unfold onSwap at hon
  rw [hkind] at hon
  by_cases hr : p.rate s.tokenIn = 0
  · simp [hr] at hon
  · simp [hr] at hon
    obtain ⟨hfee', hlt, hceq⟩ := hon
    subst hceq
    have hr' : 0 < p.rate s.tokenIn := by omega
    have hD : 0 < (ONE - p.fee) * p.rate s.tokenIn := D_pos_of p s hfee' hr'
    have hDne : (ONE - p.fee) * p.rate s.tokenIn ≠ 0 := by omega
    have _hlt' := hlt
    simp only [outPrice] at ⊢
    by_cases hN : 0 < ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))
    · have hpred := ceil_pred_mul_lt_aux hD hN
      have hle : (givenOutCharge m p s - 1) * ((ONE - p.fee) * p.rate s.tokenIn) < ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := by
        unfold givenOutCharge
        simp only
        exact hpred
      have hadd : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) := by
        have e : ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) = ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + ONE * p.rate s.tokenIn := by
          rw [Nat.mul_add, Nat.mul_assoc]
        omega
      have hcomm : (givenOutCharge m p s - 1) * ((ONE - p.fee) * p.rate s.tokenIn) = (givenOutCharge m p s - 1) * (ONE - p.fee) * p.rate s.tokenIn := by
        rw [Nat.mul_assoc]
      omega
    · have hzz : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) = 0 := by omega
      have hprice : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) = 0 := by
        have hOOpos : 0 < ONE * ONE := Nat.mul_pos one_pos one_pos
        have hOO : ONE * ONE ≠ 0 := by omega
        have h := (Nat.mul_eq_zero).1 hzz
        cases h with
        | inl hl => omega
        | inr hr => exact hr
      have hcharge0 : givenOutCharge m p s = 0 := by
        unfold givenOutCharge
        simp only
        rw [hprice]
        simp only [Nat.mul_zero, Nat.zero_add]
        exact (Nat.div_eq_zero_iff).2 (Or.inr (by omega))
      have hzero : (givenOutCharge m p s - 1) * (ONE - p.fee) * p.rate s.tokenIn = 0 := by
        rw [hcharge0]
        simp
      rw [hprice]
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [hzero]
      exact Nat.mul_pos one_pos hr'

theorem scaleUp_zero (a : Nat) : scaleUp a 0 = 0 := by
  unfold scaleUp
  simp only [Nat.mul_zero, Nat.zero_add]
  exact (Nat.div_eq_zero_iff).2 (Or.inr (by have h := one_pos; omega))

theorem scaleDown_zero (b : Nat) : scaleDown b 0 = 0 := by
  unfold scaleDown
  simp only [Nat.mul_zero]
  exact Nat.zero_div _

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hwb hkind hval hr_out hfee
  have hrate : p.rate s.tokenOut ≠ 0 := Nat.ne_of_gt hr_out
  have hon : onSwap m p s = some (givenInQuote m p s) := by
    unfold onSwap
    rw [hkind]
    simp [hrate]
  have hprice_le := (hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
    (netInDown p s) hval.1 hval.2.1 hval.2.2).1
  have hq_le : givenInQuote m p s * p.rate s.tokenOut ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    quote_mul_le_aux m p s
  have hle : givenInQuote m p s * p.rate s.tokenOut ≤
      p.balance s.tokenOut * p.rate s.tokenOut := by
    have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤
        scaledBalances p s.tokenOut * ONE :=
      Nat.mul_le_mul_right ONE hprice_le
    have h2 : scaledBalances p s.tokenOut * ONE ≤
        p.balance s.tokenOut * p.rate s.tokenOut := by
      unfold scaledBalances scaleDown
      exact Nat.div_mul_le_self _ _
    omega
  have hq_bal : givenInQuote m p s ≤ p.balance s.tokenOut :=
    Nat.le_of_mul_le_mul_right hle hr_out
  have hstep_eq : step onSwap m p s = settle p s (givenInQuote m p s) := by
    unfold step
    rw [if_pos hval, hon]
  rw [hstep_eq]
  unfold settle amountOut amountIn
  rw [hkind]
  simp only
  rw [if_pos hq_bal]
  simp

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hwb hkind hval hr_in hfee hlt
  have hrate_in : p.rate s.tokenIn ≠ 0 := Nat.ne_of_gt hr_in
  have hrate_out : 0 < p.rate s.tokenOut := by
    by_cases hz : p.rate s.tokenOut = 0
    · rw [hz, scaleUp_zero, scaleDown_zero] at hlt
      omega
    · exact Nat.pos_of_ne_zero hz
  have hamt_le : s.amount ≤ p.balance s.tokenOut :=
    amount_raw_le_of_scale hrate_out hlt
  have hon : onSwap m p s = some (givenOutCharge m p s) := by
    unfold onSwap
    rw [hkind]
    simp [hrate_in, show ¬ ONE ≤ p.fee by omega, hlt]
  have hstep_eq : step onSwap m p s = settle p s (givenOutCharge m p s) := by
    unfold step
    rw [if_pos hval, hon]
  rw [hstep_eq]
  unfold settle amountOut amountIn
  rw [hkind]
  simp only
  rw [if_pos hamt_le]
  simp

theorem inflow_givenIn_le (p : Pool) (s : Swap) :
    (scaledBalances p s.tokenIn + netInDown p s) * ONE ≤
      (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn := by
  have hB : scaledBalances p s.tokenIn * ONE ≤
      p.balance s.tokenIn * p.rate s.tokenIn := by
    unfold scaledBalances scaleDown
    exact Nat.div_mul_le_self _ _
  have hdiv : netInDown p s * (ONE * ONE) ≤
      s.amount * (ONE - p.fee) * p.rate s.tokenIn := by
    unfold netInDown
    exact Nat.div_mul_le_self _ _
  have hN : s.amount * (ONE - p.fee) ≤ s.amount * ONE :=
    Nat.mul_le_mul_left _ (by omega)
  have hNr : s.amount * (ONE - p.fee) * p.rate s.tokenIn ≤
      s.amount * ONE * p.rate s.tokenIn :=
    Nat.mul_le_mul_right _ hN
  have h1 : netInDown p s * (ONE * ONE) ≤ s.amount * ONE * p.rate s.tokenIn :=
    Nat.le_trans hdiv hNr
  have e1 : netInDown p s * (ONE * ONE) = netInDown p s * ONE * ONE := by
    ac_rfl
  have e2 : s.amount * ONE * p.rate s.tokenIn = s.amount * p.rate s.tokenIn * ONE := by
    ac_rfl
  have h2 : netInDown p s * ONE * ONE ≤ s.amount * p.rate s.tokenIn * ONE := by
    omega
  have hnet_one : netInDown p s * ONE ≤ s.amount * p.rate s.tokenIn :=
    Nat.le_of_mul_le_mul_right h2 one_pos
  have e_add1 : (scaledBalances p s.tokenIn + netInDown p s) * ONE =
      scaledBalances p s.tokenIn * ONE + netInDown p s * ONE := by
    rw [Nat.add_mul]
  have e_add2 : (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn =
      p.balance s.tokenIn * p.rate s.tokenIn + s.amount * p.rate s.tokenIn := by
    rw [Nat.add_mul]
  omega

theorem outflow_givenIn_le (m : PoolMath) (p : Pool) (s : Swap)
    (_hr : 0 < p.rate s.tokenOut)
    (hy : givenInQuote m p s ≤ p.balance s.tokenOut) :
    scaledBalances p s.tokenOut ≤
      scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) +
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
  have hB : scaledBalances p s.tokenOut * ONE ≤
      p.balance s.tokenOut * p.rate s.tokenOut := by
    unfold scaledBalances scaleDown
    exact Nat.div_mul_le_self _ _
  have hq : givenInQuote m p s * p.rate s.tokenOut ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    quote_mul_le_aux m p s
  have hbal : p.balance s.tokenOut * p.rate s.tokenOut =
      (p.balance s.tokenOut - givenInQuote m p s) * p.rate s.tokenOut +
        givenInQuote m p s * p.rate s.tokenOut := by
    have h1 : (p.balance s.tokenOut - givenInQuote m p s) * p.rate s.tokenOut +
        givenInQuote m p s * p.rate s.tokenOut =
        p.balance s.tokenOut * p.rate s.tokenOut := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hy]
    exact h1.symm
  have hlt : (p.balance s.tokenOut - givenInQuote m p s) * p.rate s.tokenOut <
      (scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) + 1) * ONE := by
    have h := floor_lt_succ_mul
      ((p.balance s.tokenOut - givenInQuote m p s) * p.rate s.tokenOut) ONE one_pos
    have e : scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) =
        (p.balance s.tokenOut - givenInQuote m p s) * p.rate s.tokenOut / ONE := by
      rfl
    rw [e]
    exact h
  have e_mul : (scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) + 1) * ONE +
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE =
      (scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) +
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) + 1) * ONE := by
    simp only [Nat.add_mul, Nat.one_mul]
    ac_rfl
  have hlt2 : scaledBalances p s.tokenOut * ONE <
      (scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) +
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) + 1) * ONE := by
    omega
  have hlt3 : scaledBalances p s.tokenOut <
      scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) +
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) + 1 :=
    Nat.lt_of_mul_lt_mul_right hlt2
  omega

theorem inflow_givenOut_le (m : PoolMath) (p : Pool) (s : Swap)
    (hfee : p.fee < ONE) (hr : 0 < p.rate s.tokenIn) :
    (scaledBalances p s.tokenIn +
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut))) * ONE ≤
      (p.balance s.tokenIn + givenOutCharge m p s) * p.rate s.tokenIn := by
  have hB : scaledBalances p s.tokenIn * ONE ≤
      p.balance s.tokenIn * p.rate s.tokenIn := by
    unfold scaledBalances scaleDown
    exact Nat.div_mul_le_self _ _
  have hD : 0 < (ONE - p.fee) * p.rate s.tokenIn := D_pos_of p s hfee hr
  have hge : ONE * ONE *
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) ≤
      givenOutCharge m p s * ((ONE - p.fee) * p.rate s.tokenIn) :=
    charge_ge_aux m p s hD
  have hfee_le : (ONE - p.fee) ≤ ONE := by omega
  have hcharge_le : givenOutCharge m p s * ((ONE - p.fee) * p.rate s.tokenIn) ≤
      givenOutCharge m p s * (ONE * p.rate s.tokenIn) := by
    have h : (ONE - p.fee) * p.rate s.tokenIn ≤ ONE * p.rate s.tokenIn :=
      Nat.mul_le_mul_right _ hfee_le
    exact Nat.mul_le_mul_left _ h
  have e1 : givenOutCharge m p s * (ONE * p.rate s.tokenIn) =
      givenOutCharge m p s * p.rate s.tokenIn * ONE := by ac_rfl
  have e2 : ONE * ONE *
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) =
      (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE := by ac_rfl
  have hprice_one : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤
      givenOutCharge m p s * p.rate s.tokenIn := by
    have h1 : (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE ≤
        givenOutCharge m p s * p.rate s.tokenIn * ONE := by omega
    exact Nat.le_of_mul_le_mul_right h1 one_pos
  have e_add1 : (scaledBalances p s.tokenIn +
      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut))) * ONE =
      scaledBalances p s.tokenIn * ONE +
        m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE := by
    rw [Nat.add_mul]
  have e_add2 : (p.balance s.tokenIn + givenOutCharge m p s) * p.rate s.tokenIn =
      p.balance s.tokenIn * p.rate s.tokenIn +
        givenOutCharge m p s * p.rate s.tokenIn := by
    rw [Nat.add_mul]
  omega

theorem outflow_givenOut_le (p : Pool) (s : Swap)
    (hamt : s.amount ≤ p.balance s.tokenOut) :
    scaledBalances p s.tokenOut ≤
      scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) +
        scaleUp s.amount (p.rate s.tokenOut) := by
  have hB : scaledBalances p s.tokenOut * ONE ≤
      p.balance s.tokenOut * p.rate s.tokenOut := by
    unfold scaledBalances scaleDown
    exact Nat.div_mul_le_self _ _
  have hUp : s.amount * p.rate s.tokenOut ≤
      scaleUp s.amount (p.rate s.tokenOut) * ONE :=
    scaleUp_ge _ _
  have hbal : p.balance s.tokenOut * p.rate s.tokenOut =
      (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut +
        s.amount * p.rate s.tokenOut := by
    have h1 : (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut +
        s.amount * p.rate s.tokenOut =
        p.balance s.tokenOut * p.rate s.tokenOut := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hamt]
    exact h1.symm
  have hlt : (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut <
      (scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) + 1) * ONE := by
    have h := floor_lt_succ_mul
      ((p.balance s.tokenOut - s.amount) * p.rate s.tokenOut) ONE one_pos
    have e : scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) =
        (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut / ONE := by
      rfl
    rw [e]
    exact h
  have e_mul : (scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) + 1) * ONE +
      scaleUp s.amount (p.rate s.tokenOut) * ONE =
      (scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) +
        scaleUp s.amount (p.rate s.tokenOut) + 1) * ONE := by
    simp only [Nat.add_mul, Nat.one_mul]
    ac_rfl
  have hlt2 : scaledBalances p s.tokenOut * ONE <
      (scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) +
        scaleUp s.amount (p.rate s.tokenOut) + 1) * ONE := by
    omega
  have hlt3 : scaledBalances p s.tokenOut <
      scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) +
        scaleUp s.amount (p.rate s.tokenOut) + 1 :=
    Nat.lt_of_mul_lt_mul_right hlt2
  omega

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hwb hstep
  unfold step at hstep
  by_cases hval : Valid p s
  · simp [hval] at hstep
    cases hq : onSwap m p s with
    | none => simp [hq] at hstep
    | some c =>
      simp [hq] at hstep
      unfold settle at hstep
      by_cases hset : amountOut s c ≤ p.balance s.tokenOut
      · simp [hset] at hstep
        subst hstep
        unfold value
        cases hkind : s.kind with
        | givenIn =>
          have hon : onSwap m p s = some (givenInQuote m p s) := by
            unfold onSwap
            rw [hkind]
            by_cases hr : p.rate s.tokenOut = 0
            · unfold onSwap at hq
              rw [hkind] at hq
              simp [hr] at hq
            · simp [hr]
          rw [hon] at hq
          simp at hq
          subst hq
          simp only [amountIn, amountOut, hkind] at ⊢
          have hval' : s.tokenIn ≠ s.tokenOut ∧ s.tokenIn < p.n ∧ s.tokenOut < p.n := hval
          have hsound := hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
            (netInDown p s) hval'.1 hval'.2.1 hval'.2.2
          have hprice_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
              (netInDown p s) ≤ scaledBalances p s.tokenOut := hsound.1
          have hmono := hwb.monotone
          have htrade_le := hsound.2
          have hr_out : 0 < p.rate s.tokenOut := by
            by_cases hr : p.rate s.tokenOut = 0
            · unfold onSwap at hon
              rw [hkind] at hon
              simp [hr] at hon
            · exact Nat.pos_of_ne_zero hr
          have hy_le : givenInQuote m p s ≤ p.balance s.tokenOut := by
            unfold amountOut at hset
            rw [hkind] at hset
            simpa using hset
          have hinflow : scaledBalances p s.tokenIn + netInDown p s ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - givenInQuote m p s) } s.tokenIn := by
            have h := inflow_givenIn_le p s
            have hle : (scaledBalances p s.tokenIn + netInDown p s) * ONE ≤
                (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn := h
            have hle2 : scaledBalances p s.tokenIn + netInDown p s ≤
                scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) :=
              (Nat.le_div_iff_mul_le one_pos).2 hle
            have heq : (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
                s.tokenOut (p.balance s.tokenOut - givenInQuote m p s)) s.tokenIn =
                p.balance s.tokenIn + s.amount := by
              unfold update2
              simp
            have heq2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - givenInQuote m p s) } s.tokenIn = scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := by
              unfold scaledBalances
              simp [heq]
            rw [heq2]
            exact hle2
          have houtflow : scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - givenInQuote m p s) } s.tokenOut := by
            have hle : scaledBalances p s.tokenOut ≤
                scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) +
                  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
              outflow_givenIn_le m p s hr_out hy_le
            have heq : (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
                s.tokenOut (p.balance s.tokenOut - givenInQuote m p s)) s.tokenOut =
                p.balance s.tokenOut - givenInQuote m p s := by
              unfold update2
              simp [Ne.symm hval'.1]
            have heq2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - givenInQuote m p s) } s.tokenOut = scaleDown (p.balance s.tokenOut - givenInQuote m p s) (p.rate s.tokenOut) := by
              unfold scaledBalances
              simp [heq]
            omega
          have hle_all : ∀ k, k < p.n → update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - givenInQuote m p s) } k := by
            intro k hk
            by_cases hi : k = s.tokenIn
            · subst hi
              have e : update2 (scaledBalances p) s.tokenIn
                  (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut
                  (scaledBalances p s.tokenOut -
                    m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))
                  s.tokenIn =
                  scaledBalances p s.tokenIn + netInDown p s := by
                unfold update2
                simp
              rw [e]
              exact hinflow
            · by_cases hj : k = s.tokenOut
              · subst hj
                have e : update2 (scaledBalances p) s.tokenIn
                    (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut
                    (scaledBalances p s.tokenOut -
                      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))
                    s.tokenOut =
                    scaledBalances p s.tokenOut -
                      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
                  unfold update2
                  simp [hi]
                rw [e]
                exact houtflow
              · have e1 : update2 (scaledBalances p) s.tokenIn
                    (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut
                    (scaledBalances p s.tokenOut -
                      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k =
                    scaledBalances p k := by
                  unfold update2
                  simp [hi, hj]
                have e2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - givenInQuote m p s) } k = scaledBalances p k := by
                  unfold scaledBalances
                  have e : (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
                      s.tokenOut (p.balance s.tokenOut - givenInQuote m p s)) k =
                      p.balance k := by
                    unfold update2
                    simp [hi, hj]
                  simp [e]
                rw [e1, e2]
                exact Nat.le_refl _
          have h1 : m.invariant (scaledBalances p) ≤
              m.invariant (update2 (scaledBalances p) s.tokenIn
                (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut
                (scaledBalances p s.tokenOut -
                  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))) :=
            htrade_le
          have h2 : m.invariant (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))) ≤ m.invariant (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - givenInQuote m p s) }) := hmono _ _ hle_all
          exact Nat.le_trans h1 h2
        | givenOut =>
          have hq0 : onSwap m p s = some c := hq
          unfold onSwap at hq0
          rw [hkind] at hq0
          simp at hq0
          obtain ⟨h1, h2, h3, h4⟩ := hq0
          have hon : onSwap m p s = some (givenOutCharge m p s) := by
            unfold onSwap
            rw [hkind]
            simp [h1, h2, h3]
          rw [hon] at hq
          simp at hq
          subst hq
          simp only [amountIn, amountOut, hkind] at ⊢
          have hval' : s.tokenIn ≠ s.tokenOut ∧ s.tokenIn < p.n ∧ s.tokenOut < p.n := hval
          have hy_le : s.amount ≤ p.balance s.tokenOut := by
            unfold amountOut at hset
            rw [hkind] at hset
            simpa using hset
          have hfee : p.fee < ONE := h2
          have hr_in : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero h1
          have hlt : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := h3
          have hsound := hwb.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) hval'.1 hval'.2.1 hval'.2.2 hlt
          have hmono := hwb.monotone
          have hinflow : scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut (p.balance s.tokenOut - s.amount) } s.tokenIn := by
            have h := inflow_givenOut_le m p s hfee hr_in
            have hle : (scaledBalances p s.tokenIn +
                m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut))) * ONE ≤
                (p.balance s.tokenIn + givenOutCharge m p s) * p.rate s.tokenIn := h
            have hle2 : scaledBalances p s.tokenIn +
                m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut)) ≤
                scaleDown (p.balance s.tokenIn + givenOutCharge m p s) (p.rate s.tokenIn) :=
              (Nat.le_div_iff_mul_le one_pos).2 hle
            have heq : (update2 p.balance s.tokenIn
                (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut
                (p.balance s.tokenOut - s.amount)) s.tokenIn =
                p.balance s.tokenIn + givenOutCharge m p s := by
              unfold update2
              simp
            have heq2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut (p.balance s.tokenOut - s.amount) } s.tokenIn = scaleDown (p.balance s.tokenIn + givenOutCharge m p s) (p.rate s.tokenIn) := by
              unfold scaledBalances
              simp [heq]
            rw [heq2]
            exact hle2
          have houtflow : scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut (p.balance s.tokenOut - s.amount) } s.tokenOut := by
            have hle : scaledBalances p s.tokenOut ≤
                scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) +
                  scaleUp s.amount (p.rate s.tokenOut) :=
              outflow_givenOut_le p s hy_le
            have heq : (update2 p.balance s.tokenIn
                (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut
                (p.balance s.tokenOut - s.amount)) s.tokenOut =
                p.balance s.tokenOut - s.amount := by
              unfold update2
              simp [Ne.symm hval'.1]
            have heq2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut (p.balance s.tokenOut - s.amount) } s.tokenOut = scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
              unfold scaledBalances
              simp [heq]
            omega
          have hle_all : ∀ k, k < p.n → update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut (p.balance s.tokenOut - s.amount) } k := by
            intro k hk
            by_cases hi : k = s.tokenIn
            · subst hi
              have e : update2 (scaledBalances p) s.tokenIn
                  (scaledBalances p s.tokenIn +
                    m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                      (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
                  (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))
                  s.tokenIn =
                  scaledBalances p s.tokenIn +
                    m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                      (scaleUp s.amount (p.rate s.tokenOut)) := by
                unfold update2
                simp
              rw [e]
              exact hinflow
            · by_cases hj : k = s.tokenOut
              · subst hj
                have e : update2 (scaledBalances p) s.tokenIn
                    (scaledBalances p s.tokenIn +
                      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                        (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
                    (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))
                    s.tokenOut =
                    scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
                  unfold update2
                  simp [hi]
                rw [e]
                exact houtflow
              · have e1 : update2 (scaledBalances p) s.tokenIn
                    (scaledBalances p s.tokenIn +
                      m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                        (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
                    (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k =
                    scaledBalances p k := by
                  unfold update2
                  simp [hi, hj]
                have e2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut (p.balance s.tokenOut - s.amount) } k = scaledBalances p k := by
                  unfold scaledBalances
                  have e : (update2 p.balance s.tokenIn
                      (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut
                      (p.balance s.tokenOut - s.amount)) k =
                      p.balance k := by
                    unfold update2
                    simp [hi, hj]
                  simp [e]
                rw [e1, e2]
                exact Nat.le_refl _
          have h1 : m.invariant (scaledBalances p) ≤
              m.invariant (update2 (scaledBalances p) s.tokenIn
                (scaledBalances p s.tokenIn +
                  m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                    (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
                (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))) :=
            hsound
          have h2 : m.invariant (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))) ≤ m.invariant (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + givenOutCharge m p s) s.tokenOut (p.balance s.tokenOut - s.amount) }) := hmono _ _ hle_all
          exact Nat.le_trans h1 h2
      · simp [hset] at hstep
  · simp [hval] at hstep

theorem step_n_eq (m : PoolMath) (p : Pool) (s : Swap) (p1 : Pool) :
    step onSwap m p s = some p1 → p1.n = p.n := by
  intro h
  unfold step at h
  by_cases hval : Valid p s
  · simp [hval] at h
    cases hq : onSwap m p s with
    | none => simp [hq] at h
    | some c =>
      simp [hq] at h
      unfold settle at h
      by_cases hset : amountOut s c ≤ p.balance s.tokenOut
      · simp [hset] at h
        subst h
        rfl
      · simp [hset] at h
  · simp [hval] at h

theorem run_n_eq (m : PoolMath) (p : Pool) (ss : List Swap) (p' : Pool) :
    run onSwap m p ss = some p' → p'.n = p.n := by
  intro h
  induction ss generalizing p p' with
  | nil =>
    simp [run] at h
    subst h
    rfl
  | cons s ss ih =>
    simp only [run] at h
    cases hstep : step onSwap m p s with
    | none => simp [hstep] at h
    | some p1 =>
      simp [hstep] at h
      have hn1 : p1.n = p.n := step_n_eq m p s p1 hstep
      have hn2 : p'.n = p1.n := ih p1 p' h
      omega

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' hwb hrun
  induction ss generalizing p p' with
  | nil =>
    simp [run] at hrun
    subst hrun
    unfold value
    exact Nat.le_refl _
  | cons s ss ih =>
    simp only [run] at hrun
    cases hstep : step onSwap m p s with
    | none => simp [hstep] at hrun
    | some p1 =>
      simp [hstep] at hrun
      have h1 : value m p ≤ value m p1 :=
        req_swap_keeps_value m p s p1 hwb hstep
      have hn1 : p1.n = p.n := step_n_eq m p s p1 hstep
      have hwb1 : WellBehaved m p1.n := by rw [hn1]; exact hwb
      have h2 : value m p1 ≤ value m p' := ih p1 p' hwb1 hrun
      exact Nat.le_trans h1 h2

end BalancerSwap

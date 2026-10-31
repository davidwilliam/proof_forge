import BalancerSwap.Spec
import ProofForgeFin.Rounding
namespace BalancerSwap

def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn =>
    if p.rate s.tokenOut = 0 then none
    else some ((m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) / p.rate s.tokenOut)
  | .givenOut =>
    if scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) then
      if p.rate s.tokenIn = 0 then none
      else if ONE ≤ p.fee then none
      else some (ProofForgeFin.ceilDiv (ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee))
    else none

theorem one_pos : 0 < ONE := by decide

theorem one_ne_zero : ONE ≠ 0 := by decide

theorem scaleUp_eq_ceil (a r : Nat) : scaleUp a r = ProofForgeFin.ceilDiv (a * r) ONE := by
  unfold scaleUp ProofForgeFin.ceilDiv
  have h : a * r + (ONE - 1) = a * r + ONE - 1 := by
    have := one_pos
    omega
  rw [h]

theorem ceil_ge' (a b : Nat) (hb : 0 < b) : a ≤ ProofForgeFin.ceilDiv a b * b :=
  ProofForgeFin.le_ceilDiv_mul a b hb

theorem ceil_lt' (a b : Nat) (hb : 0 < b) : ProofForgeFin.ceilDiv a b * b < a + b :=
  ProofForgeFin.ceilDiv_mul_lt a b hb

theorem floor_le' (a b : Nat) : a / b * b ≤ a := Nat.div_mul_le_self a b

theorem floor_lt' (a b : Nat) (hb : 0 < b) : a < (a / b + 1) * b :=
  ProofForgeFin.lt_div_add_one_mul a b hb

theorem netLessOne_le_net (p : Pool) (s : Swap) : netInLessOneDown p s ≤ netInDown p s := by
  unfold netInLessOneDown netInDown
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  omega

theorem scaleDown_mul_le (a r : Nat) : scaleDown a r * ONE ≤ a * r := by
  unfold scaleDown
  exact Nat.div_mul_le_self _ _

theorem scaleUp_ge (a r : Nat) : a * r ≤ scaleUp a r * ONE := by
  rw [scaleUp_eq_ceil]
  exact ProofForgeFin.le_ceilDiv_mul _ _ one_pos

theorem scaleUp_lt (a r : Nat) : scaleUp a r * ONE < a * r + ONE := by
  rw [scaleUp_eq_ceil]
  exact ProofForgeFin.ceilDiv_mul_lt _ _ one_pos

theorem ceil_sub_one_mul_lt {a b : Nat} (hb : 0 < b) (ha : 0 < a) :
    (ProofForgeFin.ceilDiv a b - 1) * b < a := by
  have h1 := ProofForgeFin.ceilDiv_mul_lt a b hb
  have sm : (ProofForgeFin.ceilDiv a b - 1) * b =
      ProofForgeFin.ceilDiv a b * b - b := by
    rw [Nat.sub_mul, Nat.one_mul]
  omega

theorem ceil_pred_mul_le {a b : Nat} (hb : 0 < b) :
    (ProofForgeFin.ceilDiv a b - 1) * b < a + 1 := by
  by_cases ha : a = 0
  · subst ha
    simp [ProofForgeFin.ceilDiv_zero_left]
  · have ha' : 0 < a := Nat.pos_of_ne_zero ha
    have := ceil_sub_one_mul_lt hb ha'
    omega

theorem rate_pos_of_scale_lt {a B r : Nat}
    (h : scaleUp a r < scaleDown B r) : 0 < r := by
  by_cases hr : r = 0
  · subst hr
    exfalso
    have e1 : a * 0 = 0 := Nat.mul_zero a
    have e2 : B * 0 = 0 := Nat.mul_zero B
    unfold scaleUp scaleDown at h
    rw [e1, e2] at h
    have d1 : (0 + (ONE - 1)) / ONE = 0 := Nat.div_eq_of_lt (by have := one_pos; omega)
    have d2 : (0 : Nat) / ONE = 0 := Nat.zero_div ONE
    rw [d1, d2] at h
    exact Nat.lt_irrefl 0 h
  · exact Nat.pos_of_ne_zero hr

theorem raw_le_of_scale_lt {a B r : Nat}
    (h : scaleUp a r < scaleDown B r) : a ≤ B := by
  have hr' := rate_pos_of_scale_lt h
  have h1 := scaleUp_ge a r
  have h2 := scaleDown_mul_le B r
  have hle : scaleUp a r + 1 ≤ scaleDown B r := h
  have h3 : (scaleUp a r + 1) * ONE ≤ scaleDown B r * ONE :=
    Nat.mul_le_mul_right ONE hle
  have h4 : scaleUp a r * ONE + ONE ≤ B * r := by
    have e : (scaleUp a r + 1) * ONE = scaleUp a r * ONE + ONE := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  have h5 : a * r < B * r + 1 := by omega
  have h6 : a * r < (B + 1) * r := by
    have e2 : (B + 1) * r = B * r + r := by rw [Nat.add_mul, Nat.one_mul]
    omega
  have hlt : a < B + 1 := Nat.lt_of_mul_lt_mul_right h6
  omega

theorem given_in_quote_le_balance (m : PoolMath) (p : Pool) (s : Swap)
    (wb : WellBehaved m p.n) (hv : Valid p s) (hr : 0 < p.rate s.tokenOut) :
    (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) /
      p.rate s.tokenOut ≤ p.balance s.tokenOut := by
  have hP := (wb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
    hv.1 hv.2.1 hv.2.2).1
  unfold scaledBalances at hP
  have hdiv : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) /
      p.rate s.tokenOut * p.rate s.tokenOut ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    Nat.div_mul_le_self _ _
  have hPONE : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤
      p.balance s.tokenOut * p.rate s.tokenOut := by
    have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤
        (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE :=
      Nat.mul_le_mul_right ONE hP
    have h2 : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤
        p.balance s.tokenOut * p.rate s.tokenOut :=
      Nat.div_mul_le_self _ _
    exact Nat.le_trans h1 h2
  have hle : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) /
      p.rate s.tokenOut * p.rate s.tokenOut ≤
      p.balance s.tokenOut * p.rate s.tokenOut :=
    Nat.le_trans hdiv hPONE
  exact Nat.le_of_mul_le_mul_right hle hr

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s wb hk hv hr hf
  unfold step
  rw [if_pos hv]
  have hrne : p.rate s.tokenOut ≠ 0 := Nat.pos_iff_ne_zero.mp hr
  have hq : onSwap m p s = some ((m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
      (netInDown p s) * ONE) / p.rate s.tokenOut) := by
    unfold onSwap
    rw [hk, if_neg hrne]
  rw [hq]
  have hle := given_in_quote_le_balance m p s wb hv hr
  unfold settle amountOut
  rw [hk]
  simp only
  rw [if_pos hle]
  rfl

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s wb hk hv hr hf hlt
  unfold step
  rw [if_pos hv]
  have hrne : p.rate s.tokenIn ≠ 0 := Nat.pos_iff_ne_zero.mp hr
  have hfee : ¬ ONE ≤ p.fee := by omega
  have hq : onSwap m p s = some (ProofForgeFin.ceilDiv
      (ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) := by
    unfold onSwap
    rw [hk, if_pos hlt, if_neg hrne, if_neg hfee]
  rw [hq]
  have hle : s.amount ≤ p.balance s.tokenOut := raw_le_of_scale_lt hlt
  unfold settle amountOut
  rw [hk]
  simp only
  rw [if_pos hle]
  rfl

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hk hv hc
  by_cases hr : p.rate s.tokenOut = 0
  · unfold onSwap at hc
    simp only [hk, if_pos hr] at hc
    simp at hc
  · unfold onSwap at hc
    simp only [hk, if_neg hr] at hc
    have hy : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) /
        p.rate s.tokenOut = y := by cases hc; rfl
    rw [← hy]
    have h1 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) /
        p.rate s.tokenOut * p.rate s.tokenOut ≤
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
      Nat.div_mul_le_self _ _
    have e : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE =
        ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
      rw [Nat.mul_comm]
    omega

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hk hv hc
  by_cases hr : p.rate s.tokenOut = 0
  · unfold onSwap at hc
    simp only [hk, if_pos hr] at hc
    simp at hc
  · unfold onSwap at hc
    simp only [hk, if_neg hr] at hc
    have hy : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) /
        p.rate s.tokenOut = y := by cases hc; rfl
    have hrpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hr
    have hmo := hmono.1 (scaledBalances p) s.tokenIn s.tokenOut
      (netInLessOneDown p s) (netInDown p s) (netLessOne_le_net p s)
    have hup : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE <
        (y + 1) * p.rate s.tokenOut := by
      rw [← hy]
      exact ProofForgeFin.lt_div_add_one_mul _ _ hrpos
    have hle : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
        ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
      Nat.mul_le_mul_left ONE hmo
    have e : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) =
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
      rw [Nat.mul_comm]
    omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hk hv hc
  unfold onSwap at hc
  simp only [hk] at hc
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) <
      scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
  · rw [if_pos hlt] at hc
    by_cases hr : p.rate s.tokenIn = 0
    · rw [if_pos hr] at hc
      simp at hc
    · rw [if_neg hr] at hc
      by_cases hf : ONE ≤ p.fee
      · rw [if_pos hf] at hc
        simp at hc
      · rw [if_neg hf] at hc
        have hy : ProofForgeFin.ceilDiv (ProofForgeFin.ceilDiv
            (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE)
            (ONE - p.fee) = c := by cases hc; rfl
        unfold outPrice
        have hrpos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hr
        have hF : 0 < ONE - p.fee := by omega
        have g1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤
            ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) *
              p.rate s.tokenIn :=
          ProofForgeFin.le_ceilDiv_mul _ _ hrpos
        have g2 : ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE ≤
            c * (ONE - p.fee) := by
          rw [← hy]
          exact ProofForgeFin.le_ceilDiv_mul _ _ hF
        calc ONE * ONE * outPrice m p s
            = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE := by
              unfold outPrice; ac_rfl
          _ ≤ (ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) *
              p.rate s.tokenIn) * ONE := Nat.mul_le_mul_right ONE g1
          _ = (ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) *
              p.rate s.tokenIn := by ac_rfl
          _ ≤ (c * (ONE - p.fee)) * p.rate s.tokenIn :=
              Nat.mul_le_mul_right _ g2
          _ = c * (ONE - p.fee) * p.rate s.tokenIn := by ac_rfl
  · rw [if_neg hlt] at hc
    simp at hc

theorem ceilDiv2_bound {P R F c amt : Nat} (hR : 0 < R) (hF : 0 < F)
    (hy : ProofForgeFin.ceilDiv (amt * ONE) F = c)
    (hamt : amt = ProofForgeFin.ceilDiv (P * ONE) R) :
    (c - 1) * F * R < ONE * (ONE * P + R) := by
  by_cases hc0 : c = 0
  · have hl0 : (c - 1) * F * R = 0 := by rw [hc0]; simp
    have h1 : 0 < ONE * P + R := by omega
    have hpos : 0 < ONE * (ONE * P + R) := Nat.mul_pos one_pos h1
    omega
  · have haONE_ne : amt * ONE ≠ 0 := by
      intro h0
      have hz : ProofForgeFin.ceilDiv (amt * ONE) F = 0 := by
        rw [h0]
        exact ProofForgeFin.ceilDiv_zero_left _
      rw [hy] at hz
      exact hc0 hz
    have haONE_pos : 0 < amt * ONE := Nat.pos_of_ne_zero haONE_ne
    have hamt_ne : amt ≠ 0 := by
      intro h0
      have h00 : amt * ONE = 0 := by rw [h0]; simp
      exact haONE_ne h00
    have hPONE_ne : P * ONE ≠ 0 := by
      intro h0
      have hz : ProofForgeFin.ceilDiv (P * ONE) R = 0 := by
        rw [h0]
        exact ProofForgeFin.ceilDiv_zero_left _
      rw [← hamt] at hz
      exact hamt_ne hz
    have hPONE_pos : 0 < P * ONE := Nat.pos_of_ne_zero hPONE_ne
    have hamt_pos : 0 < amt := Nat.pos_of_ne_zero hamt_ne
    have hA : (c - 1) * F < amt * ONE := by
      rw [← hy]
      exact ceil_sub_one_mul_lt hF haONE_pos
    have hB : (amt - 1) * R < P * ONE := by
      rw [hamt]
      exact ceil_sub_one_mul_lt hR hPONE_pos
    have step1 : (c - 1) * F * R < amt * ONE * R :=
      Nat.mul_lt_mul_of_pos_right hA hR
    have step3 : (amt - 1) * R * ONE < P * ONE * ONE :=
      Nat.mul_lt_mul_of_pos_right hB one_pos
    have hsub : (amt - 1) * R = amt * R - R := by
      rw [Nat.sub_mul, Nat.one_mul]
    have h1le : 1 ≤ amt := by omega
    have hleR : R ≤ amt * R := by
      have h1R : 1 * R ≤ amt * R := Nat.mul_le_mul_right _ h1le
      simpa using h1R
    have e_amt : amt * R = (amt - 1) * R + R := by omega
    have m1 : amt * ONE * R = (amt * R) * ONE := by ac_rfl
    have m2 : (amt * R) * ONE = ((amt - 1) * R + R) * ONE := by rw [e_amt]
    have m3 : ((amt - 1) * R + R) * ONE = (amt - 1) * R * ONE + R * ONE := by
      rw [Nat.add_mul]
    have efin : P * ONE * ONE + R * ONE = ONE * (ONE * P + R) := by
      rw [Nat.mul_add]
      have a1 : ONE * (ONE * P) = P * ONE * ONE := by ac_rfl
      have a2 : ONE * R = R * ONE := Nat.mul_comm _ _
      rw [a1, a2]
    omega

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c hmono hk hv hc
  unfold onSwap at hc
  simp only [hk] at hc
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) <
      scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
  · rw [if_pos hlt] at hc
    by_cases hr : p.rate s.tokenIn = 0
    · rw [if_pos hr] at hc
      simp at hc
    · rw [if_neg hr] at hc
      by_cases hf : ONE ≤ p.fee
      · rw [if_pos hf] at hc
        simp at hc
      · rw [if_neg hf] at hc
        have hy : ProofForgeFin.ceilDiv (ProofForgeFin.ceilDiv
            (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE)
            (ONE - p.fee) = c := by cases hc; rfl
        have hrpos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hr
        have hF : 0 < ONE - p.fee := by omega
        unfold outPrice
        exact ceilDiv2_bound hrpos hF hy rfl
  · rw [if_neg hlt] at hc
    simp at hc

theorem update2_self (b : Nat → Nat) (i x j y : Nat) :
    update2 b i x j y i = x := by
  unfold update2
  simp

theorem update2_other (b : Nat → Nat) (i x j y k : Nat) (h1 : k ≠ i) (h2 : k ≠ j) :
    update2 b i x j y k = b k := by
  unfold update2
  simp [h1, h2]

theorem update2_second (b : Nat → Nat) (i x j y : Nat) (h : j ≠ i) :
    update2 b i x j y j = y := by
  unfold update2
  simp [h]

theorem add_floor_le {b net B a r : Nat}
    (h1 : b * ONE ≤ B * r) (h2 : net * ONE ≤ a * r) :
    b + net ≤ (B + a) * r / ONE := by
  have e : (b + net) * ONE = b * ONE + net * ONE := Nat.add_mul _ _ _
  have e2 : (B + a) * r = B * r + a * r := Nat.add_mul _ _ _
  have h : (b + net) * ONE ≤ (B + a) * r := by omega
  exact (ProofForgeFin.le_div_iff one_pos).2 h

theorem sub_floor_ge {b P B y r : Nat}
    (h1 : b * ONE ≤ B * r) (h2 : y * r ≤ P * ONE) :
    b - P ≤ (B - y) * r / ONE := by
  have e1 : (b - P) * ONE = b * ONE - P * ONE := Nat.sub_mul _ _ _
  have e2 : (B - y) * r = B * r - y * r := Nat.sub_mul _ _ _
  have h : (b - P) * ONE ≤ (B - y) * r := by omega
  exact (ProofForgeFin.le_div_iff one_pos).2 h

theorem out_new_in_ge {b P B c r F : Nat}
    (hb : b * ONE ≤ B * r)
    (hP : P * ONE * ONE ≤ c * F * r)
    (hF : F ≤ ONE) :
    b + P ≤ (B + c) * r / ONE := by
  have hF2 : c * F * r ≤ c * ONE * r := by
    have g1 : c * F ≤ c * ONE := Nat.mul_le_mul (Nat.le_refl _) hF
    exact Nat.mul_le_mul g1 (Nat.le_refl _)
  have h1 : P * ONE * ONE ≤ c * ONE * r := Nat.le_trans hP hF2
  have h2 : P * ONE ≤ c * r := by
    have e1 : P * ONE * ONE = (P * ONE) * ONE := by ac_rfl
    have e2 : c * ONE * r = (c * r) * ONE := by ac_rfl
    rw [e1, e2] at h1
    exact Nat.le_of_mul_le_mul_right h1 one_pos
  have e : (b + P) * ONE = b * ONE + P * ONE := Nat.add_mul _ _ _
  have e2 : (B + c) * r = B * r + c * r := Nat.add_mul _ _ _
  have h : (b + P) * ONE ≤ (B + c) * r := by omega
  exact (ProofForgeFin.le_div_iff one_pos).2 h

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' wb hstep
  have hv : Valid p s := by
    unfold step at hstep
    by_cases h : Valid p s
    · exact h
    · rw [if_neg h] at hstep
      simp at hstep
  unfold step at hstep
  rw [if_pos hv] at hstep
  cases hqq : onSwap m p s with
  | none =>
    simp [hqq] at hstep
  | some q =>
    simp only [hqq] at hstep
    have hle_set : amountOut s q ≤ p.balance s.tokenOut := by
      unfold settle at hstep
      by_cases h : amountOut s q ≤ p.balance s.tokenOut
      · exact h
      · rw [if_neg h] at hstep
        simp at hstep
    have hp' : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s q) s.tokenOut (p.balance s.tokenOut - amountOut s q) } := by
      unfold settle at hstep
      rw [if_pos hle_set] at hstep
      cases hstep
      rfl
    by_cases hk : s.kind = Kind.givenIn
    · have eOut : amountOut s q = q := by simp [amountOut, hk]
      have eIn : amountIn s q = s.amount := by simp [amountIn, hk]
      rw [eIn, eOut] at hp'
      have hbal : p'.balance = update2 p.balance s.tokenIn
          (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - q) := by
        rw [hp']
      have hrate : p'.rate = p.rate := by
        rw [hp']
      have hrne : p.rate s.tokenOut ≠ 0 := by
        intro h0
        unfold onSwap at hqq
        simp only [hk, if_pos h0] at hqq
        simp at hqq
      have hqeq : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) /
          p.rate s.tokenOut = q := by
        unfold onSwap at hqq
        simp only [hk, if_neg hrne] at hqq
        cases hqq
        rfl
      have hrpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrne
      have hsound := wb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
        hv.1 hv.2.1 hv.2.2
      have hyR : q * p.rate s.tokenOut ≤
          m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
        rw [← hqeq]
        exact Nat.div_mul_le_self _ _
      have hnet1 : netInDown p s * ONE ≤ s.amount * p.rate s.tokenIn := by
        have hnet : netInDown p s * (ONE * ONE) ≤
            s.amount * (ONE - p.fee) * p.rate s.tokenIn := by
          unfold netInDown
          exact Nat.div_mul_le_self _ _
        have hfee : ONE - p.fee ≤ ONE := Nat.sub_le _ _
        have hA : s.amount * (ONE - p.fee) ≤ s.amount * ONE :=
          Nat.mul_le_mul (Nat.le_refl _) hfee
        have hB : s.amount * (ONE - p.fee) * p.rate s.tokenIn ≤
            s.amount * ONE * p.rate s.tokenIn := Nat.mul_le_mul hA (Nat.le_refl _)
        have hc := Nat.le_trans hnet hB
        have e1 : netInDown p s * (ONE * ONE) = (netInDown p s * ONE) * ONE := by ac_rfl
        have e2 : s.amount * ONE * p.rate s.tokenIn =
            (s.amount * p.rate s.tokenIn) * ONE := by ac_rfl
        rw [e1, e2] at hc
        exact Nat.le_of_mul_le_mul_right hc one_pos
      have hb_in : scaledBalances p s.tokenIn + netInDown p s ≤
          (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE :=
        add_floor_le (scaleDown_mul_le _ _) hnet1
      have hb_out : scaledBalances p s.tokenOut -
          m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤
          (p.balance s.tokenOut - q) * p.rate s.tokenOut / ONE :=
        sub_floor_ge (scaleDown_mul_le _ _) hyR
      have eb' : ∀ k, scaledBalances p' k =
          scaleDown ((update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
            s.tokenOut (p.balance s.tokenOut - q)) k) (p.rate k) := by
        intro k
        unfold scaledBalances
        rw [hbal, hrate]
      have hmid : m.invariant (update2 (scaledBalances p) s.tokenIn
          (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut
          (scaledBalances p s.tokenOut -
            m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))) ≤
          m.invariant (scaledBalances p') := by
        apply wb.monotone
        intro k hklt
        rw [eb' k]
        by_cases hki : k = s.tokenIn
        · subst hki
          rw [update2_self, update2_self]
          exact hb_in
        · by_cases hkj : k = s.tokenOut
          · subst hkj
            rw [update2_second _ _ _ _ _ (Ne.symm hv.1),
              update2_second _ _ _ _ _ (Ne.symm hv.1)]
            exact hb_out
          · rw [update2_other _ _ _ _ _ _ hki hkj, update2_other _ _ _ _ _ _ hki hkj]
            exact Nat.le_refl _
      unfold value
      exact Nat.le_trans hsound.2 hmid
    · have hk2 : s.kind = Kind.givenOut := by
        cases hs : s.kind
        · exact absurd hs hk
        · rfl
      have eOut : amountOut s q = s.amount := by simp [amountOut, hk2]
      have eIn : amountIn s q = q := by simp [amountIn, hk2]
      rw [eIn, eOut] at hp'
      have hbal : p'.balance = update2 p.balance s.tokenIn (p.balance s.tokenIn + q) s.tokenOut (p.balance s.tokenOut - s.amount) := by
        rw [hp']
      have hrate : p'.rate = p.rate := by
        rw [hp']
      unfold onSwap at hqq
      simp only [hk2] at hqq
      by_cases hlt2 : scaleUp s.amount (p.rate s.tokenOut) <
          scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
      · rw [if_pos hlt2] at hqq
        by_cases hrne : p.rate s.tokenIn = 0
        · rw [if_pos hrne] at hqq
          simp at hqq
        · rw [if_neg hrne] at hqq
          by_cases hfee : ONE ≤ p.fee
          · rw [if_pos hfee] at hqq
            simp at hqq
          · rw [if_neg hfee] at hqq
            have hqeq : ProofForgeFin.ceilDiv (ProofForgeFin.ceilDiv
                (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE)
                (ONE - p.fee) = q := by cases hqq; rfl
            have hrpos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
            have hFle : ONE - p.fee ≤ ONE := Nat.sub_le _ _
            have hlt2' : scaleUp s.amount (p.rate s.tokenOut) <
                scaledBalances p s.tokenOut := hlt2
            have hsound := wb.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut)) hv.1 hv.2.1 hv.2.2 hlt2'
            have g1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤
                ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) *
                  p.rate s.tokenIn :=
              ProofForgeFin.le_ceilDiv_mul _ _ hrpos
            have hP2 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE ≤
                q * (ONE - p.fee) * p.rate s.tokenIn := by
              have hFpos : 0 < ONE - p.fee := by omega
              have g2 : ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn
                  s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE)
                  (p.rate s.tokenIn) * ONE ≤ q * (ONE - p.fee) := by
                rw [← hqeq]
                exact ProofForgeFin.le_ceilDiv_mul _ _ hFpos
              calc m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                    (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE
                  = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                    (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE := by ac_rfl
                _ ≤ (ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                    (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) *
                    p.rate s.tokenIn) * ONE := Nat.mul_le_mul_right ONE g1
                _ = (ProofForgeFin.ceilDiv (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                    (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) *
                    p.rate s.tokenIn := by ac_rfl
                _ ≤ (q * (ONE - p.fee)) * p.rate s.tokenIn :=
                    Nat.mul_le_mul_right _ g2
                _ = q * (ONE - p.fee) * p.rate s.tokenIn := by ac_rfl
            have hb_in2 : scaledBalances p s.tokenIn +
                m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                  (scaleUp s.amount (p.rate s.tokenOut)) ≤
                (p.balance s.tokenIn + q) * p.rate s.tokenIn / ONE :=
              out_new_in_ge (scaleDown_mul_le _ _) hP2 hFle
            have hb_out2 : scaledBalances p s.tokenOut -
                scaleUp s.amount (p.rate s.tokenOut) ≤
                (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut / ONE :=
              sub_floor_ge (scaleDown_mul_le _ _) (scaleUp_ge _ _)
            have eb' : ∀ k, scaledBalances p' k =
                scaleDown ((update2 p.balance s.tokenIn (p.balance s.tokenIn + q)
                  s.tokenOut (p.balance s.tokenOut - s.amount)) k) (p.rate k) := by
              intro k
              unfold scaledBalances
              rw [hbal, hrate]
            have hmid : m.invariant (update2 (scaledBalances p) s.tokenIn
                (scaledBalances p s.tokenIn +
                  m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
                    (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
                (scaledBalances p s.tokenOut -
                  scaleUp s.amount (p.rate s.tokenOut))) ≤
                m.invariant (scaledBalances p') := by
              apply wb.monotone
              intro k hklt
              rw [eb' k]
              by_cases hki : k = s.tokenIn
              · subst hki
                rw [update2_self, update2_self]
                exact hb_in2
              · by_cases hkj : k = s.tokenOut
                · subst hkj
                  rw [update2_second _ _ _ _ _ (Ne.symm hv.1),
                    update2_second _ _ _ _ _ (Ne.symm hv.1)]
                  exact hb_out2
                · rw [update2_other _ _ _ _ _ _ hki hkj, update2_other _ _ _ _ _ _ hki hkj]
                  exact Nat.le_refl _
            unfold value
            exact Nat.le_trans hsound hmid
      · rw [if_neg hlt2] at hqq
        simp at hqq

theorem step_preserves_n (m : PoolMath) (p : Pool) (s : Swap) (p1 : Pool)
    (h : step onSwap m p s = some p1) : p1.n = p.n := by
  unfold step at h
  by_cases hv : Valid p s
  · rw [if_pos hv] at h
    cases hq : onSwap m p s with
    | none =>
      simp [hq] at h
    | some q =>
      simp only [hq] at h
      unfold settle at h
      by_cases hs : amountOut s q ≤ p.balance s.tokenOut
      · rw [if_pos hs] at h
        cases h
        rfl
      · rw [if_neg hs] at h
        simp at h
  · rw [if_neg hv] at h
    simp at h

theorem batch_le_aux (m : PoolMath) (ss : List Swap) :
    ∀ (p p' : Pool), WellBehaved m p.n → run onSwap m p ss = some p' →
      value m p ≤ value m p' := by
  induction ss with
  | nil =>
    intro p p' wb hrun
    simp only [run] at hrun
    cases hrun
    exact Nat.le_refl _
  | cons hd tl ih =>
    intro p p' wb hrun
    simp only [run] at hrun
    cases hst : step onSwap m p hd with
    | none =>
      simp [hst] at hrun
    | some p1 =>
      simp only [hst] at hrun
      have hn : p1.n = p.n := step_preserves_n m p hd p1 hst
      have wb1 : WellBehaved m p1.n := by rw [hn]; exact wb
      have h1 : value m p ≤ value m p1 := req_swap_keeps_value m p hd p1 wb hst
      have h2 : value m p1 ≤ value m p' := ih p1 p' wb1 hrun
      exact Nat.le_trans h1 h2

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' wb hrun
  exact batch_le_aux m ss p p' wb hrun

end BalancerSwap

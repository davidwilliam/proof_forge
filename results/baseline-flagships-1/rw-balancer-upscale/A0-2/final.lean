import BalancerSwap.Spec

namespace BalancerSwap

theorem Sol_ONE_pos : 0 < ONE := by decide

theorem Sol_div_mul_le_self (a b : Nat) : a / b * b ≤ a := by
  have h := Nat.div_add_mod a b
  have hle : b * (a / b) ≤ b * (a / b) + a % b := Nat.le_add_right _ _
  rw [h] at hle
  have e : a / b * b = b * (a / b) := Nat.mul_comm _ _
  rw [e]
  exact hle

theorem Sol_lt_succ_mul_self (a b : Nat) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h := Nat.div_add_mod a b
  have hmod : a % b < b := Nat.mod_lt a hb
  have e2 : (a / b + 1) * b = b * (a / b) + b := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a / b) b]
  rw [e2]
  omega

def SolCeil (a b : Nat) : Nat := (a + b - 1) / b

theorem SolCeil_mul_ge (a b : Nat) (hb : 0 < b) : a ≤ SolCeil a b * b := by
  unfold SolCeil
  by_cases ha : a = 0
  · rw [ha]
    exact Nat.zero_le _
  · have hmod := Nat.div_add_mod (a + b - 1) b
    have hrlt : (a + b - 1) % b < b := Nat.mod_lt _ hb
    have hleQ : b * ((a + b - 1) / b) ≤ a + b - 1 := by
      have hle : b * ((a + b - 1) / b) ≤ b * ((a + b - 1) / b) + (a + b - 1) % b :=
        Nat.le_add_right _ _
      rw [hmod] at hle
      exact hle
    have eQ : (a + b - 1) / b * b = b * ((a + b - 1) / b) := Nat.mul_comm _ _
    have hRle : (a + b - 1) % b ≤ b - 1 := Nat.le_pred_of_lt hrlt
    have hsub : a + b - 1 - (b - 1) = a := by omega
    have hge : a + b - 1 - (b - 1) ≤ (a + b - 1) - (a + b - 1) % b := by
      apply Nat.sub_le_sub_left hRle
    rw [hsub] at hge
    have hQeq : a + b - 1 - (a + b - 1) % b = b * ((a + b - 1) / b) := by
      omega
    omega

theorem SolCeil_pred_lt (a b : Nat) (hb : 0 < b) (ha : 0 < a) :
    (SolCeil a b - 1) * b < a := by
  unfold SolCeil
  have hle : (a + b - 1) / b * b ≤ a + b - 1 := Sol_div_mul_le_self _ _
  have hle2 : b ≤ a + b - 1 := by omega
  have hdiv : b / b ≤ (a + b - 1) / b := Nat.div_le_div_right hle2
  have hbb : b / b = 1 := Nat.div_self hb
  have hge : 1 ≤ (a + b - 1) / b := by omega
  have hsub : ((a + b - 1) / b - 1) * b = (a + b - 1) / b * b - b := by
    rw [Nat.sub_mul, Nat.one_mul]
  rw [hsub]
  have hle3 : (a + b - 1) / b * b - b ≤ (a + b - 1) - b := Nat.sub_le_sub_right hle b
  have heq : (a + b - 1) - b = a - 1 := by omega
  rw [heq] at hle3
  have hlt : a - 1 < a := by omega
  omega

theorem Sol_div_small_eq_zero (a b : Nat) (hb : 0 < b) (hlt : a < b) : a / b = 0 := by
  have hle : a / b * b ≤ a := Sol_div_mul_le_self _ _
  by_cases hc : a / b = 0
  · exact hc
  · have hpos : 0 < a / b := Nat.pos_of_ne_zero hc
    have h1 : 1 * b ≤ a / b * b := Nat.mul_le_mul hpos (Nat.le_refl b)
    have e1 : 1 * b = b := Nat.one_mul b
    rw [e1] at h1
    omega

theorem SolCeil_eq_zero_iff (a b : Nat) (hb : 0 < b) : SolCeil a b = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact ha
    · have hpos : 0 < a := Nat.pos_of_ne_zero ha
      have hge := SolCeil_mul_ge a b hb
      rw [h] at hge
      simp at hge
      exact hge
  · intro h
    subst h
    unfold SolCeil
    have hb1 : 0 + b - 1 = b - 1 := by omega
    rw [hb1]
    have hlt1 : b - 1 < b := by omega
    exact Sol_div_small_eq_zero _ _ hb hlt1

theorem SolCeil_ub (a b : Nat) : SolCeil a b * b ≤ a + b := by
  unfold SolCeil
  have h1 : (a + b - 1) / b * b ≤ a + b - 1 := Sol_div_mul_le_self _ _
  exact Nat.le_trans h1 (Nat.sub_le _ _)

theorem Sol_scaleUp_mul_ge (a r : Nat) : a * r ≤ scaleUp a r * ONE := by
  unfold scaleUp
  have hmod := Nat.div_add_mod (a * r + (ONE - 1)) ONE
  have hrlt : (a * r + (ONE - 1)) % ONE < ONE := Nat.mod_lt _ Sol_ONE_pos
  have hRle : (a * r + (ONE - 1)) % ONE ≤ ONE - 1 := Nat.le_pred_of_lt hrlt
  have hleQ : ONE * ((a * r + (ONE - 1)) / ONE) ≤ a * r + (ONE - 1) := by
    have hle : ONE * ((a * r + (ONE - 1)) / ONE)
        ≤ ONE * ((a * r + (ONE - 1)) / ONE) + (a * r + (ONE - 1)) % ONE :=
      Nat.le_add_right _ _
    rw [hmod] at hle
    exact hle
  have hcancel : a * r + (ONE - 1) - (ONE - 1) = a * r := Nat.add_sub_cancel _ _
  have hge : a * r + (ONE - 1) - (ONE - 1) ≤ (a * r + (ONE - 1)) - (a * r + (ONE - 1)) % ONE := by
    apply Nat.sub_le_sub_left hRle
  rw [hcancel] at hge
  have hQeq : (a * r + (ONE - 1)) - (a * r + (ONE - 1)) % ONE
      = ONE * ((a * r + (ONE - 1)) / ONE) := by omega
  rw [hQeq] at hge
  have eQ : (a * r + (ONE - 1)) / ONE * ONE = ONE * ((a * r + (ONE - 1)) / ONE) :=
    Nat.mul_comm _ _
  rw [eQ]
  exact hge

theorem Sol_bmul_le (B r : Nat) : scaleDown B r * ONE ≤ B * r := by
  unfold scaleDown
  exact Sol_div_mul_le_self _ _

theorem Sol_le_floor_of_mul_le (u P : Nat) (h : u * ONE ≤ P) : u ≤ P / ONE := by
  have hcan : u * ONE / ONE = u := Nat.mul_div_cancel u Sol_ONE_pos
  have hle : u * ONE / ONE ≤ P / ONE := Nat.div_le_div_right h
  rw [hcan] at hle
  exact hle

theorem Sol_cancel_one_mul (a b : Nat) (h : a * ONE ≤ b * ONE) : a ≤ b := by
  have hle : a * ONE / ONE ≤ b * ONE / ONE := Nat.div_le_div_right h
  have ea : a * ONE / ONE = a := Nat.mul_div_cancel a Sol_ONE_pos
  have eb : b * ONE / ONE = b := Nat.mul_div_cancel b Sol_ONE_pos
  rw [ea, eb] at hle
  exact hle

theorem Sol_sub_le (a b c d : Nat) (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c := by
  omega

theorem Sol_lt_of_lt_of_le {a b c : Nat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  omega

theorem Sol_lt_of_le_of_lt {a b c : Nat} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  omega

theorem Sol_netIn_le (A fee r : Nat) :
    (A * (ONE - fee) * r / (ONE * ONE)) * ONE ≤ A * r := by
  have hdiv : (A * (ONE - fee) * r / (ONE * ONE)) * (ONE * ONE)
      ≤ A * (ONE - fee) * r := Sol_div_mul_le_self _ _
  have hfee : A * (ONE - fee) ≤ A * ONE :=
    Nat.mul_le_mul (Nat.le_refl _) (Nat.sub_le _ _)
  have hmul : A * (ONE - fee) * r ≤ A * r * ONE := by
    have h1 : A * (ONE - fee) * r ≤ A * ONE * r :=
      Nat.mul_le_mul hfee (Nat.le_refl _)
    have e : A * ONE * r = A * r * ONE := by
      calc A * ONE * r = A * (ONE * r) := by rw [Nat.mul_assoc]
        _ = A * (r * ONE) := by rw [Nat.mul_comm ONE r]
        _ = A * r * ONE := by rw [← Nat.mul_assoc]
    rw [e] at h1
    exact h1
  have htrans : (A * (ONE - fee) * r / (ONE * ONE)) * (ONE * ONE)
      ≤ A * r * ONE := Nat.le_trans hdiv hmul
  have eassoc : (A * (ONE - fee) * r / (ONE * ONE)) * (ONE * ONE)
      = ((A * (ONE - fee) * r / (ONE * ONE)) * ONE) * ONE :=
    (Nat.mul_assoc _ _ _).symm
  rw [eassoc] at htrans
  exact Sol_cancel_one_mul _ _ htrans

theorem Sol_netIn_le_pool (p : Pool) (s : Swap) :
    netInDown p s * ONE ≤ s.amount * p.rate s.tokenIn := by
  unfold netInDown
  exact Sol_netIn_le _ _ _

theorem Sol_up_in (b : Nat → Nat) (i x j y : Nat) : update2 b i x j y i = x := by
  unfold update2
  simp

theorem Sol_up_other (b : Nat → Nat) (i x j y k : Nat) (hki : k ≠ i) (hkj : k ≠ j) :
    update2 b i x j y k = b k := by
  unfold update2
  simp [hki, hkj]

theorem Sol_up_out (b : Nat → Nat) (i x j y : Nat) (hji : j ≠ i) :
    update2 b i x j y j = y := by
  unfold update2
  simp [hji]

theorem Sol_settle_some {p : Pool} {s : Swap} {c : Nat} {p' : Pool}
    (h : settle p s c = some p') :
    amountOut s c ≤ p.balance s.tokenOut ∧
    p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } := by
  unfold settle at h
  by_cases hle : amountOut s c ≤ p.balance s.tokenOut
  · simp [hle] at h
    exact ⟨hle, h.symm⟩
  · simp [hle] at h

theorem Sol_step_n (impl : Impl) (m : PoolMath) (p : Pool) (s : Swap) (q : Pool)
    (h : step impl m p s = some q) : q.n = p.n := by
  unfold step at h
  by_cases hv : Valid p s
  · simp [hv] at h
    cases hc : impl m p s with
    | none => simp [hc] at h
    | some c =>
      simp [hc] at h
      obtain ⟨_, heq⟩ := Sol_settle_some h
      rw [heq]
  · simp [hv] at h

theorem Sol_pool_bal (p : Pool) (b : Nat → Nat) (k : Nat) :
    ({ p with balance := b } : Pool).balance k = b k := by
  cases p
  rfl

theorem Sol_pool_rate (p : Pool) (b : Nat → Nat) (k : Nat) :
    ({ p with balance := b } : Pool).rate k = p.rate k := by
  cases p
  rfl

theorem Sol_scaled_other (p : Pool) (a b : Nat) (s : Swap) (k : Nat)
    (hki : k ≠ s.tokenIn) (hkj : k ≠ s.tokenOut) :
    scaledBalances { p with balance := update2 p.balance s.tokenIn a s.tokenOut b } k
      = scaleDown (p.balance k) (p.rate k) := by
  unfold scaledBalances
  have hb : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).balance k)
      = p.balance k := by
    have h1 : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).balance k)
        = update2 p.balance s.tokenIn a s.tokenOut b k := Sol_pool_bal _ _ _
    rw [h1]
    exact Sol_up_other _ _ _ _ _ _ hki hkj
  have hr : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).rate k)
      = p.rate k := Sol_pool_rate _ _ _
  rw [hb, hr]

theorem Sol_scaled_in (p : Pool) (a b : Nat) (s : Swap) :
    scaledBalances { p with balance := update2 p.balance s.tokenIn a s.tokenOut b } s.tokenIn
      = scaleDown a (p.rate s.tokenIn) := by
  unfold scaledBalances
  have hb : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).balance s.tokenIn) = a := by
    have h : update2 p.balance s.tokenIn a s.tokenOut b s.tokenIn = a :=
      Sol_up_in _ _ _ _ _
    have heq : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).balance s.tokenIn)
        = update2 p.balance s.tokenIn a s.tokenOut b s.tokenIn := Sol_pool_bal _ _ _
    rw [heq]
    exact h
  have hr : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).rate s.tokenIn)
      = p.rate s.tokenIn := Sol_pool_rate _ _ _
  rw [hb, hr]

theorem Sol_scaled_out (p : Pool) (a b : Nat) (s : Swap) (hji : s.tokenOut ≠ s.tokenIn) :
    scaledBalances { p with balance := update2 p.balance s.tokenIn a s.tokenOut b } s.tokenOut
      = scaleDown b (p.rate s.tokenOut) := by
  unfold scaledBalances
  have hb : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).balance s.tokenOut) = b := by
    have h : update2 p.balance s.tokenIn a s.tokenOut b s.tokenOut = b :=
      Sol_up_out _ _ _ _ _ hji
    have heq : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).balance s.tokenOut)
        = update2 p.balance s.tokenIn a s.tokenOut b s.tokenOut := Sol_pool_bal _ _ _
    rw [heq]
    exact h
  have hr : (({ p with balance := update2 p.balance s.tokenIn a s.tokenOut b } : Pool).rate s.tokenOut)
      = p.rate s.tokenOut := Sol_pool_rate _ _ _
  rw [hb, hr]

theorem Sol_givenIn_value_le (m : PoolMath) (p p' : Pool) (s : Swap) (c X Y : Nat)
    (wb : WellBehaved m p.n)
    (hne : s.tokenIn ≠ s.tokenOut) (hin : s.tokenIn < p.n) (hout : s.tokenOut < p.n)
    (hYeq : Y = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut X)
    (hX : X * ONE ≤ s.amount * p.rate s.tokenIn)
    (hY : c * p.rate s.tokenOut ≤ Y * ONE)
    (hp' : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - c) }) :
    value m p ≤ value m p' := by
  have hInv1 : m.invariant (scaledBalances p)
      ≤ m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + X) s.tokenOut ((scaledBalances p) s.tokenOut - Y)) := by
    have h := (wb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut X hne hin hout).2
    rw [← hYeq] at h
    exact h
  have hdom : ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + X) s.tokenOut ((scaledBalances p) s.tokenOut - Y) k
      ≤ scaledBalances p' k := by
    intro k hk
    by_cases hki : k = s.tokenIn
    · subst hki
      have hmid : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + X) s.tokenOut ((scaledBalances p) s.tokenOut - Y) s.tokenIn
          = (scaledBalances p) s.tokenIn + X := Sol_up_in _ _ _ _ _
      have hpk : scaledBalances p' s.tokenIn
          = scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := by
        rw [hp']
        exact Sol_scaled_in _ _ _ _
      rw [hmid, hpk]
      have hP : (scaledBalances p) s.tokenIn * ONE ≤ p.balance s.tokenIn * p.rate s.tokenIn := Sol_bmul_le _ _
      have hsum : ((scaledBalances p) s.tokenIn + X) * ONE
          ≤ (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn := by
        have e1 : ((scaledBalances p) s.tokenIn + X) * ONE
          = (scaledBalances p) s.tokenIn * ONE + X * ONE := Nat.add_mul _ _ _
        have e2 : (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn
          = p.balance s.tokenIn * p.rate s.tokenIn + s.amount * p.rate s.tokenIn := Nat.add_mul _ _ _
        rw [e1, e2]
        exact Nat.add_le_add hP hX
      exact Sol_le_floor_of_mul_le _ _ hsum
    · by_cases hkj : k = s.tokenOut
      · subst hkj
        have hmid : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + X) s.tokenOut ((scaledBalances p) s.tokenOut - Y) s.tokenOut
            = (scaledBalances p) s.tokenOut - Y := Sol_up_out _ _ _ _ _ (Ne.symm hne)
        have hpk : scaledBalances p' s.tokenOut
            = scaleDown (p.balance s.tokenOut - c) (p.rate s.tokenOut) := by
          rw [hp']
          exact Sol_scaled_out _ _ _ _ (Ne.symm hne)
        rw [hmid, hpk]
        have hbONE : (scaledBalances p) s.tokenOut * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := Sol_bmul_le _ _
        have e1 : ((scaledBalances p) s.tokenOut - Y) * ONE
            = (scaledBalances p) s.tokenOut * ONE - Y * ONE := Nat.sub_mul _ _ _
        have e2 : (p.balance s.tokenOut - c) * p.rate s.tokenOut
            = p.balance s.tokenOut * p.rate s.tokenOut - c * p.rate s.tokenOut := Nat.sub_mul _ _ _
        have hle_sub : (scaledBalances p) s.tokenOut * ONE - Y * ONE
            ≤ p.balance s.tokenOut * p.rate s.tokenOut - c * p.rate s.tokenOut :=
          Sol_sub_le _ _ _ _ hbONE hY
        have hneed : ((scaledBalances p) s.tokenOut - Y) * ONE
            ≤ (p.balance s.tokenOut - c) * p.rate s.tokenOut := by
          rw [e1, e2]; exact hle_sub
        exact Sol_le_floor_of_mul_le _ _ hneed
      · have hmid : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + X) s.tokenOut ((scaledBalances p) s.tokenOut - Y) k
            = (scaledBalances p) k := Sol_up_other _ _ _ _ _ _ hki hkj
        have hpk : scaledBalances p' k = scaleDown (p.balance k) (p.rate k) := by
          rw [hp']
          exact Sol_scaled_other _ _ _ _ _ hki hkj
        rw [hmid, hpk]
        exact Nat.le_refl _
  have hInv2 := wb.monotone _ _ hdom
  unfold value
  rw [hp'] at hInv2 ⊢
  exact Nat.le_trans hInv1 hInv2

theorem Sol_givenOut_value_le (m : PoolMath) (p p' : Pool) (s : Swap) (c X Y : Nat)
    (wb : WellBehaved m p.n)
    (hne : s.tokenIn ≠ s.tokenOut) (hin : s.tokenIn < p.n) (hout : s.tokenOut < p.n)
    (hYeq : Y = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut X)
    (hXlt : X < (scaledBalances p) s.tokenOut)
    (hYc : Y * ONE ≤ c * p.rate s.tokenIn)
    (hXge : s.amount * p.rate s.tokenOut ≤ X * ONE)
    (hp' : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) }) :
    value m p ≤ value m p' := by
  have hInv1 : m.invariant (scaledBalances p)
      ≤ m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + Y) s.tokenOut ((scaledBalances p) s.tokenOut - X)) := by
    have h := wb.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut X hne hin hout hXlt
    rw [← hYeq] at h
    exact h
  have hdom : ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + Y) s.tokenOut ((scaledBalances p) s.tokenOut - X) k
      ≤ scaledBalances p' k := by
    intro k hk
    by_cases hki : k = s.tokenIn
    · subst hki
      have hmid : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + Y) s.tokenOut ((scaledBalances p) s.tokenOut - X) s.tokenIn
          = (scaledBalances p) s.tokenIn + Y := Sol_up_in _ _ _ _ _
      have hpk : scaledBalances p' s.tokenIn
          = scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := by
        rw [hp']
        exact Sol_scaled_in _ _ _ _
      rw [hmid, hpk]
      have hbONE : (scaledBalances p) s.tokenIn * ONE ≤ p.balance s.tokenIn * p.rate s.tokenIn := Sol_bmul_le _ _
      have hsum : ((scaledBalances p) s.tokenIn + Y) * ONE
          ≤ (p.balance s.tokenIn + c) * p.rate s.tokenIn := by
        have e1 : ((scaledBalances p) s.tokenIn + Y) * ONE
          = (scaledBalances p) s.tokenIn * ONE + Y * ONE := Nat.add_mul _ _ _
        have e2 : (p.balance s.tokenIn + c) * p.rate s.tokenIn
          = p.balance s.tokenIn * p.rate s.tokenIn + c * p.rate s.tokenIn := Nat.add_mul _ _ _
        rw [e1, e2]
        exact Nat.add_le_add hbONE hYc
      exact Sol_le_floor_of_mul_le _ _ hsum
    · by_cases hkj : k = s.tokenOut
      · subst hkj
        have hmid : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + Y) s.tokenOut ((scaledBalances p) s.tokenOut - X) s.tokenOut
            = (scaledBalances p) s.tokenOut - X := Sol_up_out _ _ _ _ _ (Ne.symm hne)
        have hpk : scaledBalances p' s.tokenOut
            = scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
          rw [hp']
          exact Sol_scaled_out _ _ _ _ (Ne.symm hne)
        rw [hmid, hpk]
        have hbONE : (scaledBalances p) s.tokenOut * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := Sol_bmul_le _ _
        have e1 : ((scaledBalances p) s.tokenOut - X) * ONE
            = (scaledBalances p) s.tokenOut * ONE - X * ONE := Nat.sub_mul _ _ _
        have e2 : (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut
            = p.balance s.tokenOut * p.rate s.tokenOut - s.amount * p.rate s.tokenOut := Nat.sub_mul _ _ _
        have hle_sub : (scaledBalances p) s.tokenOut * ONE - X * ONE
            ≤ p.balance s.tokenOut * p.rate s.tokenOut - s.amount * p.rate s.tokenOut :=
          Sol_sub_le _ _ _ _ hbONE hXge
        have hneed : ((scaledBalances p) s.tokenOut - X) * ONE
            ≤ (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut := by
          rw [e1, e2]; exact hle_sub
        exact Sol_le_floor_of_mul_le _ _ hneed
      · have hmid : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + Y) s.tokenOut ((scaledBalances p) s.tokenOut - X) k
            = (scaledBalances p) k := Sol_up_other _ _ _ _ _ _ hki hkj
        have hpk : scaledBalances p' k = scaleDown (p.balance k) (p.rate k) := by
          rw [hp']
          exact Sol_scaled_other _ _ _ _ _ hki hkj
        rw [hmid, hpk]
        exact Nat.le_refl _
  have hInv2 := wb.monotone _ _ hdom
  unfold value
  rw [hp'] at hInv2 ⊢
  exact Nat.le_trans hInv1 hInv2

theorem Sol_combine_var (Y Yup c r d : Nat)
    (h1 : Y * ONE ≤ Yup * r) (h2 : Yup * ONE ≤ c * d) :
    Y * ONE * ONE ≤ c * d * r := by
  have e1 : Y * ONE * ONE ≤ Yup * r * ONE :=
    Nat.mul_le_mul h1 (Nat.le_refl _)
  have e2 : Yup * r * ONE = Yup * ONE * r := by
    calc Yup * r * ONE = Yup * (r * ONE) := by rw [Nat.mul_assoc]
      _ = Yup * (ONE * r) := by rw [Nat.mul_comm r ONE]
      _ = Yup * ONE * r := by rw [← Nat.mul_assoc]
  rw [e2] at e1
  have e3 : Yup * ONE * r ≤ c * d * r :=
    Nat.mul_le_mul h2 (Nat.le_refl _)
  exact Nat.le_trans e1 e3

theorem Sol_strip_var (Y c r d : Nat)
    (h : Y * ONE * ONE ≤ c * d * r) (hd : d ≤ ONE) :
    Y * ONE ≤ c * r := by
  have hmid : c * d * r ≤ c * ONE * r :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) hd) (Nat.le_refl _)
  have hle : Y * ONE * ONE ≤ c * ONE * r := Nat.le_trans h hmid
  have e1 : c * ONE * r = (c * r) * ONE := by
    calc c * ONE * r = c * (ONE * r) := by rw [Nat.mul_assoc]
      _ = c * (r * ONE) := by rw [Nat.mul_comm ONE r]
      _ = (c * r) * ONE := by rw [← Nat.mul_assoc]
  rw [e1] at hle
  have e2 : Y * ONE * ONE = (Y * ONE) * ONE := rfl
  rw [e2] at hle
  exact Sol_cancel_one_mul _ _ hle

theorem Sol_mul_lt_of_pos_right {a b k : Nat} (h : a < b) (hk : 0 < k) :
    a * k < b * k := by
  have hle : a ≤ b := Nat.le_of_lt h
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  have hcpos : 0 < c := by omega
  obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have hb : b = a + (d + 1) := by omega
  have e : b * k = a * k + (d + 1) * k := by
    rw [hb, Nat.add_mul]
  have hpos : 0 < (d + 1) * k := Nat.mul_pos (by omega) hk
  omega

def onSwap : Impl := fun m p s =>
  if s.kind = Kind.givenIn then
    if p.rate s.tokenOut = 0 then none
    else some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)
  else
    if p.rate s.tokenIn = 0 then none
    else if ONE ≤ p.fee then none
    else if scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) then
      some (SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee))
    else none

theorem Sol_rateOut_ne_of_some_in {m p s y} (h : onSwap m p s = some y)
    (hk : s.kind = Kind.givenIn) : p.rate s.tokenOut ≠ 0 := by
  intro hr
  simp [onSwap, hk, hr] at h

theorem Sol_y_eq_of_some_in {m p s y} (h : onSwap m p s = some y)
    (hk : s.kind = Kind.givenIn) :
    y = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := by
  have hrne : p.rate s.tokenOut ≠ 0 := Sol_rateOut_ne_of_some_in h hk
  simp [onSwap, hk, hrne] at h
  exact h.symm

theorem Sol_rateIn_ne_of_some_out {m p s c} (h : onSwap m p s = some c)
    (hkNe : ¬ s.kind = Kind.givenIn) : p.rate s.tokenIn ≠ 0 ∧ ¬ ONE ≤ p.fee ∧
    scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := by
  have hrne : p.rate s.tokenIn ≠ 0 := by
    intro hr
    have hnone : onSwap m p s = none := by simp [onSwap, hkNe, hr]
    rw [hnone] at h
    cases h
  have hnle : ¬ ONE ≤ p.fee := by
    intro hf
    have hnone : onSwap m p s = none := by simp [onSwap, hkNe, hrne, hf]
    rw [hnone] at h
    cases h
  have hX : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := by
    by_cases hXc : scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut)
    · exact hXc
    · have hnone : onSwap m p s = none := by simp [onSwap, hkNe, hrne, hnle, hXc]
      rw [hnone] at h
      cases h
  exact ⟨hrne, hnle, hX⟩

theorem Sol_c_eq_of_some_out {m p s c} (h : onSwap m p s = some c)
    (hkNe : ¬ s.kind = Kind.givenIn) :
    c = SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) := by
  have ht := Sol_rateIn_ne_of_some_out h hkNe
  obtain ⟨hr, hf, hX⟩ := ht
  simp [onSwap, hkNe, hr, hf, hX] at h
  exact h.symm

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s wb hk hv hrate hfee
  have hrne : p.rate s.tokenOut ≠ 0 := Nat.ne_of_gt hrate
  have hImpl : onSwap m p s =
      some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by
    simp [onSwap, hk, hrne]
  have hne : s.tokenIn ≠ s.tokenOut := hv.1
  have hin : s.tokenIn < p.n := hv.2.1
  have hout : s.tokenOut < p.n := hv.2.2
  have hYle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
      ≤ (scaledBalances p) s.tokenOut :=
    (wb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hne hin hout).1
  have hsc : (scaledBalances p) s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
  rw [hsc] at hYle
  have hle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
        ≤ (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE :=
    Nat.mul_le_mul hYle (Nat.le_refl _)
  have hle2 : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE
        ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
    Sol_div_mul_le_self _ _
  have hYONE_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
    Nat.le_trans hle hle2
  have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE /
        p.rate s.tokenOut ≤ p.balance s.tokenOut * p.rate s.tokenOut / p.rate s.tokenOut :=
    Nat.div_le_div_right hYONE_le
  have h2 : p.balance s.tokenOut * p.rate s.tokenOut / p.rate s.tokenOut
        = p.balance s.tokenOut := Nat.mul_div_cancel _ hrate
  rw [h2] at h1
  have eAO : amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)
      = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut := by
    unfold amountOut
    rw [hk]
  have hleAO : amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)
      ≤ p.balance s.tokenOut := by
    rw [eAO]
    exact h1
  have hstep : step onSwap m p s =
      settle p s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by
    unfold step
    simp [hv, hImpl]
  rw [hstep]
  simp [settle, eAO, h1]

theorem scaleUp_ge_of_gt_balance_aux {a b r : Nat} (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  unfold scaleUp scaleDown at h
  by_cases hle : a ≤ b
  · exact hle
  · have hlt : b < a := by omega
    have hleBA : b ≤ a := by omega
    have hle0 : b * r ≤ a * r := Nat.mul_le_mul hleBA (Nat.le_refl _)
    have hleA : b * r ≤ a * r + (ONE - 1) := Nat.le_trans hle0 (Nat.le_add_right _ _)
    have hdiv : b * r / ONE ≤ (a * r + (ONE - 1)) / ONE := Nat.div_le_div_right hleA
    omega

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s wb hk hv hrate hfee hX
  have hrne : p.rate s.tokenIn ≠ 0 := Nat.ne_of_gt hrate
  have hkNe : ¬ s.kind = Kind.givenIn := by rw [hk]; decide
  have hfeeF : ¬ ONE ≤ p.fee := Nat.not_le_of_gt hfee
  have hEq : onSwap m p s = some (SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) := by
    simp [onSwap, hk, hrne, hfeeF, hX]
  have hle : s.amount ≤ p.balance s.tokenOut := scaleUp_ge_of_gt_balance_aux hX
  have eAO : amountOut s (SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) = s.amount := by
    unfold amountOut
    rw [hk]
  have hstep : step onSwap m p s =
      settle p s (SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee)) := by
    unfold step
    simp [hv, hEq]
  rw [hstep]
  simp [settle, eAO, hle]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hk hv hImpl
  have heq := Sol_y_eq_of_some_in hImpl hk
  rw [heq]
  have hle := Sol_div_mul_le_self
    (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE)
    (p.rate s.tokenOut)
  calc (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE /
        p.rate s.tokenOut) * p.rate s.tokenOut
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := hle
    _ = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
        rw [Nat.mul_comm]

theorem netLess_le_net' (p : Pool) (s : Swap) : netInLessOneDown p s ≤ netInDown p s := by
  unfold netInLessOneDown netInDown
  exact Nat.div_le_div_right (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.le_refl _))

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hk hv hImpl
  have hrne := Sol_rateOut_ne_of_some_in hImpl hk
  have hrate : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrne
  have heq := Sol_y_eq_of_some_in hImpl hk
  obtain ⟨h1, _⟩ := hmono
  have hle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
    h1 _ _ _ _ _ (netLess_le_net' p s)
  have hlt : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      < (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1) * p.rate s.tokenOut :=
    Sol_lt_succ_mul_self _ _ hrate
  have h2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) * ONE
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    Nat.mul_le_mul hle (Nat.le_refl _)
  have h3 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
    have e : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
        = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) * ONE := Nat.mul_comm _ _
    rw [e]
    exact h2
  have hlt2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      < (y + 1) * p.rate s.tokenOut := by
    have hlt' := hlt
    rw [← heq] at hlt'
    exact hlt'
  exact Sol_lt_of_le_of_lt h3 hlt2

theorem Sol_three_mul_comm (Y : Nat) : ONE * ONE * Y = Y * ONE * ONE := by
  calc ONE * ONE * Y = Y * (ONE * ONE) := by rw [Nat.mul_comm]
    _ = Y * ONE * ONE := by rw [Nat.mul_assoc]

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hk hv hImpl
  have hkNe : ¬ s.kind = Kind.givenIn := by rw [hk]; decide
  have ⟨hrne, hnle, hX⟩ := Sol_rateIn_ne_of_some_out hImpl hkNe
  have heq := Sol_c_eq_of_some_out hImpl hkNe
  have hrate : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
  have hfee : p.fee < ONE := Nat.lt_of_not_ge hnle
  have hcomp : 0 < ONE - p.fee := Nat.sub_pos_of_lt hfee
  rw [heq]
  unfold outPrice
  have h1 : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE
      ≤ SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn :=
    SolCeil_mul_ge _ _ hrate
  have h2 : SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE
      ≤ SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) * (ONE - p.fee) :=
    SolCeil_mul_ge _ _ hcomp
  have hcomb := Sol_combine_var _ _ _ _ _ h1 h2
  have efinal : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))
      = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE :=
    Sol_three_mul_comm _
  rw [efinal]
  exact hcomb

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c hmono hk hv hImpl
  have hkNe : ¬ s.kind = Kind.givenIn := by rw [hk]; decide
  have ⟨hrne, hnle, hX⟩ := Sol_rateIn_ne_of_some_out hImpl hkNe
  have heq := Sol_c_eq_of_some_out hImpl hkNe
  have hrate : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
  have hfee : p.fee < ONE := Nat.lt_of_not_ge hnle
  have hcomp : 0 < ONE - p.fee := Nat.sub_pos_of_lt hfee
  rw [heq]
  unfold outPrice
  have hub : SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn
      ≤ m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn :=
    SolCeil_ub _ _
  by_cases hUz : SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE = 0
  · have hc0 : SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) = 0 :=
      ((SolCeil_eq_zero_iff _ _ hcomp).mpr hUz)
    rw [hc0]
    simp only [Nat.zero_sub, Nat.zero_mul]
    have hpos1 : 0 < ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn :=
      Nat.lt_of_lt_of_le hrate (Nat.le_add_left _ _)
    have hpos2 : 0 < ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) :=
      Nat.mul_pos Sol_ONE_pos hpos1
    exact hpos2
  · have hUpos : 0 < SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE :=
      Nat.pos_of_ne_zero hUz
    have hlt2 : (SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) - 1) * (ONE - p.fee)
        < SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE :=
      SolCeil_pred_lt _ _ hcomp hUpos
    have hle_mul_lt : (SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) - 1) * (ONE - p.fee) * p.rate s.tokenIn
        < (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) * p.rate s.tokenIn :=
      Sol_mul_lt_of_pos_right hlt2 hrate
    have eU : SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn
        = (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn) * ONE := by
      calc SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE * p.rate s.tokenIn
          = SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * (ONE * p.rate s.tokenIn) := by rw [Nat.mul_assoc]
        _ = SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * (p.rate s.tokenIn * ONE) := by rw [Nat.mul_comm ONE (p.rate s.tokenIn)]
        _ = (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn) * ONE := by rw [← Nat.mul_assoc]
    rw [eU] at hle_mul_lt
    have hleU : (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn) * ONE
        ≤ (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
      Nat.mul_le_mul hub (Nat.le_refl _)
    have hfinal : (SolCeil (SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE) (ONE - p.fee) - 1) * (ONE - p.fee) * p.rate s.tokenIn
        < (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
      Sol_lt_of_lt_of_le hle_mul_lt hleU
    have eYO : ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))
        = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE :=
      Nat.mul_comm _ _
    have eComm : (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE
        = ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) := by
      rw [eYO]
      exact Nat.mul_comm _ _
    rw [eComm] at hfinal
    exact hfinal

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' wb hstep
  unfold step at hstep
  by_cases hv : Valid p s
  · simp [hv] at hstep
    cases hQ : onSwap m p s with
    | none => simp [hQ] at hstep
    | some c =>
      simp [hQ] at hstep
      have hs := Sol_settle_some hstep
      obtain ⟨hleAO0, hp'_eq0⟩ := hs
      have hne : s.tokenIn ≠ s.tokenOut := hv.1
      have hin : s.tokenIn < p.n := hv.2.1
      have hout : s.tokenOut < p.n := hv.2.2
      by_cases hkIn : s.kind = Kind.givenIn
      · have hImplY := Sol_y_eq_of_some_in hQ hkIn
        have hAin : amountIn s c = s.amount := by unfold amountIn; rw [hkIn]
        have hAout : amountOut s c = c := by unfold amountOut; rw [hkIn]
        have hp'_eq : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - c) } := by
          rw [hAin, hAout] at hp'_eq0
          exact hp'_eq0
        have hxONE : netInDown p s * ONE ≤ s.amount * p.rate s.tokenIn :=
          Sol_netIn_le_pool p s
        have hcYN : c * p.rate s.tokenOut
            ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
          rw [hImplY]
          exact Sol_div_mul_le_self _ _
        exact Sol_givenIn_value_le m p p' s c (netInDown p s)
          (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))
          wb hne hin hout rfl hxONE hcYN hp'_eq
      · have hrr := Sol_rateIn_ne_of_some_out hQ hkIn
        obtain ⟨hrne, hnle, hXlt⟩ := hrr
        have heq := Sol_c_eq_of_some_out hQ hkIn
        have hrateIn : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
        have hfee : p.fee < ONE := Nat.lt_of_not_ge hnle
        have hkOut : s.kind = Kind.givenOut := by
          match h : s.kind with
          | Kind.givenIn => exact absurd h hkIn
          | Kind.givenOut => rfl
        have hAin : amountIn s c = c := by unfold amountIn; rw [hkOut]
        have hAout : amountOut s c = s.amount := by unfold amountOut; rw [hkOut]
        have hp'_eq : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) } := by
          rw [hAin, hAout] at hp'_eq0
          exact hp'_eq0
        have hXltB : scaleUp s.amount (p.rate s.tokenOut) < (scaledBalances p) s.tokenOut := by
          have hsd : scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) = (scaledBalances p) s.tokenOut := rfl
          rw [← hsd]
          exact hXlt
        have hYc : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE ≤ c * p.rate s.tokenIn := by
          have hyup_ge : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE
              ≤ SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * p.rate s.tokenIn :=
            SolCeil_mul_ge _ _ hrateIn
          have hc_ge : SolCeil (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) (p.rate s.tokenIn) * ONE
              ≤ c * (ONE - p.fee) := by
            rw [heq]
            exact SolCeil_mul_ge _ _ (Nat.sub_pos_of_lt hfee)
          have hYmul : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE * ONE
              ≤ c * (ONE - p.fee) * p.rate s.tokenIn :=
            Sol_combine_var _ _ _ _ _ hyup_ge hc_ge
          exact Sol_strip_var _ _ _ _ hYmul (Nat.sub_le _ _)
        have hXge : s.amount * p.rate s.tokenOut
            ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE :=
          Sol_scaleUp_mul_ge _ _
        exact Sol_givenOut_value_le m p p' s c (scaleUp s.amount (p.rate s.tokenOut))
          (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)))
          wb hne hin hout rfl hXltB hYc hXge hp'_eq
  · simp [hv] at hstep

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' wb hrun
  induction ss generalizing p with
  | nil =>
    have e : run onSwap m p [] = some p := rfl
    rw [e] at hrun
    have h : p = p' := Option.some_inj.mp hrun
    subst h
    exact Nat.le_refl _
  | cons s ss ih =>
    have heq : run onSwap m p (s :: ss)
        = match step onSwap m p s with | some mid => run onSwap m mid ss | none => none := rfl
    cases hmid : step onSwap m p s with
    | none =>
      simp only [heq, hmid] at hrun
      cases hrun
    | some mid =>
      simp only [heq, hmid] at hrun
      have hle1 : value m p ≤ value m mid :=
        req_swap_keeps_value m p s mid wb hmid
      have hmid_n : mid.n = p.n := Sol_step_n onSwap m p s mid hmid
      have wb_mid : WellBehaved m mid.n := by rw [hmid_n]; exact wb
      have hle2 : value m mid ≤ value m p' := ih mid wb_mid hrun
      exact Nat.le_trans hle1 hle2

end BalancerSwap

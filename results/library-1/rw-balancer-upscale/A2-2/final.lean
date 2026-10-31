import BalancerSwap.Spec
namespace BalancerSwap

def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn =>
    if p.fee < ONE ∧ 0 < p.rate s.tokenOut then
      let amountScaled := netInDown p s
      let outScaled := m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut amountScaled
      some (outScaled * ONE / p.rate s.tokenOut)
    else none
  | .givenOut =>
    if p.fee < ONE ∧ 0 < p.rate s.tokenIn then
      let amountScaled := scaleUp s.amount (p.rate s.tokenOut)
      let b := scaledBalances p
      if amountScaled < b s.tokenOut then
        let price := m.inGivenOut b s.tokenIn s.tokenOut amountScaled
        let den := (ONE - p.fee) * p.rate s.tokenIn
        some ((ONE * ONE * price + den - 1) / den)
      else none
    else none

theorem tmp1 : ∀ (m : PoolMath) (p : Pool) (s : Swap),
  s.kind = Kind.givenIn → p.fee < ONE → 0 < p.rate s.tokenOut →
  onSwap m p s = some ((m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) / p.rate s.tokenOut) := by
  intro m p s hk hf hr
  unfold onSwap
  rw [hk]
  simp [hf, hr]

theorem tmp_ONE_posC : 0 < ONE := by unfold ONE; decide

theorem tmp_le_ceil_mulC : ∀ (N d : Nat), 0 < d → N ≤ (N + d - 1) / d * d := by
  intro N d hd
  by_cases hN : N = 0
  · subst hN; simp
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hdiv := Nat.div_add_mod (N + d - 1) d
    rw [Nat.mul_comm] at hdiv
    have hmod : (N + d - 1) % d < d := Nat.mod_lt _ hd
    have hNd : N ≤ N + d - 1 := by omega
    have hr : (N + d - 1) % d ≤ d - 1 := by omega
    omega

theorem tmp_check_names : True := by
  have h1 : ∀ (a d : Nat), a / d * d ≤ a := fun a d => Nat.div_mul_le_self a d
  have h2 : ∀ (a b c : Nat), a * c ≤ b * c → 0 < c → a ≤ b := fun a b c h hc => Nat.le_of_mul_le_mul_right h hc
  trivial

theorem scaleDown_ge_scaleUp_of_lt_aux : ∀ (a b r : Nat),
  scaleUp a r < scaleDown b r → a ≤ b := by
  intro a b r h
  by_cases hle : a ≤ b
  · exact hle
  · have hb_le : b ≤ a := by omega
    have hmul : b * r ≤ a * r := Nat.mul_le_mul_right r hb_le
    have hmul2 : b * r ≤ a * r + (ONE - 1) := Nat.le_trans hmul (Nat.le_add_right _ _)
    have hdiv : b * r / ONE ≤ (a * r + (ONE - 1)) / ONE := Nat.div_le_div_right hmul2
    unfold scaleUp scaleDown at h
    omega

theorem req_given_in_pays_at_least_aux1 : ∀ (a d : Nat), 0 < d → a < (a / d + 1) * d := by
  intro a d hd
  have h2 : a % d < d := Nat.mod_lt a hd
  have h3 := Nat.div_add_mod a d
  have h3' : a / d * d + a % d = a := by
    have hc : d * (a / d) = a / d * d := Nat.mul_comm _ _
    omega
  have h4 : (a / d + 1) * d = a / d * d + d := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

theorem req_given_out_charges_at_most_aux : ∀ (c den N R : Nat),
  0 < den → den ≤ R → (N + den - 1) / den = c →
  0 < R → (c - 1) * den < N + R := by
  intro c den N R hden hdenR hceq hR
  have hdiv : (N + den - 1) / den * den ≤ N + den - 1 :=
    Nat.div_mul_le_self _ _
  rw [hceq] at hdiv
  have hceil := tmp_le_ceil_mulC N den hden
  rw [hceq] at hceil
  by_cases hc : c = 0
  · subst hc
    simp
    omega
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    have hcc2 : c - 1 + 1 = c := by omega
    have hadd : (c - 1 + 1) * den = (c - 1) * den + 1 * den := Nat.add_mul _ _ _
    rw [hcc2] at hadd
    rw [Nat.one_mul] at hadd
    omega

theorem helper_test_snippet : True := by trivial

theorem helper_test3 : 0 < 1 := by decide

theorem helper_ONE_pos : 0 < ONE := by unfold ONE; decide

theorem helper_div_add_test : ∀ (a b n : Nat), 0 < n → a / n + b / n ≤ (a + b) / n := by
  intro a b n hn
  have h1 : a / n * n ≤ a := Nat.div_mul_le_self a n
  have h2 : b / n * n ≤ b := Nat.div_mul_le_self b n
  have h3 : (a / n + b / n) * n ≤ a + b := by
    rw [Nat.add_mul]
    omega
  have h4 : (a / n + b / n) ≤ (a + b) / n := (Nat.le_div_iff_mul_le hn).mpr h3
  exact h4

theorem helper_check_lib_sig : True := by trivial

theorem helper_batch_n_ok : ∀ (p : Pool) (s : Swap) (q : Nat) (p' : Pool), settle p s q = some p' → p'.n = p.n := by
  intro p s q p' h
  unfold settle at h
  by_cases hc : amountOut s q ≤ p.balance s.tokenOut
  · simp [hc] at h
    subst h
    rfl
  · simp [hc] at h

theorem helper_batch_n_step : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool), step onSwap m p s = some p' → p'.n = p.n := by
  intro m p s p' h
  unfold step at h
  by_cases hv : Valid p s
  · simp [hv] at h
    cases hc : onSwap m p s with
    | none => simp [hc] at h
    | some c =>
      simp [hc] at h
      exact helper_batch_n_ok p s c p' h
  · simp [hv] at h

theorem helper_batch_run_n2 : ∀ (m : PoolMath) (p : Pool) (ss : List Swap) (p' : Pool), run onSwap m p ss = some p' → p'.n = p.n := by
  intro m p ss
  induction ss generalizing p with
  | nil =>
    intro p' h
    simp [run] at h
    subst h
    rfl
  | cons s ss ih =>
    intro p' h
    unfold run at h
    cases hst : step onSwap m p s with
    | none => simp [hst] at h
    | some pm =>
      simp [hst] at h
      have hn1 : pm.n = p.n := helper_batch_n_step m p s pm hst
      have hn2 : p'.n = pm.n := ih pm p' h
      omega

theorem helper_floor_add2 : ∀ (A C n : Nat), 0 < n → A / n + C / n ≤ (A + C) / n := by
  intro A C n hn
  have h1 : A / n * n ≤ A := Nat.div_mul_le_self A n
  have h2 : C / n * n ≤ C := Nat.div_mul_le_self C n
  have h3 : (A / n + C / n) * n ≤ A + C := by
    rw [Nat.add_mul]; omega
  exact (Nat.le_div_iff_mul_le hn).mpr h3

theorem helper_div_div_check : ∀ (X : Nat), X / (ONE * ONE) = (X / ONE) / ONE := by
  intro X
  rw [Nat.div_div_eq_div_mul]

theorem helper_sub_mul_check : ∀ (a b n : Nat), (a - b) * n = a * n - b * n := by
  intro a b n; exact Nat.sub_mul a b n

theorem helper_add_mul_check : ∀ (a b n : Nat), (a + b) * n = a * n + b * n := by
  intro a b n; exact Nat.add_mul a b n

theorem helper_le_div_check : ∀ (a b n : Nat), 0 < n → (a ≤ b → a / n ≤ b / n) := by
  intro a b n hn h; exact Nat.div_le_div_right h

theorem helper_ONE_mul : ∀ (X : Nat), X * ONE / ONE = X := by
  intro X; exact Nat.mul_div_cancel X helper_ONE_pos

theorem helper_cancel_ceil : ∀ (C : Nat), (C * ONE) / (ONE * ONE) = C / ONE := by
  intro C
  have h1 : (C * ONE) / (ONE * ONE) = ((C * ONE) / ONE) / ONE := helper_div_div_check (C * ONE)
  rw [h1, helper_ONE_mul]

theorem helper_ac_test : ∀ (a b c : Nat), a * b * c = a * c * b := by
  intro a b c; ac_rfl

theorem helper_mul_le_left_test : ∀ (k a b : Nat), a ≤ b → k * a ≤ k * b := by
  intro k a b h
  exact Nat.mul_le_mul_left k h

theorem helper_gain_mul_le : ∀ (amt rate fee : Nat),
  amt * (ONE - fee) * rate ≤ amt * rate * ONE := by
  intro amt rate fee
  have h1 : amt * (ONE - fee) * rate = (amt * rate) * (ONE - fee) := by ac_rfl
  have h2 : amt * rate * ONE = (amt * rate) * ONE := rfl
  rw [h1, h2]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem helper_gainIn_dom3 : ∀ (bal amt rate fee : Nat),
  (amt * (ONE - fee) * rate / (ONE * ONE)) + (bal * rate / ONE) ≤ (bal + amt) * rate / ONE := by
  intro bal amt rate fee
  have hONE : 0 < ONE := helper_ONE_pos
  have hle : amt * (ONE - fee) * rate ≤ amt * rate * ONE := helper_gain_mul_le amt rate fee
  have h1 : amt * (ONE - fee) * rate / (ONE * ONE) ≤ amt * rate * ONE / (ONE * ONE) :=
    Nat.div_le_div_right hle
  have hmid : amt * rate * ONE / ONE = amt * rate :=
    Nat.mul_div_cancel _ hONE
  have hcan : amt * rate * ONE / (ONE * ONE) = amt * rate / ONE := by
    have h1 : amt * rate * ONE / (ONE * ONE) = ((amt * rate * ONE) / ONE) / ONE := by
      rw [Nat.div_div_eq_div_mul]
    rw [h1, hmid]
  have h2 : amt * (ONE - fee) * rate / (ONE * ONE) ≤ amt * rate / ONE := hcan ▸ h1
  have h3 : bal * rate / ONE + (amt * rate / ONE) ≤ (bal * rate + amt * rate) / ONE :=
    helper_floor_add2 _ _ _ hONE
  have h4 : (bal + amt) * rate = bal * rate + amt * rate := Nat.add_mul _ _ _
  have h4eq : (bal + amt) * rate / ONE = (bal * rate + amt * rate) / ONE := by rw [h4]
  omega



theorem plan0_scaleUp_mul_ge : ∀ (a r : Nat), a * r ≤ scaleUp a r * ONE := by
  intro a r
  have hONE : 0 < ONE := helper_ONE_pos
  have h : a * r + (ONE - 1) = a * r + ONE - 1 := by omega
  have heq : scaleUp a r = (a * r + ONE - 1) / ONE := by unfold scaleUp; rw [h]
  rw [heq]
  exact tmp_le_ceil_mulC _ _ hONE








theorem plan0_ceil_mul_ge : ∀ (N d : Nat), 0 < d → N ≤ (N + d - 1) / d * d := by
  intro N d hd
  exact tmp_le_ceil_mulC N d hd

theorem test_add_mul_div_eq : ∀ (A K : Nat), (A + K * ONE) / ONE = A / ONE + K := by
  intro A K
  unfold ONE
  omega







theorem plan1_le_ceil_mul : ∀ (n d : Nat), 0 < d → n ≤ (n + d - 1) / d * d := fun n d hd => tmp_le_ceil_mulC n d hd


theorem plan1_scaleUp_eq_ceil : ∀ (a r : Nat), scaleUp a r = (a * r + ONE - 1) / ONE := by
  intro a r
  have h : a * r + (ONE - 1) = a * r + ONE - 1 := by
    have hONE : 0 < ONE := helper_ONE_pos
    omega
  unfold scaleUp
  rw [h]


theorem plan1_one_pos : 0 < ONE := by unfold ONE; decide

theorem plan1_div_mod_eq : ∀ (m k : Nat), (m / k) * k + m % k = m := by
  intro m k
  have h := Nat.div_add_mod m k
  have hc : k * (m / k) = (m / k) * k := Nat.mul_comm _ _
  omega

theorem plan1_mod_lt_pos : ∀ (m k : Nat), 0 < k → m % k < k := by
  intro m k hk
  exact Nat.mod_lt m hk

theorem plan1_le_ceil_mul_proof : ∀ (n d : Nat), 0 < d → n ≤ (n + d - 1) / d * d := fun n d hd => tmp_le_ceil_mulC n d hd

theorem plan1_scaleUp_eq_ceil_fixed : ∀ (a r : Nat), scaleUp a r = (a * r + ONE - 1) / ONE := by
  intro a r
  have h : a * r + (ONE - 1) = a * r + ONE - 1 := by
    have hONE : 0 < ONE := helper_ONE_pos
    omega
  unfold scaleUp
  rw [h]

theorem plan1_use_fixed : ∀ (a r : Nat), scaleUp a r = (a * r + ONE - 1) / ONE :=
  fun a r => plan1_scaleUp_eq_ceil_fixed a r

theorem plan0_scaleUp_mul_ge_proof : ∀ (a r : Nat), a * r ≤ scaleUp a r * ONE := by
  intro a r
  rw [plan1_scaleUp_eq_ceil_fixed]
  exact plan1_le_ceil_mul _ _ helper_ONE_pos

theorem plan1_scaleUp_eq_ceil_check : ∀ (a r : Nat), scaleUp a r = (a * r + ONE - 1) / ONE := by
  intro a r
  have h : a * r + (ONE - 1) = a * r + ONE - 1 := by
    have hONE : 0 < ONE := helper_ONE_pos
    omega
  unfold scaleUp
  rw [h]

theorem plan0_scaleUp_mul_ge_fixed : ∀ (a r : Nat), a * r ≤ scaleUp a r * ONE := fun a r => plan0_scaleUp_mul_ge_proof a r

theorem plan0_scaleUp_selfcontained : ∀ (a r : Nat), a * r ≤ scaleUp a r * ONE := by
  intro a r
  have h : a * r + (ONE - 1) = a * r + ONE - 1 := by
    have hONE : 0 < ONE := helper_ONE_pos
    omega
  have heq : scaleUp a r = (a * r + ONE - 1) / ONE := by unfold scaleUp; rw [h]
  rw [heq]
  exact tmp_le_ceil_mulC _ _ helper_ONE_pos

theorem testSubLem : ∀ (a b c : Nat), a ≤ b + c → a - c ≤ b := by
  intro a b c h
  exact (Nat.sub_le_iff_le_add).mpr h

theorem plan0_scaleDown_sub_ge : ∀ (B y out r : Nat), y * r ≤ out * ONE → scaleDown B r - out ≤ scaleDown (B - y) r := by
  intro B y out r h
  unfold scaleDown
  by_cases hBy : y ≤ B
  · have hsub : (B - y) * r = B * r - y * r := Nat.sub_mul B y r
    rw [hsub]
    have hyr_le_Br : y * r ≤ B * r := Nat.mul_le_mul_right r hBy
    have hBr_le : B * r ≤ (B * r - y * r) + out * ONE := by omega
    have hdiv_mono : B * r / ONE ≤ ((B * r - y * r) + out * ONE) / ONE :=
      Nat.div_le_div_right hBr_le
    have hdiv_add : ((B * r - y * r) + out * ONE) / ONE = (B * r - y * r) / ONE + out :=
      Nat.add_mul_div_right _ _ helper_ONE_pos
    rw [hdiv_add] at hdiv_mono
    exact (Nat.sub_le_iff_le_add).mpr hdiv_mono
  · have hBy' : B < y := by omega
    have hsub0 : B - y = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hBy')
    rw [hsub0]
    simp only [Nat.zero_mul, Nat.zero_div]
    by_cases hr : r = 0
    · subst hr
      simp
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hBle : B * r ≤ out * ONE := by
        have h1 : (B + 1) * r ≤ y * r := Nat.mul_le_mul_right r hBy'
        have h2 : B * r + r ≤ y * r := by
          have heq : (B + 1) * r = B * r + r := by
            rw [Nat.add_mul, Nat.one_mul]
          omega
        omega
      have hdiv_le : B * r / ONE ≤ (out * ONE) / ONE := Nat.div_le_div_right hBle
      have hcancel : (out * ONE) / ONE = out := Nat.mul_div_cancel _ helper_ONE_pos
      omega

theorem plan0_scaleDown_add_net_ge : ∀ (B A r g : Nat), g ≤ ONE → scaleDown B r + A * g * r / (ONE * ONE) ≤ scaleDown (B + A) r := by
  intro B A r g hg
  unfold scaleDown
  have hONE : 0 < ONE := helper_ONE_pos
  have e1 : A * g * r = (A * r) * g := by ac_rfl
  have hle : A * g * r ≤ A * r * ONE := by
    rw [e1]
    exact Nat.mul_le_mul_left _ hg
  have h1 : A * g * r / (ONE * ONE) ≤ A * r * ONE / (ONE * ONE) :=
    Nat.div_le_div_right hle
  have hcan : A * r * ONE / (ONE * ONE) = A * r / ONE := helper_cancel_ceil (A * r)
  have h2 : A * g * r / (ONE * ONE) ≤ A * r / ONE := hcan ▸ h1
  have h3 : B * r / ONE + (A * r / ONE) ≤ (B * r + A * r) / ONE :=
    helper_floor_add2 _ _ _ hONE
  have h4 : (B + A) * r = B * r + A * r := Nat.add_mul _ _ _
  have h5 : B * r / ONE + A * g * r / (ONE * ONE) ≤ B * r / ONE + (A * r / ONE) :=
    Nat.add_le_add_left h2 _
  have h6 : B * r / ONE + (A * r / ONE) ≤ (B + A) * r / ONE := by
    rw [h4]
    exact h3
  exact Nat.le_trans h5 h6

theorem plan0_scaleDown_add_price_ge : ∀ (B c r g price : Nat), g ≤ ONE → ONE * ONE * price ≤ c * g * r → scaleDown B r + price ≤ scaleDown (B + c) r := by
  intro B c r g price hg hcov
  unfold scaleDown
  have hONE : 0 < ONE := helper_ONE_pos
  have e1 : c * g * r = (c * r) * g := by ac_rfl
  have e2 : c * r * ONE = (c * r) * ONE := rfl
  have hle1 : (c * r) * g ≤ (c * r) * ONE := Nat.mul_le_mul_left _ hg
  have hle2 : c * g * r ≤ c * r * ONE := by rw [e1]; exact hle1
  have htrans : ONE * ONE * price ≤ c * r * ONE := Nat.le_trans hcov hle2
  have hONEprice : ONE * price ≤ c * r := by
    have hrew : ONE * ONE * price = (ONE * price) * ONE := by ac_rfl
    have hrew2 : c * r * ONE = (c * r) * ONE := rfl
    rw [hrew] at htrans
    exact Nat.le_of_mul_le_mul_right htrans hONE
  have hprice_le : price ≤ c * r / ONE := by
    have hmul : price * ONE ≤ c * r := by
      have hc : price * ONE = ONE * price := Nat.mul_comm _ _
      rw [hc]; exact hONEprice
    have h := (Nat.le_div_iff_mul_le hONE).mpr hmul
    exact h
  have hfloor : B * r / ONE + (c * r / ONE) ≤ (B * r + c * r) / ONE :=
    helper_floor_add2 _ _ _ hONE
  have hadd : (B + c) * r = B * r + c * r := Nat.add_mul _ _ _
  rw [hadd]
  have hmono : B * r / ONE + price ≤ B * r / ONE + (c * r / ONE) :=
    Nat.add_le_add_left hprice_le _
  exact Nat.le_trans hmono hfloor

theorem req_swap_keeps_value_aux_tmp : True := by trivial

theorem test_cases_syntax : ∀ (s : Swap), s.kind = Kind.givenIn ∨ s.kind = Kind.givenOut := by
  intro s
  cases hk : s.kind with
  | givenIn => exact Or.inl rfl
  | givenOut => exact Or.inr rfl

theorem test_case2 : ∀ (s : Swap) (P : Prop), (s.kind = Kind.givenIn → P) → (s.kind = Kind.givenOut → P) → P := by
  intro s P h1 h2
  cases h : s.kind
  · exact h1 h
  · exact h2 h

theorem test_onSwap_simp : ∀ (m : PoolMath) (p : Pool) (s : Swap) (q : Nat),
  s.kind = Kind.givenIn → (p.fee < ONE ∧ 0 < p.rate s.tokenOut) →
  onSwap m p s = some q →
  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut = q := by
  intro m p s q hSk hC hOS
  unfold onSwap at hOS
  rw [hSk, if_pos hC] at hOS
  exact Option.some_inj.mp hOS

theorem test_contra_none : ∀ (a b : Nat), (none : Option Nat) = some b → a ≤ b := by
  intro a b h
  contradiction
-- check if contradiction solves none=some

theorem test_simp_match : ∀ (p : Pool) (s : Swap),
  s.kind = Kind.givenIn → ¬(p.fee < ONE ∧ 0 < p.rate s.tokenOut) →
  (match s.kind with
  | .givenIn => if p.fee < ONE ∧ 0 < p.rate s.tokenOut then (some 1 : Option Nat) else none
  | .givenOut => some 2) = some 3 → False := by
  intro p s hSk hC hOS
  simp [hSk, hC] at hOS

theorem test_case_with : ∀ (s : Swap) (P : Nat → Prop) (q : Nat), (s.kind = Kind.givenIn → P q) → (s.kind = Kind.givenOut → P q) → P q := by
  intro s P q h1 h2
  cases hSk : s.kind with
  | givenIn => exact h1 hSk
  | givenOut => exact h2 hSk

theorem test_contra2 : ∀ (q : Nat) (x : Option Nat), x = none → x = some q → 0 < ONE := by
  intro q x h1 h2
  rw [h1] at h2
  contradiction

theorem test_simp_onSwap2 : ∀ (m : PoolMath) (p : Pool) (s : Swap) (q : Nat),
  s.kind = Kind.givenIn → (p.fee < ONE ∧ 0 < p.rate s.tokenOut) →
  onSwap m p s = some q →
  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut = q := by
  intro m p s q hk hcond hq
  have hq2 := hq
  unfold onSwap at hq2
  simp [hk, hcond] at hq2
  exact hq2

theorem test_scope_check : ∀ (m : PoolMath) (p : Pool) (s : Swap) (q : Nat),
  s.kind = Kind.givenIn → onSwap m p s = some q → p.fee < ONE ∧ 0 < p.rate s.tokenOut := by
  intro m p s q hk hq
  have hcondX : p.fee < ONE ∧ 0 < p.rate s.tokenOut := by
    unfold onSwap at hq
    rw [hk] at hq
    by_cases hcc : p.fee < ONE ∧ 0 < p.rate s.tokenOut
    · exact hcc
    · rw [if_neg hcc] at hq
      contradiction
  exact hcondX

theorem test_have_chain : ∀ (m : PoolMath) (p : Pool) (s : Swap) (q : Nat),
  s.kind = Kind.givenIn → onSwap m p s = some q →
  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut = q := by
  intro m p s q hk hq
  have hC : p.fee < ONE ∧ 0 < p.rate s.tokenOut := by
    unfold onSwap at hq
    rw [hk] at hq
    by_cases hcc : p.fee < ONE ∧ 0 < p.rate s.tokenOut
    · exact hcc
    · rw [if_neg hcc] at hq
      contradiction
  have hfee : p.fee < ONE := hC.1
  have hEq : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut = q := by
    unfold onSwap at hq
    rw [hk, if_pos hC] at hq
    exact Option.some_inj.mp hq
  exact hEq

theorem plan2_div_mul_le : ∀ (out r : Nat), out * ONE / r * r ≤ out * ONE := fun out r => Nat.div_mul_le_self _ _






theorem plan2_scaled_givenIn_dom : ∀ (p : Pool) (s : Swap) (y outS : Nat),
    s.tokenIn ≠ s.tokenOut →
    y * p.rate s.tokenOut ≤ outS * ONE →
    ∀ k, update2 (scaledBalances p) s.tokenIn
          ((scaledBalances p) s.tokenIn + netInDown p s)
          s.tokenOut ((scaledBalances p) s.tokenOut - outS) k ≤
        scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
          s.tokenOut (p.balance s.tokenOut - y) k) (p.rate k) := by
  intro p s y outS hneq hle k
  by_cases hi : k = s.tokenIn
  · subst hi
    have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - outS) s.tokenIn = (scaledBalances p) s.tokenIn + netInDown p s := by
      unfold update2
      simp
    have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - y) s.tokenIn = p.balance s.tokenIn + s.amount := by
      unfold update2
      simp
    rw [hL, hR]
    have hgoal : (scaledBalances p) s.tokenIn + netInDown p s ≤ scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := by
      unfold scaledBalances netInDown
      exact plan0_scaleDown_add_net_ge (p.balance s.tokenIn) s.amount (p.rate s.tokenIn) (ONE - p.fee) (Nat.sub_le ONE p.fee)
    exact hgoal
  · by_cases hj : k = s.tokenOut
    · subst hj
      have hne2 : s.tokenOut ≠ s.tokenIn := Ne.symm hneq
      have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - outS) s.tokenOut = (scaledBalances p) s.tokenOut - outS := by
        unfold update2
        simp [hne2]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - y) s.tokenOut = p.balance s.tokenOut - y := by
        unfold update2
        simp [hne2]
      rw [hL, hR]
      have hgoal : (scaledBalances p) s.tokenOut - outS ≤ scaleDown (p.balance s.tokenOut - y) (p.rate s.tokenOut) := by
        unfold scaledBalances
        exact plan0_scaleDown_sub_ge (p.balance s.tokenOut) y outS (p.rate s.tokenOut) hle
      exact hgoal
    · have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - outS) k = (scaledBalances p) k := by
        unfold update2
        simp [hi, hj]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - y) k = p.balance k := by
        unfold update2
        simp [hi, hj]
      rw [hL, hR]
      unfold scaledBalances
      exact Nat.le_refl _


theorem plan2_scaled_givenOut_dom_aux2 : True := by trivial


theorem plan2_ceil_charge_ge : ∀ (price fee rate c : Nat),
    0 < (ONE - fee) * rate →
    c = (ONE * ONE * price + ((ONE - fee) * rate) - 1) / ((ONE - fee) * rate) →
    ONE * ONE * price ≤ c * (ONE - fee) * rate := by
  intro price fee rate c hden hc
  have h := tmp_le_ceil_mulC (ONE * ONE * price) ((ONE - fee) * rate) hden
  rw [← hc] at h
  have hass : c * ((ONE - fee) * rate) = c * (ONE - fee) * rate := by
    rw [Nat.mul_assoc]
  rw [← hass]
  exact h

theorem plan2_invariant_mono_of_update2_le : ∀ (m : PoolMath) (n : Nat)
    (b b' : Nat → Nat) (i j xi yj : Nat),
    InvariantMonotone m n →
    (∀ k, k < n → update2 b i xi j yj k ≤ b' k) →
    m.invariant (update2 b i xi j yj) ≤ m.invariant b' := by
  intro m n b b' i j xi yj hmono hdom
  exact hmono _ _ hdom

theorem plan2_scaled_givenIn_dom_proof : ∀ (p : Pool) (s : Swap) (y outS : Nat),
    s.tokenIn ≠ s.tokenOut →
    y * p.rate s.tokenOut ≤ outS * ONE →
    ∀ k, update2 (scaledBalances p) s.tokenIn
          ((scaledBalances p) s.tokenIn + netInDown p s)
          s.tokenOut ((scaledBalances p) s.tokenOut - outS) k ≤
        scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
          s.tokenOut (p.balance s.tokenOut - y) k) (p.rate k) := by
  intro p s y outS hneq hle k
  by_cases hi : k = s.tokenIn
  · subst hi
    have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - outS) s.tokenIn = (scaledBalances p) s.tokenIn + netInDown p s := by
      unfold update2
      simp
    have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - y) s.tokenIn = p.balance s.tokenIn + s.amount := by
      unfold update2
      simp
    rw [hL, hR]
    have hgoal : (scaledBalances p) s.tokenIn + netInDown p s ≤ scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := by
      unfold scaledBalances netInDown
      exact plan0_scaleDown_add_net_ge (p.balance s.tokenIn) s.amount (p.rate s.tokenIn) (ONE - p.fee) (Nat.sub_le ONE p.fee)
    exact hgoal
  · by_cases hj : k = s.tokenOut
    · subst hj
      have hne2 : s.tokenOut ≠ s.tokenIn := Ne.symm hneq
      have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - outS) s.tokenOut = (scaledBalances p) s.tokenOut - outS := by
        unfold update2
        simp [hne2]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - y) s.tokenOut = p.balance s.tokenOut - y := by
        unfold update2
        simp [hne2]
      rw [hL, hR]
      have hgoal : (scaledBalances p) s.tokenOut - outS ≤ scaleDown (p.balance s.tokenOut - y) (p.rate s.tokenOut) := by
        unfold scaledBalances
        exact plan0_scaleDown_sub_ge (p.balance s.tokenOut) y outS (p.rate s.tokenOut) hle
      exact hgoal
    · have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - outS) k = (scaledBalances p) k := by
        unfold update2
        simp [hi, hj]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - y) k = p.balance k := by
        unfold update2
        simp [hi, hj]
      rw [hL, hR]
      unfold scaledBalances
      exact Nat.le_refl _

theorem plan2_scaled_givenOut_dom_pf : ∀ (p : Pool) (s : Swap) (c price : Nat),
    s.tokenIn ≠ s.tokenOut →
    ONE * ONE * price ≤ c * (ONE - p.fee) * p.rate s.tokenIn →
    s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE →
    ∀ k, update2 (scaledBalances p) s.tokenIn
          ((scaledBalances p) s.tokenIn + price)
          s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k ≤
        scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) k) (p.rate k) := by
  intro p s c price hneq hcov hceil k
  by_cases hi : k = s.tokenIn
  · subst hi
    have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn = (scaledBalances p) s.tokenIn + price := by
      unfold update2
      simp
    have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenIn = p.balance s.tokenIn + c := by
      unfold update2
      simp
    rw [hL, hR]
    have hgoal : (scaledBalances p) s.tokenIn + price ≤ scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := by
      unfold scaledBalances
      exact plan0_scaleDown_add_price_ge (p.balance s.tokenIn) c (p.rate s.tokenIn) (ONE - p.fee) price (Nat.sub_le ONE p.fee) hcov
    exact hgoal
  · by_cases hj : k = s.tokenOut
    · subst hj
      have hne2 : s.tokenOut ≠ s.tokenIn := Ne.symm hneq
      have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut = (scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
        unfold update2
        simp [hne2]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenOut = p.balance s.tokenOut - s.amount := by
        unfold update2
        simp [hne2]
      rw [hL, hR]
      have hgoal : (scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) ≤ scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
        unfold scaledBalances
        exact plan0_scaleDown_sub_ge (p.balance s.tokenOut) s.amount (scaleUp s.amount (p.rate s.tokenOut)) (p.rate s.tokenOut) hceil
      exact hgoal
    · have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k = (scaledBalances p) k := by
        unfold update2
        simp [hi, hj]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) k = p.balance k := by
        unfold update2
        simp [hi, hj]
      rw [hL, hR]
      unfold scaledBalances
      exact Nat.le_refl _

theorem swap_keeps_tmp5 : SwapKeepsValue onSwap := by
  intro m p s p' hwb hstep
  unfold step at hstep
  by_cases hV : Valid p s
  · simp only [hV, ↓reduceIte] at hstep
    cases hOS : onSwap m p s with
    | none => simp [hOS] at hstep
    | some q =>
      simp [hOS] at hstep
      have hValid : s.tokenIn ≠ s.tokenOut ∧ s.tokenIn < p.n ∧ s.tokenOut < p.n := hV
      obtain ⟨hneq, hin, hout⟩ := hValid
      unfold settle at hstep
      by_cases hle : amountOut s q ≤ p.balance s.tokenOut
      · simp [hle] at hstep
        have hpEq : p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s q) s.tokenOut (p.balance s.tokenOut - amountOut s q) } := hstep.symm
        have hscaleEq : scaledBalances p' = (fun k => scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s q) s.tokenOut (p.balance s.tokenOut - amountOut s q) k) (p.rate k)) := by
          rw [hpEq]
          rfl
        have hvalEq : value m p' = m.invariant (fun k => scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s q) s.tokenOut (p.balance s.tokenOut - amountOut s q) k) (p.rate k)) := by
          unfold value
          rw [hscaleEq]
        cases hkind : s.kind with
        | givenIn =>
          have hAin : amountIn s q = s.amount := by unfold amountIn; rw [hkind]
          have hAout : amountOut s q = q := by unfold amountOut; rw [hkind]
          rw [hAin, hAout] at hpEq hscaleEq hvalEq
          rw [hAout] at hle
          have hC : p.fee < ONE ∧ 0 < p.rate s.tokenOut := by
            unfold onSwap at hOS
            rw [hkind] at hOS
            by_cases hc : p.fee < ONE ∧ 0 < p.rate s.tokenOut
            · exact hc
            · rw [if_neg hc] at hOS; contradiction
          have hqEq : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut = q := by
            unfold onSwap at hOS
            rw [hkind, if_pos hC] at hOS
            exact Option.some_inj.mp hOS
          have hsound := hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hneq hin hout
          obtain ⟨hleMath, hinv1⟩ := hsound
          have hcover : q * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
            rw [← hqEq]
            exact Nat.div_mul_le_self _ _
          have hdom : ∀ k, update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k ≤ scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - q) k) (p.rate k) :=
            plan2_scaled_givenIn_dom_proof p s q _ hneq hcover
          have hmono := hwb.monotone _ _ (fun k hk => hdom k)
          have hval0 : value m p = m.invariant (scaledBalances p) := rfl
          rw [hval0, hvalEq]
          exact Nat.le_trans hinv1 hmono
        | givenOut =>
          have hAin : amountIn s q = q := by unfold amountIn; rw [hkind]
          have hAout : amountOut s q = s.amount := by unfold amountOut; rw [hkind]
          rw [hAin, hAout] at hpEq hscaleEq hvalEq
          rw [hAout] at hle
          have hC : p.fee < ONE ∧ 0 < p.rate s.tokenIn := by
            unfold onSwap at hOS
            rw [hkind] at hOS
            by_cases hc : p.fee < ONE ∧ 0 < p.rate s.tokenIn
            · exact hc
            · have hnone : (if p.fee < ONE ∧ 0 < p.rate s.tokenIn then (let amountScaled := scaleUp s.amount (p.rate s.tokenOut); let b := scaledBalances p; if amountScaled < b s.tokenOut then let price := m.inGivenOut b s.tokenIn s.tokenOut amountScaled; let den := (ONE - p.fee) * p.rate s.tokenIn; some ((ONE * ONE * price + den - 1) / den) else none) else none) = none := if_neg hc
              rw [hnone] at hOS; contradiction
          have hfee : p.fee < ONE := hC.1
          have hrate : 0 < p.rate s.tokenIn := hC.2
          have hdenPos : 0 < (ONE - p.fee) * p.rate s.tokenIn := Nat.mul_pos (by omega) hrate
          have hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := by
            unfold onSwap at hOS
            rw [hkind, if_pos hC] at hOS
            simp only at hOS
            by_cases hh : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
            · exact hh
            · have hnone : (if scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut then (let price := m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)); let den := (ONE - p.fee) * p.rate s.tokenIn; some ((ONE * ONE * price + den - 1) / den)) else none) = none := if_neg hh
              simp only at hnone
              rw [hnone] at hOS; contradiction
          have hqEq : (ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + ((ONE - p.fee) * p.rate s.tokenIn) - 1) / ((ONE - p.fee) * p.rate s.tokenIn) = q := by
            unfold onSwap at hOS
            rw [hkind, if_pos hC, if_pos hlt] at hOS
            simp only at hOS
            exact Option.some_inj.mp hOS
          have hcov : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ q * (ONE - p.fee) * p.rate s.tokenIn := by
            have hceil := tmp_le_ceil_mulC (ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) ((ONE - p.fee) * p.rate s.tokenIn) hdenPos
            rw [hqEq] at hceil
            have hass2 : q * (ONE - p.fee) * p.rate s.tokenIn = q * ((ONE - p.fee) * p.rate s.tokenIn) := Nat.mul_assoc _ _ _
            rw [← hass2] at hceil
            exact hceil
          have hceil2 : s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE :=
            plan0_scaleUp_mul_ge_proof s.amount (p.rate s.tokenOut)
          have hsound := hwb.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) hneq hin hout hlt
          have hdom : ∀ k, update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k ≤ scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + q) s.tokenOut (p.balance s.tokenOut - s.amount) k) (p.rate k) :=
            plan2_scaled_givenOut_dom_pf p s q _ hneq hcov hceil2
          have hmono := hwb.monotone _ _ (fun k hk => hdom k)
          have hval0 : value m p = m.invariant (scaledBalances p) := rfl
          rw [hval0, hvalEq]
          exact Nat.le_trans hsound hmono
      · simp [hle] at hstep
  · simp [hV] at hstep

theorem plan2_dom_inline_test : ∀ (p : Pool) (s : Swap) (c price : Nat),
    s.tokenIn ≠ s.tokenOut →
    ONE * ONE * price ≤ c * (ONE - p.fee) * p.rate s.tokenIn →
    s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE →
    ∀ k, update2 (scaledBalances p) s.tokenIn
          ((scaledBalances p) s.tokenIn + price)
          s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k ≤
        scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) k) (p.rate k) := by
  intro p s c price hneq hcov hceil k
  by_cases hi : k = s.tokenIn
  · subst hi
    have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn = (scaledBalances p) s.tokenIn + price := by
      unfold update2
      simp
    have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenIn = p.balance s.tokenIn + c := by
      unfold update2
      simp
    rw [hL, hR]
    have hgoal : (scaledBalances p) s.tokenIn + price ≤ scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := by
      unfold scaledBalances
      exact plan0_scaleDown_add_price_ge (p.balance s.tokenIn) c (p.rate s.tokenIn) (ONE - p.fee) price (Nat.sub_le ONE p.fee) hcov
    exact hgoal
  · by_cases hj : k = s.tokenOut
    · subst hj
      have hne2 : s.tokenOut ≠ s.tokenIn := Ne.symm hneq
      have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut = (scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
        unfold update2
        simp [hne2]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenOut = p.balance s.tokenOut - s.amount := by
        unfold update2
        simp [hne2]
      rw [hL, hR]
      have hgoal : (scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) ≤ scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
        unfold scaledBalances
        exact plan0_scaleDown_sub_ge (p.balance s.tokenOut) s.amount (scaleUp s.amount (p.rate s.tokenOut)) (p.rate s.tokenOut) hceil
      exact hgoal
    · have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k = (scaledBalances p) k := by
        unfold update2
        simp [hi, hj]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) k = p.balance k := by
        unfold update2
        simp [hi, hj]
      rw [hL, hR]
      unfold scaledBalances
      exact Nat.le_refl _

theorem plan2_scaled_givenOut_dom : ∀ (p : Pool) (s : Swap) (c price : Nat),
    s.tokenIn ≠ s.tokenOut →
    ONE * ONE * price ≤ c * (ONE - p.fee) * p.rate s.tokenIn →
    s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE →
    ∀ k, update2 (scaledBalances p) s.tokenIn
          ((scaledBalances p) s.tokenIn + price)
          s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k ≤
        scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) k) (p.rate k) := by
  intro p s c price hneq hcov hceil k
  by_cases hi : k = s.tokenIn
  · subst hi
    have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn = (scaledBalances p) s.tokenIn + price := by
      unfold update2
      simp
    have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenIn = p.balance s.tokenIn + c := by
      unfold update2
      simp
    rw [hL, hR]
    have hgoal : (scaledBalances p) s.tokenIn + price ≤ scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := by
      unfold scaledBalances
      exact plan0_scaleDown_add_price_ge (p.balance s.tokenIn) c (p.rate s.tokenIn) (ONE - p.fee) price (Nat.sub_le ONE p.fee) hcov
    exact hgoal
  · by_cases hj : k = s.tokenOut
    · subst hj
      have hne2 : s.tokenOut ≠ s.tokenIn := Ne.symm hneq
      have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut = (scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
        unfold update2
        simp [hne2]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenOut = p.balance s.tokenOut - s.amount := by
        unfold update2
        simp [hne2]
      rw [hL, hR]
      have hgoal : (scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) ≤ scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
        unfold scaledBalances
        exact plan0_scaleDown_sub_ge (p.balance s.tokenOut) s.amount (scaleUp s.amount (p.rate s.tokenOut)) (p.rate s.tokenOut) hceil
      exact hgoal
    · have hL : update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + price) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k = (scaledBalances p) k := by
        unfold update2
        simp [hi, hj]
      have hR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c) s.tokenOut (p.balance s.tokenOut - s.amount) k = p.balance k := by
        unfold update2
        simp [hi, hj]
      rw [hL, hR]
      unfold scaledBalances
      exact Nat.le_refl _

theorem req_swap_keeps_value_proof_alias : SwapKeepsValue onSwap := swap_keeps_tmp5

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hwb hk hvalid hrate hfee
  have hon : onSwap m p s = some (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) := by
    unfold onSwap
    rw [hk]
    rw [if_pos (And.intro hfee hrate)]
  have hvalid2 : s.tokenIn ≠ s.tokenOut ∧ s.tokenIn < p.n ∧ s.tokenOut < p.n := hvalid
  obtain ⟨hneq, hin, hout⟩ := hvalid2
  have hsound := hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hneq hin hout
  obtain ⟨hle_math, _⟩ := hsound
  have hscale_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤ scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := by
    have hthis : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤ (scaledBalances p) s.tokenOut := hle_math
    have heq : (scaledBalances p) s.tokenOut = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
    rw [heq] at hthis
    exact hthis
  unfold scaleDown at hscale_le
  have hy_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut ≤ p.balance s.tokenOut := by
    have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤ (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE := Nat.mul_le_mul_right _ hscale_le
    have h2 : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
      Nat.div_mul_le_self _ _
    have h3 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut :=
      Nat.le_trans h1 h2
    have h4 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut ≤ (p.balance s.tokenOut * p.rate s.tokenOut) / p.rate s.tokenOut :=
      Nat.div_le_div_right h3
    have h5 : (p.balance s.tokenOut * p.rate s.tokenOut) / p.rate s.tokenOut = p.balance s.tokenOut :=
      Nat.mul_div_cancel _ hrate
    rw [h5] at h4
    exact h4
  have hle : amountOut s (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut) ≤ p.balance s.tokenOut := by
    unfold amountOut
    rw [hk]
    exact hy_le
  unfold step
  rw [if_pos hvalid, hon]
  simp [settle, hle]

theorem req_given_out_succeeds       : GivenOutSucceeds onSwap := by
  intro m p s hwb hk hvalid hrate hfee hlt
  have hle : s.amount ≤ p.balance s.tokenOut :=
    scaleDown_ge_scaleUp_of_lt_aux s.amount (p.balance s.tokenOut) (p.rate s.tokenOut) hlt
  have hcond : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := by
    unfold scaledBalances scaleDown
    unfold scaleUp scaleDown at hlt
    exact hlt
  have hon : onSwap m p s = some ((ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + ((ONE - p.fee) * p.rate s.tokenIn) - 1) / ((ONE - p.fee) * p.rate s.tokenIn)) := by
    unfold onSwap
    rw [hk]
    rw [if_pos (And.intro hfee hrate)]
    rw [if_pos hcond]
  unfold step
  rw [if_pos hvalid, hon]
  simp [settle, amountOut, hk, hle]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y _ hk hvalid himpl
  unfold onSwap at himpl
  rw [hk] at himpl
  by_cases hcond : p.fee < ONE ∧ 0 < p.rate s.tokenOut
  · rw [if_pos hcond] at himpl
    simp only at himpl
    have hEq : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut = y := Option.some_inj.mp himpl
    subst hEq
    have hc : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := Nat.mul_comm _ _
    rw [hc]
    exact Nat.div_mul_le_self _ _
  · rw [if_neg hcond] at himpl
    contradiction

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hk hvalid himpl
  unfold onSwap at himpl
  rw [hk] at himpl
  by_cases hcond : p.fee < ONE ∧ 0 < p.rate s.tokenOut
  · rw [if_pos hcond] at himpl
    have hy : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut = y :=
      Option.some_inj.mp himpl
    have hrate : 0 < p.rate s.tokenOut := hcond.2
    have hnetle : netInLessOneDown p s ≤ netInDown p s := by
      unfold netInLessOneDown netInDown
      apply Nat.div_le_div_right
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hout : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
      hmono.1 _ _ _ _ _ hnetle
    have hONEle : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
      have h := Nat.mul_le_mul_left ONE hout
      have hc : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) =
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.mul_comm _ _
      omega
    have hlt : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE <
        (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut + 1) *
        p.rate s.tokenOut :=
      req_given_in_pays_at_least_aux1 _ _ hrate
    rw [hy] at hlt
    omega
  · rw [if_neg hcond] at himpl
    contradiction

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c _ hk hvalid himpl
  unfold onSwap at himpl
  rw [hk] at himpl
  by_cases hcond : p.fee < ONE ∧ 0 < p.rate s.tokenIn
  · rw [if_pos hcond] at himpl
    have hfee : p.fee < ONE := hcond.1
    have hrate : 0 < p.rate s.tokenIn := hcond.2
    have hden_pos : 0 < (ONE - p.fee) * p.rate s.tokenIn := by
      apply Nat.mul_pos
      · omega
      · exact hrate
    by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
    · rw [if_pos hlt] at himpl
      simp only at himpl
      have hc : (ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + ((ONE - p.fee) * p.rate s.tokenIn) - 1) / ((ONE - p.fee) * p.rate s.tokenIn) = c := Option.some_inj.mp himpl
      have hcov : ONE * ONE * outPrice m p s ≤ (ONE * ONE * outPrice m p s + ((ONE - p.fee) * p.rate s.tokenIn) - 1) / ((ONE - p.fee) * p.rate s.tokenIn) * ((ONE - p.fee) * p.rate s.tokenIn) := tmp_le_ceil_mulC _ _ hden_pos
      have hout : outPrice m p s = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := by unfold outPrice; rfl
      rw [hout] at hcov
      rw [hc] at hcov
      have hass : c * ((ONE - p.fee) * p.rate s.tokenIn) = c * (ONE - p.fee) * p.rate s.tokenIn := by rw [Nat.mul_assoc]
      rw [hass] at hcov
      have hL : ONE * ONE * outPrice m p s = ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := by rw [hout]
      rw [hL]
      exact hcov
    · rw [if_neg hlt] at himpl
      contradiction
  · rw [if_neg hcond] at himpl
    contradiction

theorem req_given_out_charges_at_most  : GivenOutChargesAtMost onSwap := by
  intro m p s c _ hk hvalid himpl
  unfold onSwap at himpl
  rw [hk] at himpl
  have hONEpos : 0 < ONE := by unfold ONE; decide
  by_cases hcond : p.fee < ONE ∧ 0 < p.rate s.tokenIn
  · rw [if_pos hcond] at himpl
    have hfee : p.fee < ONE := hcond.1
    have hrate : 0 < p.rate s.tokenIn := hcond.2
    have hden_pos : 0 < (ONE - p.fee) * p.rate s.tokenIn :=
      Nat.mul_pos (by omega) hrate
    have hRpos : 0 < ONE * p.rate s.tokenIn := Nat.mul_pos hONEpos hrate
    have hdenR : (ONE - p.fee) * p.rate s.tokenIn ≤ ONE * p.rate s.tokenIn := by
      apply Nat.mul_le_mul_right
      omega
    by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
    · rw [if_pos hlt] at himpl
      simp only at himpl
      have hc : (ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + ((ONE - p.fee) * p.rate s.tokenIn) - 1) / ((ONE - p.fee) * p.rate s.tokenIn) = c :=
        Option.some_inj.mp himpl
      have hbound := req_given_out_charges_at_most_aux c ((ONE - p.fee) * p.rate s.tokenIn)
        (ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)))
        (ONE * p.rate s.tokenIn) hden_pos hdenR hc hRpos
      have hout : outPrice m p s =
          m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := by
        unfold outPrice; rfl
      have hRHS : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) +
          ONE * p.rate s.tokenIn = ONE * (ONE * outPrice m p s + p.rate s.tokenIn) := by
        rw [hout]
        rw [Nat.mul_add]
        congr 1
        rw [Nat.mul_assoc]
      have hLHS : (c - 1) * (ONE - p.fee) * p.rate s.tokenIn =
          (c - 1) * ((ONE - p.fee) * p.rate s.tokenIn) := by
        rw [Nat.mul_assoc]
      rw [hLHS]
      rw [← hRHS]
      exact hbound
    · rw [if_neg hlt] at himpl
      contradiction
  · rw [if_neg hcond] at himpl
    contradiction

theorem req_swap_keeps_value : SwapKeepsValue onSwap := swap_keeps_tmp5

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss
  induction ss generalizing p with
  | nil =>
    intro p' hwb hrun
    simp [run] at hrun
    subst hrun
    exact Nat.le_refl _
  | cons s ss ih =>
    intro p' hwb hrun
    unfold run at hrun
    cases hst : step onSwap m p s with
    | none => simp [hst] at hrun
    | some pm =>
      simp [hst] at hrun
      have hn : pm.n = p.n := helper_batch_n_step m p s pm hst
      have hwb2 : WellBehaved m pm.n := by rw [hn]; exact hwb
      have hle1 : value m p ≤ value m pm := req_swap_keeps_value m p s pm hwb hst
      have hle2 : value m pm ≤ value m p' := ih pm p' hwb2 hrun
      exact Nat.le_trans hle1 hle2

end BalancerSwap

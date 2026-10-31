import BalancerSwap.Spec
namespace BalancerSwap

def ginQuote (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut

def ginOpt (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if p.rate s.tokenOut = 0 then none else some (ginQuote m p s)

def goutD (p : Pool) (s : Swap) : Nat :=
  (ONE - p.fee) * p.rate s.tokenIn

def goutN (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  ONE * ONE * outPrice m p s

def goutQuote (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  (goutN m p s + goutD p s - 1) / goutD p s

def goutOpt (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if p.rate s.tokenIn = 0 then none
  else if ONE ≤ p.fee then none
  else if scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) then none
  else some (goutQuote m p s)

def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => ginOpt m p s
  | .givenOut => goutOpt m p s

theorem onePos : 0 < ONE := by unfold ONE; omega

theorem divMulLe (a b : Nat) : a / b * b ≤ a := by
  have h := Nat.div_add_mod a b
  have hc : a / b * b = b * (a / b) := Nat.mul_comm _ _
  omega

theorem ceilGe (n d : Nat) (hd : 0 < d) : n ≤ (n + d - 1) / d * d := by
  have h := Nat.div_add_mod (n + d - 1) d
  have hlt : (n + d - 1) % d < d := Nat.mod_lt _ hd
  have hc : (n + d - 1) / d * d = d * ((n + d - 1) / d) := Nat.mul_comm _ _
  omega

theorem leOfMulLeRight (a b c : Nat) (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  cases hcab : decide (a ≤ b) with
  | true => exact of_decide_eq_true hcab
  | false =>
    have hle : ¬ a ≤ b := of_decide_eq_false hcab
    have h1 : b + 1 ≤ a := by omega
    have hm : (b + 1) * c ≤ a * c := Nat.mul_le_mul h1 (Nat.le_refl _)
    have he : (b + 1) * c = b * c + c := by rw [Nat.add_mul, Nat.one_mul]
    omega

theorem leDivOfMulLe (x y k : Nat) (hk : 0 < k) (h : x * k ≤ y) : x ≤ y / k := by
  cases hcab : decide (x ≤ y / k) with
  | true => exact of_decide_eq_true hcab
  | false =>
    have hle : ¬ x ≤ y / k := of_decide_eq_false hcab
    have h1 : y / k + 1 ≤ x := by omega
    have hm : (y / k + 1) * k ≤ x * k := Nat.mul_le_mul h1 (Nat.le_refl _)
    have he : (y / k + 1) * k = k * (y / k) + k := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (y / k) k]
    have hmod := Nat.div_add_mod y k
    have hlt : y % k < k := Nat.mod_lt _ hk
    omega

theorem divMono (a b k : Nat) (h : a ≤ b) : a / k ≤ b / k := by
  cases hc : decide (0 < k) with
  | true =>
    have hk : 0 < k := of_decide_eq_true hc
    have h1 : a / k * k ≤ a := divMulLe _ _
    have h2 : a / k * k ≤ b := Nat.le_trans h1 h
    exact leDivOfMulLe _ _ _ hk h2
  | false =>
    have hk : ¬ 0 < k := of_decide_eq_false hc
    have hk0 : k = 0 := by omega
    simp [hk0]

theorem scaleDownLe (a r : Nat) : scaleDown a r * ONE ≤ a * r := by
  unfold scaleDown
  exact divMulLe _ _

theorem scaleUpGe (a r : Nat) : a * r ≤ scaleUp a r * ONE := by
  unfold scaleUp
  have h := ceilGe (a * r) ONE onePos
  have heq : a * r + ONE - 1 = a * r + (ONE - 1) := by
    have hO : 0 < ONE := onePos
    omega
  rw [heq] at h
  exact h

theorem netLessLe (p : Pool) (s : Swap) : netInLessOneDown p s ≤ netInDown p s := by
  unfold netInLessOneDown netInDown
  apply divMono
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.le_refl _)

theorem ginInGe (bal amt r f : Nat) :
    bal * r / ONE + amt * (ONE - f) * r / (ONE * ONE) ≤ (bal + amt) * r / ONE := by
  apply leDivOfMulLe _ _ _ onePos
  have hA : bal * r / ONE * ONE ≤ bal * r := divMulLe _ _
  have hN : amt * (ONE - f) * r / (ONE * ONE) * (ONE * ONE) ≤ amt * (ONE - f) * r :=
    divMulLe _ _
  have hC : amt * (ONE - f) * r ≤ amt * r * ONE := by
    have h1 : amt * (ONE - f) ≤ amt * ONE := Nat.mul_le_mul (Nat.le_refl _) (Nat.sub_le _ _)
    have h2 : amt * (ONE - f) * r ≤ amt * ONE * r := Nat.mul_le_mul h1 (Nat.le_refl _)
    have e1 : amt * ONE * r = amt * r * ONE := by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm ONE r]
    rw [e1] at h2
    exact h2
  have hX : amt * (ONE - f) * r / (ONE * ONE) * ONE ≤ amt * r := by
    have hle : amt * (ONE - f) * r / (ONE * ONE) * ONE * ONE ≤ amt * r * ONE := by
      have e : amt * (ONE - f) * r / (ONE * ONE) * ONE * ONE
        = amt * (ONE - f) * r / (ONE * ONE) * (ONE * ONE) := by rw [Nat.mul_assoc]
      rw [e]
      exact Nat.le_trans hN hC
    have e2 : amt * (ONE - f) * r / (ONE * ONE) * ONE * ONE
      = (amt * (ONE - f) * r / (ONE * ONE) * ONE) * ONE := by rw [Nat.mul_assoc]
    have e3 : amt * r * ONE = (amt * r) * ONE := by rw [Nat.mul_assoc]
    exact leOfMulLeRight _ _ _ onePos (by rw [e2] at hle; rw [e3] at hle; exact hle)
  have hexp : (bal * r / ONE + amt * (ONE - f) * r / (ONE * ONE)) * ONE
    = bal * r / ONE * ONE + amt * (ONE - f) * r / (ONE * ONE) * ONE := Nat.add_mul _ _ _
  rw [hexp]
  have hexp2 : (bal + amt) * r = bal * r + amt * r := Nat.add_mul _ _ _
  rw [hexp2]
  exact Nat.add_le_add hA hX

theorem ginOutGe (bal y r O : Nat) (hyr : y * r ≤ O * ONE)
    (hle : O ≤ bal * r / ONE) (hyb : y ≤ bal) :
    bal * r / ONE - O ≤ (bal - y) * r / ONE := by
  apply leDivOfMulLe _ _ _ onePos
  cases hc : decide (bal * r / ONE ≤ O) with
  | true =>
    have hqO : bal * r / ONE ≤ O := of_decide_eq_true hc
    have hzero : bal * r / ONE - O = 0 := Nat.sub_eq_zero_of_le hqO
    rw [hzero]
    simp
  | false =>
    have hqO : ¬ bal * r / ONE ≤ O := of_decide_eq_false hc
    have hOX : O ≤ bal * r / ONE := by omega
    have h1 : bal * r / ONE - O + O = bal * r / ONE := Nat.sub_add_cancel hOX
    have h2 : (bal * r / ONE - O + O) * ONE = bal * r / ONE * ONE := by rw [h1]
    have h3 : (bal * r / ONE - O + O) * ONE = (bal * r / ONE - O) * ONE + O * ONE := Nat.add_mul _ _ _
    have hA : bal * r / ONE * ONE ≤ bal * r := divMulLe _ _
    have hBeq : (bal - y) * r + y * r = bal * r := by
      have h1b : bal - y + y = bal := Nat.sub_add_cancel hyb
      have h2b : (bal - y + y) * r = bal * r := by rw [h1b]
      rw [Nat.add_mul] at h2b
      exact h2b
    omega

theorem goutInGe (bal c r P f : Nat) (hf : f < ONE) (hr : 0 < r)
    (hch : P * ONE * ONE ≤ c * (ONE - f) * r) :
    bal * r / ONE + P ≤ (bal + c) * r / ONE := by
  apply leDivOfMulLe _ _ _ onePos
  have hA : bal * r / ONE * ONE ≤ bal * r := divMulLe _ _
  have hP : P * ONE ≤ c * r := by
    have h1 : P * ONE * ONE ≤ c * r * ONE := by
      have h2 : c * (ONE - f) * r ≤ c * r * ONE := by
        have ha : c * (ONE - f) ≤ c * ONE := Nat.mul_le_mul (Nat.le_refl _) (Nat.sub_le _ _)
        have hb : c * (ONE - f) * r ≤ c * ONE * r := Nat.mul_le_mul ha (Nat.le_refl _)
        have e : c * ONE * r = c * r * ONE := by
          rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm ONE r]
        rw [e] at hb
        exact hb
      exact Nat.le_trans hch h2
    exact leOfMulLeRight _ _ _ onePos h1
  have hexp : (bal * r / ONE + P) * ONE = bal * r / ONE * ONE + P * ONE := Nat.add_mul _ _ _
  rw [hexp]
  have hexp2 : (bal + c) * r = bal * r + c * r := Nat.add_mul _ _ _
  rw [hexp2]
  exact Nat.add_le_add hA hP

theorem goutOutGe (bal amt r : Nat) (hyb : amt ≤ bal) :
    bal * r / ONE - (amt * r + (ONE - 1)) / ONE ≤ (bal - amt) * r / ONE := by
  apply leDivOfMulLe _ _ _ onePos
  cases hc : decide (bal * r / ONE ≤ (amt * r + (ONE - 1)) / ONE) with
  | true =>
    have hq : bal * r / ONE ≤ (amt * r + (ONE - 1)) / ONE := of_decide_eq_true hc
    have hzero : bal * r / ONE - (amt * r + (ONE - 1)) / ONE = 0 :=
      Nat.sub_eq_zero_of_le hq
    rw [hzero]
    simp
  | false =>
    have hq : ¬ bal * r / ONE ≤ (amt * r + (ONE - 1)) / ONE := of_decide_eq_false hc
    have hOX : (amt * r + (ONE - 1)) / ONE ≤ bal * r / ONE := by omega
    have hDist : (bal * r / ONE - (amt * r + (ONE - 1)) / ONE) * ONE
      = bal * r / ONE * ONE - ((amt * r + (ONE - 1)) / ONE) * ONE := Nat.sub_mul _ _ _
    rw [hDist]
    have hA : bal * r / ONE * ONE ≤ bal * r := divMulLe _ _
    have hQlow : amt * r ≤ ((amt * r + (ONE - 1)) / ONE) * ONE := by
      have h := ceilGe (amt * r) ONE onePos
      have heq : amt * r + ONE - 1 = amt * r + (ONE - 1) := by
        have hO : 0 < ONE := onePos
        omega
      rw [heq] at h
      exact h
    have hBeq : (bal - amt) * r + amt * r = bal * r := by
      have h1b : bal - amt + amt = bal := Nat.sub_add_cancel hyb
      have h2b : (bal - amt + amt) * r = bal * r := by rw [h1b]
      rw [Nat.add_mul] at h2b
      exact h2b
    omega

theorem ceilPredLe (N D : Nat) (hD : 0 < D) : ((N + D - 1) / D - 1) * D ≤ N := by
  cases hc : decide ((N + D - 1) / D = 0) with
  | true =>
    have hQ : (N + D - 1) / D = 0 := of_decide_eq_true hc
    rw [hQ]
    simp
  | false =>
    have hQ : ¬ (N + D - 1) / D = 0 := of_decide_eq_false hc
    have hle1 : 1 ≤ (N + D - 1) / D := Nat.pos_of_ne_zero hQ
    have h1 : (N + D - 1) / D * D ≤ N + D - 1 := divMulLe _ _
    have heq : (N + D - 1) / D - 1 + 1 = (N + D - 1) / D := Nat.sub_add_cancel hle1
    have h2 : ((N + D - 1) / D - 1) * D + D = (N + D - 1) / D * D := by
      have h : ((N + D - 1) / D - 1 + 1) * D = (N + D - 1) / D * D := by rw [heq]
      rw [Nat.add_mul, Nat.one_mul] at h
      exact h
    omega

theorem scaleLtLe (a b r : Nat) (hr : 0 < r) (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  cases hc : decide (a ≤ b) with
  | true => exact of_decide_eq_true hc
  | false =>
    have hcon : ¬ a ≤ b := of_decide_eq_false hc
    have hgt : b + 1 ≤ a := by omega
    have hm : (b + 1) * r ≤ a * r := Nat.mul_le_mul hgt (Nat.le_refl _)
    have h1 : a * r ≤ scaleUp a r * ONE := scaleUpGe _ _
    have h2 : scaleDown b r * ONE ≤ b * r := scaleDownLe _ _
    have hle2 : scaleUp a r + 1 ≤ scaleDown b r := h
    have hmono : (scaleUp a r + 1) * ONE ≤ scaleDown b r * ONE :=
      Nat.mul_le_mul hle2 (Nat.le_refl _)
    have e1 : (scaleUp a r + 1) * ONE = scaleUp a r * ONE + ONE := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [e1] at hmono
    have e2 : (b + 1) * r = b * r + r := by rw [Nat.add_mul, Nat.one_mul]
    rw [e2] at hm
    omega

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  unfold GivenInSucceeds
  intro m p s hw hk hv hr hf
  unfold step
  rw [if_pos hv]
  have hne : p.rate s.tokenOut ≠ 0 := by omega
  have himpl : onSwap m p s = some (ginQuote m p s) := by
    unfold onSwap ginOpt
    simp [hk, hne]
  rw [himpl]
  simp only
  unfold settle amountOut
  rw [hk]
  simp only
  have hs := hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
    hv.1 hv.2.1 hv.2.2
  have hOle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
      ≤ scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := hs.1
  have hNle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
    have h1 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE
      ≤ scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) * ONE :=
      Nat.mul_le_mul hOle (Nat.le_refl _)
    exact Nat.le_trans h1 (scaleDownLe _ _)
  have hQle : ginQuote m p s * p.rate s.tokenOut ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
    unfold ginQuote
    exact Nat.le_trans (divMulLe _ _) hNle
  have hle : ginQuote m p s ≤ p.balance s.tokenOut :=
    leOfMulLeRight _ _ _ hr hQle
  simp [hle]

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  unfold GivenOutSucceeds
  intro m p s hw hk hv hr hf hbal
  unfold step
  rw [if_pos hv]
  have hbal2 : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := hbal
  have h1 : p.rate s.tokenIn ≠ 0 := by omega
  have h2 : ¬ ONE ≤ p.fee := by omega
  have h3 : ¬ scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := by omega
  have himpl : onSwap m p s = some (goutQuote m p s) := by
    unfold onSwap goutOpt
    simp [hk, h1, h2, h3]
  rw [himpl]
  simp only
  unfold settle amountOut
  rw [hk]
  simp only
  have hrOut : 0 < p.rate s.tokenOut := by
    cases hc : decide (p.rate s.tokenOut = 0) with
    | true =>
      have h0 : p.rate s.tokenOut = 0 := of_decide_eq_true hc
      have heq : scaledBalances p s.tokenOut = 0 := by
        unfold scaledBalances scaleDown
        simp [h0]
      rw [heq] at hbal2
      omega
    | false => exact Nat.pos_of_ne_zero (of_decide_eq_false hc)
  have hfin : s.amount ≤ p.balance s.tokenOut := scaleLtLe _ _ _ hrOut hbal
  simp [hfin]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  unfold GivenInPaysAtMost
  intro m p s y _ hk hv himpl
  cases hc : decide (p.rate s.tokenOut = 0) with
  | true =>
    have h0 : p.rate s.tokenOut = 0 := of_decide_eq_true hc
    have heq : onSwap m p s = none := by unfold onSwap ginOpt; simp [hk, h0]
    rw [heq] at himpl
    simp at himpl
  | false =>
    have hne : p.rate s.tokenOut ≠ 0 := of_decide_eq_false hc
    have heq : onSwap m p s = some (ginQuote m p s) := by
      unfold onSwap ginOpt; simp [hk, hne]
    rw [heq] at himpl
    simp at himpl
    subst himpl
    unfold ginQuote
    have h := divMulLe (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) (p.rate s.tokenOut)
    have heq2 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
      = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.mul_comm _ _
    rw [heq2]
    exact h

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  unfold GivenInPaysAtLeast
  intro m p s y hm hk hv himpl
  cases hc : decide (p.rate s.tokenOut = 0) with
  | true =>
    have h0 : p.rate s.tokenOut = 0 := of_decide_eq_true hc
    have heq : onSwap m p s = none := by unfold onSwap ginOpt; simp [hk, h0]
    rw [heq] at himpl
    simp at himpl
  | false =>
    have hne : p.rate s.tokenOut ≠ 0 := of_decide_eq_false hc
    have heq : onSwap m p s = some (ginQuote m p s) := by
      unfold onSwap ginOpt; simp [hk, hne]
    rw [heq] at himpl
    simp at himpl
    subst himpl
    have hrpos : 0 < p.rate s.tokenOut := by omega
    have hle : netInLessOneDown p s ≤ netInDown p s := netLessLe p s
    have hmono : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
        ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
      hm.1 _ _ _ _ _ hle
    have hmul : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
        ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := by
      have h1 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
        ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
        Nat.mul_le_mul (Nat.le_refl _) hmono
      have e : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
        = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.mul_comm _ _
      rw [e] at h1
      exact h1
    have hmod := Nat.div_add_mod
      (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) (p.rate s.tokenOut)
    have hlt : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE) % p.rate s.tokenOut
      < p.rate s.tokenOut := Nat.mod_lt _ hrpos
    have hcomm : (ginQuote m p s + 1) * p.rate s.tokenOut
      = p.rate s.tokenOut * (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE / p.rate s.tokenOut)
        + p.rate s.tokenOut := by
      unfold ginQuote
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (_ / _) _]
    rw [hcomm]
    omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  unfold GivenOutChargesAtLeast
  intro m p s c _ hk hv himpl
  cases hc1 : decide (p.rate s.tokenIn = 0) with
  | true =>
    have h0 : p.rate s.tokenIn = 0 := of_decide_eq_true hc1
    have heq : onSwap m p s = none := by unfold onSwap goutOpt; simp [hk, h0]
    rw [heq] at himpl
    simp at himpl
  | false =>
    have h1 : p.rate s.tokenIn ≠ 0 := of_decide_eq_false hc1
    cases hc2 : decide (ONE ≤ p.fee) with
    | true =>
      have hcc : ONE ≤ p.fee := of_decide_eq_true hc2
      have heq : onSwap m p s = none := by unfold onSwap goutOpt; simp [hk, h1, hcc]
      rw [heq] at himpl
      simp at himpl
    | false =>
      have h2 : ¬ ONE ≤ p.fee := of_decide_eq_false hc2
      cases hc3 : decide (scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut)) with
      | true =>
        have hcc : scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := of_decide_eq_true hc3
        have heq : onSwap m p s = none := by unfold onSwap goutOpt; simp [hk, h1, hcc]
        rw [heq] at himpl
        simp at himpl
      | false =>
        have h3 : ¬ scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := of_decide_eq_false hc3
        have heq : onSwap m p s = some (goutQuote m p s) := by
          unfold onSwap goutOpt; simp [hk, h1, h2, h3]
        rw [heq] at himpl
        simp at himpl
        subst himpl
        have hr : 0 < p.rate s.tokenIn := by omega
        have hf : p.fee < ONE := by omega
        have hsub : 0 < ONE - p.fee := by omega
        have hDpos : 0 < goutD p s := by unfold goutD; exact Nat.mul_pos hsub hr
        have hge := ceilGe (goutN m p s) (goutD p s) hDpos
        have hEq : goutQuote m p s * (ONE - p.fee) * p.rate s.tokenIn = goutQuote m p s * goutD p s := by
          unfold goutD; rw [Nat.mul_assoc]
        rw [hEq]
        show ONE * ONE * outPrice m p s ≤ goutQuote m p s * goutD p s
        have hGN : goutN m p s = ONE * ONE * outPrice m p s := rfl
        have hGQ : goutQuote m p s = (goutN m p s + goutD p s - 1) / goutD p s := rfl
        rw [← hGN]
        rw [hGQ]
        exact hge

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  unfold GivenOutChargesAtMost
  intro m p s c _ hk hv himpl
  cases hc1 : decide (p.rate s.tokenIn = 0) with
  | true =>
    have h0 : p.rate s.tokenIn = 0 := of_decide_eq_true hc1
    have heq : onSwap m p s = none := by unfold onSwap goutOpt; simp [hk, h0]
    rw [heq] at himpl
    simp at himpl
  | false =>
    have h1 : p.rate s.tokenIn ≠ 0 := of_decide_eq_false hc1
    cases hc2 : decide (ONE ≤ p.fee) with
    | true =>
      have hcc : ONE ≤ p.fee := of_decide_eq_true hc2
      have heq : onSwap m p s = none := by unfold onSwap goutOpt; simp [hk, h1, hcc]
      rw [heq] at himpl
      simp at himpl
    | false =>
      have h2 : ¬ ONE ≤ p.fee := of_decide_eq_false hc2
      cases hc3 : decide (scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut)) with
      | true =>
        have hcc : scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := of_decide_eq_true hc3
        have heq : onSwap m p s = none := by unfold onSwap goutOpt; simp [hk, h1, hcc]
        rw [heq] at himpl
        simp at himpl
      | false =>
        have h3 : ¬ scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := of_decide_eq_false hc3
        have heq : onSwap m p s = some (goutQuote m p s) := by
          unfold onSwap goutOpt; simp [hk, h1, h2, h3]
        rw [heq] at himpl
        simp at himpl
        subst himpl
        have hr : 0 < p.rate s.tokenIn := by omega
        have hf : p.fee < ONE := by omega
        have hDpos : 0 < goutD p s := by unfold goutD; exact Nat.mul_pos (by omega : 0 < ONE - p.fee) hr
        have hle := ceilPredLe (goutN m p s) (goutD p s) hDpos
        have hEq : (goutQuote m p s - 1) * (ONE - p.fee) * p.rate s.tokenIn
          = ((goutN m p s + goutD p s - 1) / goutD p s - 1) * goutD p s := by
          unfold goutQuote goutD
          rw [Nat.mul_assoc]
        rw [hEq]
        have hEq2 : ONE * (ONE * outPrice m p s + p.rate s.tokenIn)
          = goutN m p s + ONE * p.rate s.tokenIn := by
          unfold goutN
          rw [Nat.mul_add, Nat.mul_assoc]
        rw [hEq2]
        have hpos : 0 < ONE * p.rate s.tokenIn := Nat.mul_pos onePos hr
        omega

theorem validOfStepAux (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool)
    (hstep : step onSwap m p s = some p') : Valid p s := by
  unfold step at hstep
  cases hc : decide (Valid p s) with
  | true => exact of_decide_eq_true hc
  | false =>
    have h : ¬ Valid p s := of_decide_eq_false hc
    simp [h] at hstep

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  unfold SwapKeepsValue
  intro m p s p' hw hstep
  have hv : Valid p s := validOfStepAux m p s p' hstep
  cases hc : s.kind with
  | givenIn =>
    have hk : s.kind = Kind.givenIn := hc
    have hon : onSwap m p s = ginOpt m p s := by unfold onSwap; simp [hk]
    cases hgin : ginOpt m p s with
    | none =>
      unfold step at hstep
      simp [hv, hon, hgin] at hstep
    | some y =>
      unfold step at hstep
      simp [hv, hon, hgin] at hstep
      have hset : settle p s y = some p' := hstep
      cases hlc : decide (y ≤ p.balance s.tokenOut) with
      | false =>
        have hle : ¬ y ≤ p.balance s.tokenOut := of_decide_eq_false hlc
        unfold settle amountIn amountOut at hset
        rw [hk] at hset
        simp [hle] at hset
      | true =>
        have hle : y ≤ p.balance s.tokenOut := of_decide_eq_true hlc
        unfold settle amountIn amountOut at hset
        rw [hk] at hset
        simp only at hset
        simp [hle] at hset
        subst hset
        simp only [value]
        cases hc0 : decide (p.rate s.tokenOut = 0) with
        | true =>
          have h0 : p.rate s.tokenOut = 0 := of_decide_eq_true hc0
          have heq : ginOpt m p s = none := by unfold ginOpt; simp [h0]
          rw [heq] at hgin
          simp at hgin
        | false =>
          have hne : p.rate s.tokenOut ≠ 0 := of_decide_eq_false hc0
          have hqeq : y = ginQuote m p s := by
            have heq : ginOpt m p s = some (ginQuote m p s) := by
              unfold ginOpt; simp [hne]
            rw [heq] at hgin
            simp at hgin
            exact hgin.symm
          subst hqeq
          have hsnd := hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hv.1 hv.2.1 hv.2.2
          have hinvMid : m.invariant (scaledBalances p)
            ≤ m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + netInDown p s) s.tokenOut ((scaledBalances p) s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s))) := hsnd.2
          have hyr : ginQuote m p s * p.rate s.tokenOut
            ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := divMulLe _ _
          have hOle : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
            ≤ scaledBalances p s.tokenOut := hsnd.1
          have hInGe : scaledBalances p s.tokenIn + netInDown p s
            ≤ scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := by
            unfold scaledBalances netInDown scaleDown
            exact ginInGe _ _ _ _
          have hOutGe : scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)
            ≤ scaleDown (p.balance s.tokenOut - ginQuote m p s) (p.rate s.tokenOut) := by
            unfold scaledBalances scaleDown
            exact ginOutGe _ _ _ _ hyr hOle hle
          apply Nat.le_trans hinvMid
          apply hw.monotone
          intro k hk2
          have hR : scaledBalances (Pool.mk p.n (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - ginQuote m p s)) p.rate p.fee) k
            = scaleDown ((update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - ginQuote m p s)) k) (p.rate k) := rfl
          rw [hR]
          cases hc1 : decide (k = s.tokenIn) with
          | true =>
            have hi : k = s.tokenIn := of_decide_eq_true hc1
            subst hi
            have e1 : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) s.tokenIn
              = scaledBalances p s.tokenIn + netInDown p s := by simp [update2]
            rw [e1]
            have e2 : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - ginQuote m p s) s.tokenIn
              = p.balance s.tokenIn + s.amount := by simp [update2]
            rw [e2]
            exact hInGe
          | false =>
            have hi : ¬ k = s.tokenIn := of_decide_eq_false hc1
            cases hc2 : decide (k = s.tokenOut) with
            | true =>
              have hj : k = s.tokenOut := of_decide_eq_true hc2
              subst hj
              have e1 : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) s.tokenOut
                = scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by simp [update2, hi]
              rw [e1]
              have e2 : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - ginQuote m p s) s.tokenOut
                = p.balance s.tokenOut - ginQuote m p s := by simp [update2, hi]
              rw [e2]
              exact hOutGe
            | false =>
              have hj : ¬ k = s.tokenOut := of_decide_eq_false hc2
              have e1 : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k
                = scaledBalances p k := by simp [update2, hi, hj]
              rw [e1]
              have e2 : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount) s.tokenOut (p.balance s.tokenOut - ginQuote m p s) k
                = p.balance k := by simp [update2, hi, hj]
              rw [e2]
              unfold scaledBalances scaleDown
              exact Nat.le_refl _
  | givenOut =>
    have hk : s.kind = Kind.givenOut := hc
    have hon : onSwap m p s = goutOpt m p s := by unfold onSwap; simp [hk]
    cases hgout : goutOpt m p s with
    | none =>
      unfold step at hstep
      simp [hv, hon, hgout] at hstep
    | some c =>
      unfold step at hstep
      simp [hv, hon, hgout] at hstep
      have hset : settle p s c = some p' := hstep
      cases hlc : decide (s.amount ≤ p.balance s.tokenOut) with
      | false =>
        have hle : ¬ s.amount ≤ p.balance s.tokenOut := of_decide_eq_false hlc
        unfold settle amountIn amountOut at hset
        rw [hk] at hset
        simp [hle] at hset
      | true =>
        have hle : s.amount ≤ p.balance s.tokenOut := of_decide_eq_true hlc
        unfold settle amountIn amountOut at hset
        rw [hk] at hset
        simp only at hset
        simp [hle] at hset
        subst hset
        simp only [value]
        cases hc1 : decide (p.rate s.tokenIn = 0) with
        | true =>
          have h0 : p.rate s.tokenIn = 0 := of_decide_eq_true hc1
          have heq : goutOpt m p s = none := by unfold goutOpt; simp [h0]
          rw [heq] at hgout
          simp at hgout
        | false =>
          have h1 : p.rate s.tokenIn ≠ 0 := of_decide_eq_false hc1
          cases hc2 : decide (ONE ≤ p.fee) with
          | true =>
            have hcc : ONE ≤ p.fee := of_decide_eq_true hc2
            have heq : goutOpt m p s = none := by unfold goutOpt; simp [h1, hcc]
            rw [heq] at hgout
            simp at hgout
          | false =>
            have h2 : ¬ ONE ≤ p.fee := of_decide_eq_false hc2
            cases hc3 : decide (scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut)) with
            | true =>
              have hcc : scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := of_decide_eq_true hc3
              have heq : goutOpt m p s = none := by unfold goutOpt; simp [h1, hcc]
              rw [heq] at hgout
              simp at hgout
            | false =>
              have h3 : ¬ scaledBalances p s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) := of_decide_eq_false hc3
              have hqeq : c = goutQuote m p s := by
                have heq : goutOpt m p s = some (goutQuote m p s) := by
                  unfold goutOpt; simp [h1, h2, h3]
                rw [heq] at hgout
                simp at hgout
                exact hgout.symm
              subst hqeq
              have hf : p.fee < ONE := by omega
              have hr : 0 < p.rate s.tokenIn := by omega
              have hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := by omega
              have hsnd := hw.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) hv.1 hv.2.1 hv.2.2 hlt
              have hinvMid : m.invariant (scaledBalances p)
                ≤ m.invariant (update2 (scaledBalances p) s.tokenIn ((scaledBalances p) s.tokenIn + outPrice m p s) s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))) := hsnd
              have hch : outPrice m p s * ONE * ONE ≤ goutQuote m p s * (ONE - p.fee) * p.rate s.tokenIn := by
                have hDpos : 0 < goutD p s := by unfold goutD; exact Nat.mul_pos (by omega : 0 < ONE - p.fee) hr
                have hge := ceilGe (goutN m p s) (goutD p s) hDpos
                have hEq : goutQuote m p s * (ONE - p.fee) * p.rate s.tokenIn = goutQuote m p s * goutD p s := by
                  unfold goutD; rw [Nat.mul_assoc]
                rw [hEq]
                show outPrice m p s * ONE * ONE ≤ goutQuote m p s * goutD p s
                have hGN : goutN m p s = ONE * ONE * outPrice m p s := rfl
                have hGQ : goutQuote m p s = (goutN m p s + goutD p s - 1) / goutD p s := rfl
                have hEqN : outPrice m p s * ONE * ONE = goutN m p s := by
                  rw [hGN]
                  simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
                rw [hEqN]
                rw [hGQ]
                exact hge
              have hInGe : scaledBalances p s.tokenIn + outPrice m p s
                ≤ scaleDown (p.balance s.tokenIn + goutQuote m p s) (p.rate s.tokenIn) := by
                unfold scaledBalances outPrice scaleDown
                exact goutInGe _ _ _ _ _ hf hr hch
              have hOutGe : scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)
                ≤ scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
                unfold scaledBalances scaleUp scaleDown
                exact goutOutGe _ _ _ hle
              apply Nat.le_trans hinvMid
              apply hw.monotone
              intro k hk2
              have hR : scaledBalances (Pool.mk p.n (update2 p.balance s.tokenIn (p.balance s.tokenIn + goutQuote m p s) s.tokenOut (p.balance s.tokenOut - s.amount)) p.rate p.fee) k
                = scaleDown ((update2 p.balance s.tokenIn (p.balance s.tokenIn + goutQuote m p s) s.tokenOut (p.balance s.tokenOut - s.amount)) k) (p.rate k) := rfl
              rw [hR]
              cases hc4 : decide (k = s.tokenIn) with
              | true =>
                have hi : k = s.tokenIn := of_decide_eq_true hc4
                subst hi
                have e1 : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + outPrice m p s) s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn
                  = scaledBalances p s.tokenIn + outPrice m p s := by simp [update2]
                rw [e1]
                have e2 : update2 p.balance s.tokenIn (p.balance s.tokenIn + goutQuote m p s) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenIn
                  = p.balance s.tokenIn + goutQuote m p s := by simp [update2]
                rw [e2]
                exact hInGe
              | false =>
                have hi : ¬ k = s.tokenIn := of_decide_eq_false hc4
                cases hc5 : decide (k = s.tokenOut) with
                | true =>
                  have hj : k = s.tokenOut := of_decide_eq_true hc5
                  subst hj
                  have e1 : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + outPrice m p s) s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut
                    = scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by simp [update2, hi]
                  rw [e1]
                  have e2 : update2 p.balance s.tokenIn (p.balance s.tokenIn + goutQuote m p s) s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenOut
                    = p.balance s.tokenOut - s.amount := by simp [update2, hi]
                  rw [e2]
                  exact hOutGe
                | false =>
                  have hj : ¬ k = s.tokenOut := of_decide_eq_false hc5
                  have e1 : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + outPrice m p s) s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k
                    = scaledBalances p k := by simp [update2, hi, hj]
                  rw [e1]
                  have e2 : update2 p.balance s.tokenIn (p.balance s.tokenIn + goutQuote m p s) s.tokenOut (p.balance s.tokenOut - s.amount) k
                    = p.balance k := by simp [update2, hi, hj]
                  rw [e2]
                  unfold scaledBalances scaleDown
                  exact Nat.le_refl _

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  unfold BatchKeepsValue
  intro m p ss p' hw hrun
  induction ss generalizing p p' with
  | nil =>
    simp [run] at hrun
    cases hrun
    exact Nat.le_refl _
  | cons s ss ih =>
    unfold run at hrun
    cases hmid : step onSwap m p s with
    | none => simp [hmid] at hrun
    | some pm =>
      simp [hmid] at hrun
      have hstep : step onSwap m p s = some pm := hmid
      have hle1 : value m p ≤ value m pm := req_swap_keeps_value m p s pm hw hstep
      have hpm_n : pm.n = p.n := by
        unfold step at hmid
        cases hvc : decide (Valid p s) with
        | true =>
          have hv : Valid p s := of_decide_eq_true hvc
          simp [hv] at hmid
          cases himpl : onSwap m p s with
          | none => simp [himpl] at hmid
          | some c =>
            simp [himpl] at hmid
            unfold settle at hmid
            cases hlc : decide (amountOut s c ≤ p.balance s.tokenOut) with
            | true =>
              have hle : amountOut s c ≤ p.balance s.tokenOut := of_decide_eq_true hlc
              simp [hle] at hmid
              cases hmid
              rfl
            | false =>
              have hle : ¬ amountOut s c ≤ p.balance s.tokenOut := of_decide_eq_false hlc
              simp [hle] at hmid
        | false =>
          have hv : ¬ Valid p s := of_decide_eq_false hvc
          simp [hv] at hmid
      have hw2 : WellBehaved m pm.n := by rw [hpm_n]; exact hw
      have hle2 : value m pm ≤ value m p' := ih pm p' hw2 hrun
      exact Nat.le_trans hle1 hle2

end BalancerSwap

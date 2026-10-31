import BalancerSwap.Spec
import ProofForgeFin.DeFi.AMM
namespace BalancerSwap

def mulDown (a b : Nat) : Nat := a * b / ONE

def mulUp (a b : Nat) : Nat := if a * b = 0 then 0 else (a * b - 1) / ONE + 1

def divDown (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some (a * ONE / b)

def divUp (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)

def complement (x : Nat) : Nat := if x < ONE then ONE - x else 0

def upscale (amount scalingFactor : Nat) : Nat := mulDown amount scalingFactor

def upscaleArray (p : Pool) : Nat → Nat := fun k => mulDown (p.balance k) (p.rate k)

def downscaleDown (amount scalingFactor : Nat) : Option Nat := divDown amount scalingFactor

def downscaleUp (amount scalingFactor : Nat) : Option Nat := divUp amount scalingFactor

def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none

def addSwapFeeAmount (amount fee : Nat) : Option Nat := divUp amount (complement fee)

/-- Fixed `_swapGivenIn`: price the exact net amount (fee rounded down, single upscale). -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  let balances := scaledBalances p
  let net := netInDown p s
  let amountOut := m.outGivenIn balances s.tokenIn s.tokenOut net
  downscaleDown amountOut (p.rate s.tokenOut)

/-- Fixed `_swapGivenOut`: round the amount out up, require strict balance check. -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  let balances := scaledBalances p
  let amount := scaleUp s.amount (p.rate s.tokenOut)
  if amount < balances s.tokenOut then
    match downscaleUp (m.inGivenOut balances s.tokenIn s.tokenOut amount) (p.rate s.tokenIn) with
    | none => none
    | some amountIn => addSwapFeeAmount amountIn p.fee
  else none

/-- `onSwap` for a regular swap (fixed rounding). -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

def fooTest1 : Nat := 1

def probeONE : Nat := 3

def probe2 : Nat := 4

def probe3 : Nat := 5

def probeA : Nat := 6

def fooTest2 : Nat := 2

theorem myTestLemma : 0 < ONE := by unfold ONE; omega

def fooTest3 : Nat := 3

def fooProbeA : Nat := 7

theorem complement_eq_of_lt2 (fee : Nat) (h : fee < ONE) : complement fee = ONE - fee := by unfold complement; simp [h]

theorem div_mono_test (x y : Nat) (h : x ≤ y) : x / 1000000000000000000 ≤ (y + 999999999999999999) / 1000000000000000000 := by omega

theorem complement_ne_zero_of_lt (fee : Nat) (h : fee < ONE) : complement fee ≠ 0 := by unfold complement; simp [h]; unfold ONE at h ⊢; omega

theorem divUp_nonzero_test (a b : Nat) (hb : b ≠ 0) (ha : a ≠ 0) : divUp a b ≠ none := by unfold divUp; simp [hb, ha]

theorem check_swapGivenIn_eq (m : PoolMath) (p : Pool) (s : Swap) :
  swapGivenIn m p s = downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := rfl

theorem check_downscale_eq (a r : Nat) :
  downscaleDown a r = divDown a r := rfl

theorem explore_gin (m : PoolMath) (p : Pool) (s : Swap) (y : Nat)
  (h : swapGivenIn m p s = some y) :
  downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) = some y := by
  have e : swapGivenIn m p s = downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := rfl
  rw [e] at h
  exact h

theorem divDown_bound2 (a b y : Nat) (h : divDown a b = some y) : y * b ≤ a * ONE := by
  unfold divDown at h
  by_cases hb : b = 0
  · rw [if_pos hb] at h
    cases h
  · rw [if_neg hb] at h
    by_cases ha : a = 0
    · rw [if_pos ha] at h
      cases h
      rw [ha]
      simp
    · rw [if_neg ha] at h
      cases h
      exact Nat.div_mul_le_self _ _

theorem divDown_upper_aux (a b y : Nat) (hb : b ≠ 0) (h : divDown a b = some y) : a * ONE < (y + 1) * b := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  unfold divDown at h
  simp [hb] at h
  by_cases ha : a = 0
  · subst ha
    simp at h
    subst h
    simp
    exact hbpos
  · simp [ha] at h
    subst h
    have heq : b * (a * ONE / b) + a * ONE % b = a * ONE := Nat.div_add_mod _ _
    have hmod : a * ONE % b < b := Nat.mod_lt _ hbpos
    have hlt : b * (a * ONE / b) + a * ONE % b < b * (a * ONE / b) + b := Nat.add_lt_add_left hmod _
    rw [heq] at hlt
    have hcomm : b * (a * ONE / b) = a * ONE / b * b := Nat.mul_comm _ _
    rw [hcomm] at hlt
    have hsucc : (a * ONE / b + 1) * b = a * ONE / b * b + b := by rw [Nat.add_mul, Nat.one_mul]
    rw [hsucc]
    exact hlt

theorem netLess_le_net_aux (p : Pool) (s : Swap) : netInLessOneDown p s ≤ netInDown p s := by
  unfold netInLessOneDown netInDown
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  omega

theorem divUp_lower_aux2 (a b y : Nat) (h : divUp a b = some y) : a * ONE ≤ y * b := by
  unfold divUp at h
  by_cases hb : b = 0
  · rw [if_pos hb] at h
    cases h
  · rw [if_neg hb] at h
    by_cases ha : a = 0
    · rw [if_pos ha] at h
      cases h
      subst_vars
      simp
    · rw [if_neg ha] at h
      cases h
      have hONEpos : 0 < ONE := by unfold ONE; omega
      have haONEpos : 0 < a * ONE := Nat.mul_pos (Nat.pos_of_ne_zero ha) hONEpos
      have h1le : 1 ≤ a * ONE := haONEpos
      have hsub : a * ONE - 1 + 1 = a * ONE := Nat.sub_add_cancel h1le
      have hdecomp : b * ((a * ONE - 1) / b) + (a * ONE - 1) % b = a * ONE - 1 := Nat.div_add_mod _ _
      have hmodlt : (a * ONE - 1) % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero hb)
      have hsuccmul : ((a * ONE - 1) / b + 1) * b = b * ((a * ONE - 1) / b) + b := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      rw [hsuccmul]
      omega

theorem complement_eq_sub2 (x : Nat) : complement x = ONE - x := by
  unfold complement
  by_cases h : x < ONE
  · simp [h]
  · simp [h]
    omega

theorem divUp_upper_aux2 (a b y : Nat) (h : divUp a b = some y) (hb : b ≠ 0) :
    (y = 0 ∧ a = 0) ∨ (y - 1) * b < a * ONE := by
  unfold divUp at h
  rw [if_neg hb] at h
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl] at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  · rw [if_neg ha] at h
    cases h
    right
    have hONEpos : 0 < ONE := by unfold ONE; omega
    have haONEpos : 0 < a * ONE := Nat.mul_pos (Nat.pos_of_ne_zero ha) hONEpos
    have h1le : 1 ≤ a * ONE := haONEpos
    have hylem : (a * ONE - 1) / b + 1 - 1 = (a * ONE - 1) / b := Nat.add_sub_cancel _ _
    rw [hylem]
    have hle : ((a * ONE - 1) / b) * b ≤ a * ONE - 1 := Nat.div_mul_le_self _ _
    omega

theorem req_given_out_charges_at_most_aux1 (m : PoolMath) (p : Pool) (s : Swap) (c : Nat)
  (h2 : swapGivenOut m p s = some c)
  (hlt : ¬ scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut) : False := by
  unfold swapGivenOut at h2
  simp only [hlt, if_false] at h2
  simp at h2

theorem charges_most_step1 (r0 : Nat) (cf : Nat) (c : Nat) (hadd' : divUp r0 cf = some c) (hcomp_ne : cf ≠ 0) (hc0 : c ≠ 0) : (c - 1) * cf < r0 * ONE := by
  have hupC := divUp_upper_aux2 r0 cf c hadd' hcomp_ne
  cases hupC with
  | inl h =>
    obtain ⟨hy0, _⟩ := h
    contradiction
  | inr h => exact h

theorem charges_most_step2 (P : Nat) (rin : Nat) (r0 : Nat) (hdown' : divUp P rin = some r0) (hrne : rin ≠ 0) (hr0pos : 0 < r0) : (r0 - 1) * rin < P * ONE := by
  have hupR := divUp_upper_aux2 P rin r0 hdown' hrne
  cases hupR with
  | inl h =>
    obtain ⟨hy0, _⟩ := h
    omega
  | inr h => exact h

theorem charges_most_combine (P rin cf r0 c : Nat) (hONEpos : 0 < ONE) (hrate_pos : 0 < rin)
  (hClt : (c - 1) * cf < r0 * ONE) (hRlt : (r0 - 1) * rin < P * ONE) (hr0pos : 0 < r0) :
  (c - 1) * cf * rin < ONE * (ONE * P + rin) := by
  have hstep1 : (c - 1) * cf * rin < r0 * ONE * rin :=
    Nat.mul_lt_mul_of_pos_right hClt hrate_pos
  have hr0mul : r0 * rin = (r0 - 1) * rin + rin := by
    cases r0 with
    | zero => simp at hr0pos
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.add_mul, Nat.one_mul]
  have hr0lt : r0 * rin < P * ONE + rin := by
    rw [hr0mul]; exact Nat.add_lt_add_right hRlt _
  have e : r0 * ONE * rin = (r0 * rin) * ONE := by ac_rfl
  have e2 : ONE * (ONE * P + rin) = (P * ONE + rin) * ONE := by ac_rfl
  have hstep2 : r0 * ONE * rin < ONE * (ONE * P + rin) := by
    rw [e, e2]
    exact Nat.mul_lt_mul_of_pos_right hr0lt hONEpos
  exact Nat.lt_trans hstep1 hstep2

theorem divUp_zero_of_ne (b : Nat) (hb : b ≠ 0) : divUp 0 b = some 0 := by
  unfold divUp
  simp [hb]

theorem r0_ne_zero_of_c_ne_zero (r0 : Nat) (cf c : Nat) (hadd' : divUp r0 cf = some c) (hcomp_ne : cf ≠ 0) (hc0 : c ≠ 0) : r0 ≠ 0 := by
  intro hz
  subst hz
  have hzero := divUp_zero_of_ne cf hcomp_ne
  rw [hzero] at hadd'
  cases hadd'
  exact hc0 rfl

theorem divDown_isSome2 (a b : Nat) (hb : b ≠ 0) : ∃ y, divDown a b = some y := by
  unfold divDown
  simp [hb]
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]

theorem scale_le_of_lt_aux4 (a b r : Nat) (h : b < a) : scaleDown b r ≤ scaleUp a r := by
  unfold scaleDown scaleUp
  have hle : b * r ≤ a * r + (ONE - 1) := by
    have h1 : b * r ≤ a * r := Nat.mul_le_mul_right r (Nat.le_of_lt h)
    omega
  exact Nat.div_le_div_right hle

theorem scale_amount_le_balance_aux4 (a b r : Nat) (h : scaleUp a r < scaleDown b r) : a ≤ b := by
  have htot := Nat.le_total a b
  cases htot with
  | inl hle => exact hle
  | inr hge =>
    have h2 := Nat.lt_or_eq_of_le hge
    cases h2 with
    | inl hlt =>
      have hle := scale_le_of_lt_aux4 a b r hlt
      omega
    | inr heq =>
      omega

theorem divUp_exists_aux7 (a b : Nat) (hb : b ≠ 0) : ∃ y, divUp a b = some y := by
  unfold divUp
  simp only [hb, ↓reduceIte]
  by_cases ha : a = 0
  · simp only [ha, ↓reduceIte]
    exact ⟨0, rfl⟩
  · simp only [ha, ↓reduceIte]
    exact ⟨(a * ONE - 1) / b + 1, rfl⟩

theorem swapOut_eq_aux7 (m : PoolMath) (p : Pool) (s : Swap) (r0 c : Nat)
  (hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut)
  (hr0 : downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0)
  (hc : addSwapFeeAmount r0 p.fee = some c) :
  swapGivenOut m p s = some c := by
  unfold swapGivenOut
  simp only
  rw [if_pos hlt]
  rw [hr0]
  simp only [hc]

theorem scaleDown_add_ge_try2 (a x r : Nat) : scaleDown a r + scaleDown x r ≤ scaleDown (a + x) r := by
  unfold scaleDown
  have hone : 0 < ONE := by unfold ONE; omega
  have h1 : (a * r / ONE) * ONE + (x * r / ONE) * ONE ≤ a * r + x * r := by
    have h1 : (a * r / ONE) * ONE ≤ a * r := Nat.div_mul_le_self _ _
    have h2 : (x * r / ONE) * ONE ≤ x * r := Nat.div_mul_le_self _ _
    omega
  have h2 : (a * r / ONE + x * r / ONE) * ONE ≤ a * r + x * r := by
    have e : (a * r / ONE + x * r / ONE) * ONE = (a * r / ONE) * ONE + (x * r / ONE) * ONE := Nat.add_mul _ _ _
    omega
  have h3 : (a * r / ONE + x * r / ONE) * ONE ≤ (a + x) * r := by
    have e : (a + x) * r = a * r + x * r := Nat.add_mul _ _ _
    omega
  exact (Nat.le_div_iff_mul_le hone).mpr h3

theorem plan0_scaleDown_add_le (a b r : Nat) :
    scaleDown a r + scaleDown b r ≤ scaleDown (a + b) r := by
  unfold scaleDown
  have hone : 0 < ONE := by unfold ONE; omega
  have h1 : (a * r / ONE) * ONE ≤ a * r := Nat.div_mul_le_self _ _
  have h2 : (b * r / ONE) * ONE ≤ b * r := Nat.div_mul_le_self _ _
  have h3 : (a * r / ONE + b * r / ONE) * ONE ≤ (a + b) * r := by
    have e : (a * r / ONE + b * r / ONE) * ONE = (a * r / ONE) * ONE + (b * r / ONE) * ONE := Nat.add_mul _ _ _
    have e2 : (a + b) * r = a * r + b * r := Nat.add_mul _ _ _
    omega
  exact (Nat.le_div_iff_mul_le hone).mpr h3




theorem plan0_scaleDown_sub_le_of_mul_le (b out y r : Nat)
    (hy : y * r ≤ out * ONE) (hout : out ≤ scaleDown b r) :
    scaleDown b r - out ≤ scaleDown (b - y) r := by
  unfold scaleDown at *
  have hONEpos : 0 < ONE := by unfold ONE; omega
  by_cases hr : r = 0
  · subst hr
    simp only [Nat.mul_zero, Nat.zero_div] at hout ⊢
    omega
  · have hA : (b * r / ONE) * ONE ≤ b * r := Nat.div_mul_le_self _ _
    have houtONE : out * ONE ≤ (b * r / ONE) * ONE :=
      Nat.mul_le_mul_right ONE hout
    have hsub_eq : (b - y) * r = b * r - y * r := Nat.sub_mul b y r
    rw [hsub_eq]
    have h_eq1 : ((b * r / ONE) - out) * ONE = (b * r / ONE) * ONE - out * ONE := Nat.sub_mul _ _ _
    have h1 : (b * r / ONE) * ONE - out * ONE ≤ b * r - out * ONE :=
      Nat.sub_le_sub_right hA _
    have h2 : b * r - out * ONE ≤ b * r - y * r := Nat.sub_le_sub_left hy _
    have hle : ((b * r / ONE) - out) * ONE ≤ b * r - y * r := by
      rw [h_eq1]
      exact Nat.le_trans h1 h2
    exact (Nat.le_div_iff_mul_le hONEpos).mpr hle




theorem plan0_scaleDown_charge_le_of_divUp_chain (P rin fee r0 c : Nat)
    (h1 : divUp P rin = some r0) (h2 : addSwapFeeAmount r0 fee = some c) :
    P ≤ scaleDown c rin := by
  have hlow1 : P * ONE ≤ r0 * rin := divUp_lower_aux2 P rin r0 h1
  have hcomp_eq : complement fee = ONE - fee := complement_eq_sub2 fee
  have hlow2 : r0 * ONE ≤ c * complement fee := by
    unfold addSwapFeeAmount at h2
    rw [hcomp_eq] at h2 ⊢
    exact divUp_lower_aux2 r0 (ONE - fee) c h2
  have hONEpos : 0 < ONE := by unfold ONE; omega
  have hcomp_le : complement fee ≤ ONE := by rw [hcomp_eq]; exact Nat.sub_le ONE fee
  have hA : (P * ONE) * ONE ≤ (r0 * rin) * ONE :=
    Nat.mul_le_mul hlow1 (Nat.le_refl ONE)
  have heq1 : (r0 * rin) * ONE = (r0 * ONE) * rin := by ac_rfl
  rw [heq1] at hA
  have hB : (r0 * ONE) * rin ≤ (c * complement fee) * rin :=
    Nat.mul_le_mul hlow2 (Nat.le_refl rin)
  have hC : (c * complement fee) * rin ≤ (c * ONE) * rin := by
    have h1c : c * complement fee ≤ c * ONE := Nat.mul_le_mul (Nat.le_refl c) hcomp_le
    exact Nat.mul_le_mul h1c (Nat.le_refl rin)
  have heq2 : (c * ONE) * rin = (c * rin) * ONE := by ac_rfl
  rw [heq2] at hC
  have htrans : (P * ONE) * ONE ≤ (c * rin) * ONE := Nat.le_trans hA (Nat.le_trans hB hC)
  have hmid : P * ONE ≤ c * rin := Nat.le_of_mul_le_mul_right htrans hONEpos
  unfold scaleDown
  exact (Nat.le_div_iff_mul_le hONEpos).mpr hmid




theorem plan0_test_add_le (a b r : Nat) :
    scaleDown a r + scaleDown b r ≤ scaleDown (a + b) r := by
  unfold scaleDown
  have hone : 0 < ONE := by unfold ONE; omega
  have h1 : (a * r / ONE) * ONE ≤ a * r := Nat.div_mul_le_self _ _
  have h2 : (b * r / ONE) * ONE ≤ b * r := Nat.div_mul_le_self _ _
  have h3 : (a * r / ONE + b * r / ONE) * ONE ≤ (a + b) * r := by
    have e : (a * r / ONE + b * r / ONE) * ONE = (a * r / ONE) * ONE + (b * r / ONE) * ONE := Nat.add_mul _ _ _
    have e2 : (a + b) * r = a * r + b * r := Nat.add_mul _ _ _
    omega
  exact (Nat.le_div_iff_mul_le hone).mpr h3

theorem plan0_netInDown_le_scaleDown (p : Pool) (s : Swap) :
    netInDown p s ≤ scaleDown s.amount (p.rate s.tokenIn) := by
  unfold netInDown scaleDown
  have hONEpos : 0 < ONE := by unfold ONE; omega
  have hOOpos : 0 < ONE * ONE := Nat.mul_pos hONEpos hONEpos
  -- N1 ≤ N2 * ONE
  have hNle : s.amount * (ONE - p.fee) * p.rate s.tokenIn ≤ (s.amount * p.rate s.tokenIn) * ONE := by
    have h1 : s.amount * (ONE - p.fee) ≤ s.amount * ONE := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    calc s.amount * (ONE - p.fee) * p.rate s.tokenIn
        = (s.amount * (ONE - p.fee)) * p.rate s.tokenIn := by ac_rfl
      _ ≤ (s.amount * ONE) * p.rate s.tokenIn := Nat.mul_le_mul_right _ h1
      _ = (s.amount * p.rate s.tokenIn) * ONE := by ac_rfl
  have hdiv : (s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE)) * (ONE * ONE)
    ≤ s.amount * (ONE - p.fee) * p.rate s.tokenIn := Nat.div_mul_le_self _ _
  have hle1 : ((s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE)) * ONE) * ONE
    ≤ (s.amount * p.rate s.tokenIn) * ONE := by
    have e : ((s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE)) * ONE) * ONE
      = (s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE)) * (ONE * ONE) := by ac_rfl
    rw [e]
    exact Nat.le_trans hdiv hNle
  have hle2 : (s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE)) * ONE
    ≤ s.amount * p.rate s.tokenIn :=
    Nat.le_of_mul_le_mul_right hle1 hONEpos
  exact (Nat.le_div_iff_mul_le hONEpos).mpr hle2

theorem plan0_sub_le_tmp (b out y r : Nat)
    (hy : y * r ≤ out * ONE) (hout : out ≤ scaleDown b r) :
    scaleDown b r - out ≤ scaleDown (b - y) r := by
  unfold scaleDown at *
  have hONEpos : 0 < ONE := by unfold ONE; omega
  by_cases hr : r = 0
  · subst hr
    simp only [Nat.mul_zero, Nat.zero_div] at hout ⊢
    omega
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hA : (b * r / ONE) * ONE ≤ b * r := Nat.div_mul_le_self _ _
    have houtONE : out * ONE ≤ (b * r / ONE) * ONE :=
      Nat.mul_le_mul_right ONE hout
    have hyb : y * r ≤ b * r := Nat.le_trans hy (Nat.le_trans houtONE hA)
    have hsub_eq : (b - y) * r = b * r - y * r := Nat.sub_mul b y r
    rw [hsub_eq]
    have h_eq1 : ((b * r / ONE) - out) * ONE = (b * r / ONE) * ONE - out * ONE := Nat.sub_mul _ _ _
    have h1 : (b * r / ONE) * ONE - out * ONE ≤ b * r - out * ONE :=
      Nat.sub_le_sub_right hA _
    have h2 : b * r - out * ONE ≤ b * r - y * r := Nat.sub_le_sub_left hy _
    have hle : ((b * r / ONE) - out) * ONE ≤ b * r - y * r := by
      rw [h_eq1]
      exact Nat.le_trans h1 h2
    exact (Nat.le_div_iff_mul_le hONEpos).mpr hle

theorem plan0_scaleDown_sub_le_of_mul_le_fix : ∀ (b out y r : Nat),
    (y * r ≤ out * ONE) → (out ≤ scaleDown b r) →
    scaleDown b r - out ≤ scaleDown (b - y) r := by
  intro b out y r hy hout
  exact plan0_sub_le_tmp b out y r hy hout

theorem plan0_add_mul_tmp3 (b t r : Nat) (hlt : t < b) :
    b * r = (b - t) * r + t * r := by
  have h1 : (b - t) + t = b := Nat.sub_add_cancel (Nat.le_of_lt hlt)
  have e : ((b - t) + t) * r = (b - t) * r + t * r := Nat.add_mul (b - t) t r
  rw [h1] at e
  exact e

theorem plan0_key_tmp4 (b t r : Nat) (hlt : t < b) :
    b * r / ONE ≤ (b - t) * r / ONE + (t * r + (ONE - 1)) / ONE := by
  have hmul := plan0_add_mul_tmp3 b t r hlt
  unfold ONE at hmul ⊢
  omega

theorem plan0_key_all_tmp5 (b t r : Nat) :
    b * r / ONE ≤ (b - t) * r / ONE + (t * r + (ONE - 1)) / ONE := by
  have htot := Nat.le_total b t
  cases htot with
  | inl hbt =>
    have hsub : b - t = 0 := Nat.sub_eq_zero_of_le hbt
    rw [hsub]
    simp only [Nat.zero_mul, Nat.zero_div, Nat.zero_add]
    have hbr : b * r ≤ t * r := Nat.mul_le_mul_right r hbt
    have hle2 : b * r ≤ t * r + (ONE - 1) := Nat.le_trans hbr (Nat.le_add_right _ _)
    exact Nat.div_le_div_right hle2
  | inr hge =>
    have hlt_or : t < b ∨ t = b := by omega
    cases hlt_or with
    | inl hlt => exact plan0_key_tmp4 b t r hlt
    | inr heq =>
      have hsub : b - t = 0 := by omega
      rw [hsub]
      simp only [Nat.zero_mul, Nat.zero_div, Nat.zero_add]
      rw [← heq]
      exact Nat.div_le_div_right (Nat.le_add_right _ _)







theorem plan1_scaleDown_le_add_scaleUp_auxfix (b t r : Nat) :
    scaleDown b r ≤ scaleDown (b - t) r + scaleUp t r := by
  unfold scaleDown scaleUp
  exact plan0_key_all_tmp5 b t r


theorem plan1_sub_add_mul_eq (b t r : Nat) (h : t ≤ b) :
    b * r = (b - t) * r + t * r := by
  have h1 : (b - t) + t = b := Nat.sub_add_cancel h
  calc b * r = ((b - t) + t) * r := by rw [h1]
    _ = (b - t) * r + t * r := by rw [Nat.add_mul]

theorem plan1_mul_le_sub_mul_add (b t r : Nat) :
    b * r ≤ (b - t) * r + t * r := by
  have htot := Nat.le_total b t
  cases htot with
  | inl hbt =>
    have hsub : b - t = 0 := Nat.sub_eq_zero_of_le hbt
    rw [hsub]
    simp only [Nat.zero_mul, Nat.zero_add]
    exact Nat.mul_le_mul_right r hbt
  | inr hge =>
    have heq := plan1_sub_add_mul_eq b t r hge
    omega

theorem plan1_div_add_le (u v : Nat) :
    (u + v) / ONE ≤ u / ONE + (v + (ONE - 1)) / ONE := by
  unfold ONE
  omega

theorem plan1_scaleDown_le_add_scaleUp_proof : ∀ (b t r : Nat),
    scaleDown b r ≤ scaleDown (b - t) r + scaleUp t r := by
  intro b t r
  unfold scaleDown scaleUp
  have hm : b * r ≤ (b - t) * r + t * r := plan1_mul_le_sub_mul_add b t r
  have h1 : b * r / ONE ≤ ((b - t) * r + t * r) / ONE := Nat.div_le_div_right hm
  have h2 : ((b - t) * r + t * r) / ONE ≤ (b - t) * r / ONE + (t * r + (ONE - 1)) / ONE :=
    plan1_div_add_le ((b - t) * r) (t * r)
  exact Nat.le_trans h1 h2

theorem plan1_alt_using_early (b t r : Nat) :
    scaleDown b r ≤ scaleDown (b - t) r + scaleUp t r := by
  unfold scaleDown scaleUp
  exact plan0_key_all_tmp5 b t r

theorem plan1_scaleDown_le_add_scaleUp (b t r : Nat) :
    scaleDown b r ≤ scaleDown (b - t) r + scaleUp t r := by
  unfold scaleDown scaleUp
  exact plan0_key_all_tmp5 b t r

theorem tmp_test_sub_le (b t r : Nat) :
    scaleDown b r - scaleUp t r ≤ scaleDown (b - t) r := by
  have h := plan1_scaleDown_le_add_scaleUp b t r
  omega

theorem plan0_scaleDown_sub_scaleUp_le (b t r : Nat) :
    scaleDown b r - scaleUp t r ≤ scaleDown (b - t) r := by
  have h := plan1_scaleDown_le_add_scaleUp b t r
  omega

theorem testCharge (P rin fee r0 c : Nat)
    (h1 : divUp P rin = some r0) (h2 : addSwapFeeAmount r0 fee = some c) :
    P ≤ scaleDown c rin := by
  have hlow1 : P * ONE ≤ r0 * rin := divUp_lower_aux2 P rin r0 h1
  have hcomp_eq : complement fee = ONE - fee := complement_eq_sub2 fee
  have hlow2 : r0 * ONE ≤ c * complement fee := by
    unfold addSwapFeeAmount at h2
    rw [hcomp_eq] at h2 ⊢
    exact divUp_lower_aux2 r0 (ONE - fee) c h2
  have hONEpos : 0 < ONE := by unfold ONE; omega
  have hcomp_le : complement fee ≤ ONE := by rw [hcomp_eq]; exact Nat.sub_le ONE fee
  have hA : (P * ONE) * ONE ≤ (r0 * rin) * ONE :=
    Nat.mul_le_mul hlow1 (Nat.le_refl ONE)
  have heq1 : (r0 * rin) * ONE = (r0 * ONE) * rin := by ac_rfl
  rw [heq1] at hA
  have hB : (r0 * ONE) * rin ≤ (c * complement fee) * rin :=
    Nat.mul_le_mul hlow2 (Nat.le_refl rin)
  have hC : (c * complement fee) * rin ≤ (c * ONE) * rin := by
    have h1c : c * complement fee ≤ c * ONE := Nat.mul_le_mul (Nat.le_refl c) hcomp_le
    exact Nat.mul_le_mul h1c (Nat.le_refl rin)
  have heq2 : (c * ONE) * rin = (c * rin) * ONE := by ac_rfl
  rw [heq2] at hC
  have htrans : (P * ONE) * ONE ≤ (c * rin) * ONE := Nat.le_trans hA (Nat.le_trans hB hC)
  have hmid : P * ONE ≤ c * rin := Nat.le_of_mul_le_mul_right htrans hONEpos
  unfold scaleDown
  exact (Nat.le_div_iff_mul_le hONEpos).mpr hmid

theorem plan0_scaleDown_charge_le_of_divUp_chain_proof (P rin fee r0 c : Nat)
    (h1 : divUp P rin = some r0) (h2 : addSwapFeeAmount r0 fee = some c) :
    P ≤ scaleDown c rin := by
  have hlow1 : P * ONE ≤ r0 * rin := divUp_lower_aux2 P rin r0 h1
  have hcomp_eq : complement fee = ONE - fee := complement_eq_sub2 fee
  have hlow2 : r0 * ONE ≤ c * complement fee := by
    unfold addSwapFeeAmount at h2
    rw [hcomp_eq] at h2 ⊢
    exact divUp_lower_aux2 r0 (ONE - fee) c h2
  have hONEpos : 0 < ONE := by unfold ONE; omega
  have hcomp_le : complement fee ≤ ONE := by rw [hcomp_eq]; exact Nat.sub_le ONE fee
  have hA : (P * ONE) * ONE ≤ (r0 * rin) * ONE :=
    Nat.mul_le_mul hlow1 (Nat.le_refl ONE)
  have heq1 : (r0 * rin) * ONE = (r0 * ONE) * rin := by ac_rfl
  rw [heq1] at hA
  have hB : (r0 * ONE) * rin ≤ (c * complement fee) * rin :=
    Nat.mul_le_mul hlow2 (Nat.le_refl rin)
  have hC : (c * complement fee) * rin ≤ (c * ONE) * rin := by
    have h1c : c * complement fee ≤ c * ONE := Nat.mul_le_mul (Nat.le_refl c) hcomp_le
    exact Nat.mul_le_mul h1c (Nat.le_refl rin)
  have heq2 : (c * ONE) * rin = (c * rin) * ONE := by ac_rfl
  rw [heq2] at hC
  have htrans : (P * ONE) * ONE ≤ (c * rin) * ONE := Nat.le_trans hA (Nat.le_trans hB hC)
  have hmid : P * ONE ≤ c * rin := Nat.le_of_mul_le_mul_right htrans hONEpos
  unfold scaleDown
  exact (Nat.le_div_iff_mul_le hONEpos).mpr hmid

theorem plan0_update2_le_of_parts_check (b b' : Nat → Nat) (i j x y : Nat)
    (hij : i ≠ j) (hi : b i + x ≤ b' i) (hj : b j - y ≤ b' j)
    (hother : ∀ k, k ≠ i → k ≠ j → b k ≤ b' k) :
    ∀ k, update2 b i (b i + x) j (b j - y) k ≤ b' k := by
  intro k
  unfold update2
  by_cases hki : k = i
  · subst hki
    simp only [↓reduceIte]
    exact hi
  · simp only [hki, ↓reduceIte]
    by_cases hkj : k = j
    · subst hkj
      simp only [↓reduceIte]
      exact hj
    · simp only [hkj, ↓reduceIte]
      exact hother k hki hkj

theorem plan0_update2_le_of_parts (b b' : Nat → Nat) (i j x y : Nat)
    (hij : i ≠ j) (hi : b i + x ≤ b' i) (hj : b j - y ≤ b' j)
    (hother : ∀ k, k ≠ i → k ≠ j → b k ≤ b' k) :
    ∀ k, update2 b i (b i + x) j (b j - y) k ≤ b' k := by
  intro k
  unfold update2
  by_cases hki : k = i
  · subst hki
    simp only [↓reduceIte]
    exact hi
  · simp only [hki, ↓reduceIte]
    by_cases hkj : k = j
    · subst hkj
      simp only [↓reduceIte]
      exact hj
    · simp only [hkj, ↓reduceIte]
      exact hother k hki hkj

theorem hother_fix_test (p : Pool) (s : Swap) (c k : Nat) (hki : k ≠ s.tokenIn) (hkj : k ≠ s.tokenOut) :
    (scaledBalances p) k ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k := by
  have e : (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k) = scaledBalances p k := by
    simp only [scaledBalances, update2, hki, hkj, ↓reduceIte]
  rw [← e]
  exact Nat.le_refl _

theorem req_swap_keeps_value_test2 : SwapKeepsValue onSwap := by
  intro m p s p' hw hstep
  unfold step at hstep
  by_cases hv : Valid p s
  · simp only [hv, ↓reduceIte] at hstep
    cases himpl : onSwap m p s with
    | none => simp [himpl] at hstep
    | some c =>
      simp only [himpl] at hstep
      have hset : settle p s c = some p' := hstep
      unfold settle at hset
      by_cases hle : amountOut s c ≤ p.balance s.tokenOut
      · simp only [hle, ↓reduceIte] at hset
        cases hset
        cases hkind : s.kind with
        | givenIn =>
          have hval : Valid p s := hv
          obtain ⟨hne, hi, hj⟩ := hval
          have hne_symm : s.tokenOut ≠ s.tokenIn := Ne.symm hne
          have hon : swapGivenIn m p s = some c := by
            have h : onSwap m p s = some c := himpl
            unfold onSwap at h
            rw [hkind] at h
            exact h
          have heq : downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) = some c := by
            have e : swapGivenIn m p s = downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := rfl
            rw [e] at hon
            exact hon
          have hbound : c * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
            divDown_bound2 _ _ _ heq
          have hsound := hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hne hi hj
          obtain ⟨hle_out, hinv⟩ := hsound
          have hamout : amountOut s c = c := by simp [amountOut, hkind]
          have hamin : amountIn s c = s.amount := by simp [amountIn, hkind]
          have hdom : ∀ k, k < p.n →
              update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k
              ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k := by
            intro k hk
            have hi_le : scaledBalances p s.tokenIn + netInDown p s ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn := by
              have h1 : netInDown p s ≤ scaleDown s.amount (p.rate s.tokenIn) := plan0_netInDown_le_scaleDown p s
              have h2 : scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) + scaleDown s.amount (p.rate s.tokenIn) ≤ scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := plan0_test_add_le _ _ _
              have e1 : scaledBalances p s.tokenIn = scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) := rfl
              have e2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn = scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := by
                unfold scaledBalances scaleDown update2
                simp [hamin]
              rw [e1, e2]
              omega
            have hj_le : scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut := by
              have e : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut = scaleDown (p.balance s.tokenOut - c) (p.rate s.tokenOut) := by
                unfold scaledBalances update2
                simp [hamout, hne_symm]
              rw [e]
              have e2 : scaledBalances p s.tokenOut = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
              rw [e2]
              exact plan0_sub_le_tmp _ _ _ _ hbound hle_out
            have hother : ∀ k, k ≠ s.tokenIn → k ≠ s.tokenOut →
                (scaledBalances p) k ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k :=
              fun k hki hkj => hother_fix_test p s c k hki hkj
            have hgen := plan0_update2_le_of_parts (scaledBalances p) (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) s.tokenIn s.tokenOut (netInDown p s) (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) hne hi_le hj_le hother k
            exact hgen
          have hmono := hw.monotone _ _ (fun k hk => hdom k hk)
          have hval_eq1 : value m p = m.invariant (scaledBalances p) := rfl
          have hval_eq2 : value m { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } = m.invariant (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) := rfl
          rw [hval_eq1, hval_eq2]
          exact Nat.le_trans hinv hmono
        | givenOut =>
          have hval : Valid p s := hv
          obtain ⟨hne, hi, hj⟩ := hval
          have hne_symm : s.tokenOut ≠ s.tokenIn := Ne.symm hne
          have hon : swapGivenOut m p s = some c := by
            have h : onSwap m p s = some c := himpl
            unfold onSwap at h
            rw [hkind] at h
            exact h
          have hamout : amountOut s c = s.amount := by simp [amountOut, hkind]
          have hamin : amountIn s c = c := by simp [amountIn, hkind]
          unfold swapGivenOut at hon
          dsimp only at hon
          by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
          · rw [if_pos hlt] at hon
            obtain ⟨r0, hdown, hadd⟩ : ∃ r0, downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 ∧ addSwapFeeAmount r0 p.fee = some c := by
              cases hdd : downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
              | none => rw [hdd] at hon; simp at hon
              | some r0 => rw [hdd] at hon; exact ⟨r0, rfl, hon⟩
            have hdown' : divUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 := by
              unfold downscaleUp at hdown; exact hdown
            have hsound := hw.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) hne hi hj hlt
            have hcharge : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ scaleDown c (p.rate s.tokenIn) :=
              testCharge _ _ _ _ _ hdown' hadd
            have hdom : ∀ k, k < p.n →
                update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k
                ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k := by
              intro k hk
              have hi_le : scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn := by
                have h2 : scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) + scaleDown c (p.rate s.tokenIn) ≤ scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := plan0_test_add_le _ _ _
                have e1 : scaledBalances p s.tokenIn = scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) := rfl
                have e2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn = scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := by
                  unfold scaledBalances scaleDown update2
                  simp [hamin]
                rw [e1, e2]
                omega
              have hj_le : scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut := by
                have e : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut = scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
                  unfold scaledBalances update2
                  simp [hamout, hne_symm]
                rw [e]
                have e2 : scaledBalances p s.tokenOut = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
                rw [e2]
                exact plan0_scaleDown_sub_scaleUp_le _ _ _
              have hother : ∀ k, k ≠ s.tokenIn → k ≠ s.tokenOut →
                  (scaledBalances p) k ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k :=
                fun k hki hkj => hother_fix_test p s c k hki hkj
              have hgen := plan0_update2_le_of_parts (scaledBalances p) (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) s.tokenIn s.tokenOut (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (scaleUp s.amount (p.rate s.tokenOut)) hne hi_le hj_le hother k
              exact hgen
            have hmono := hw.monotone _ _ (fun k hk => hdom k hk)
            have hval_eq1 : value m p = m.invariant (scaledBalances p) := rfl
            have hval_eq2 : value m { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } = m.invariant (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) := rfl
            rw [hval_eq1, hval_eq2]
            exact Nat.le_trans hsound hmono
          · rw [if_neg hlt] at hon
            simp at hon
      · simp [hle] at hset
  · simp [hv] at hstep

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hw hkind hval hrate hfee
  have hrate_ne : p.rate s.tokenOut ≠ 0 := Nat.pos_iff_ne_zero.mp hrate
  have hsome : ∃ y, swapGivenIn m p s = some y := by
    unfold swapGivenIn
    dsimp only
    have e : downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) = divDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := rfl
    rw [e]
    exact divDown_isSome2 _ _ hrate_ne
  obtain ⟨y, hy⟩ := hsome
  have honSwap : onSwap m p s = some y := by unfold onSwap; rw [hkind]; exact hy
  have hbound : y * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    divDown_bound2 _ _ _ hy
  have hsound := hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hval.1 hval.2.1 hval.2.2
  obtain ⟨hle_out, _⟩ := hsound
  have hle2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤ scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := hle_out
  have hy_le : y ≤ p.balance s.tokenOut := by
    have h1 : y * p.rate s.tokenOut ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
      unfold scaleDown at hle2
      have h2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE ≤ (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE := Nat.mul_le_mul_right _ hle2
      have h3 : (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := Nat.div_mul_le_self _ _
      omega
    exact Nat.le_of_mul_le_mul_right h1 hrate
  have hstep_eq : step onSwap m p s = settle p s y := by unfold step; simp [hval, honSwap]
  rw [hstep_eq]
  have hamout : amountOut s y = y := by simp [amountOut, hkind]
  unfold settle
  rw [hamout]
  simp [hy_le]

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hw hkind hval hrate hfee hscale
  have hrate_ne : p.rate s.tokenIn ≠ 0 := Nat.pos_iff_ne_zero.mp hrate
  have hcomp_ne : complement p.fee ≠ 0 := complement_ne_zero_of_lt p.fee hfee
  have hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := hscale
  obtain ⟨r0, hr0⟩ : ∃ r0, downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 := by
    unfold downscaleUp
    exact divUp_exists_aux7 _ _ hrate_ne
  obtain ⟨c, hc⟩ : ∃ c, addSwapFeeAmount r0 p.fee = some c := by
    unfold addSwapFeeAmount
    exact divUp_exists_aux7 _ _ hcomp_ne
  have hswap : swapGivenOut m p s = some c := swapOut_eq_aux7 m p s r0 c hlt hr0 hc
  have honSwap : onSwap m p s = some c := by unfold onSwap; rw [hkind]; exact hswap
  have hle_bal : s.amount ≤ p.balance s.tokenOut :=
    scale_amount_le_balance_aux4 s.amount (p.balance s.tokenOut) (p.rate s.tokenOut) hscale
  have hstep_eq : step onSwap m p s = settle p s c := by unfold step; simp [hval, honSwap]
  rw [hstep_eq]
  have hamout : amountOut s c = s.amount := by simp [amountOut, hkind]
  unfold settle
  rw [hamout]
  simp [hle_bal]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y _ hkind hval himpl
  have h2 : swapGivenIn m p s = some y := by
    unfold onSwap at himpl
    rw [hkind] at himpl
    exact himpl
  have h3 : downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) = some y := by
    have e : swapGivenIn m p s = downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := rfl
    rw [e] at h2
    exact h2
  have h4 : y * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    divDown_bound2 _ _ _ h3
  calc y * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := h4
    _ = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := Nat.mul_comm _ _

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hkind hval himpl
  have h2 : swapGivenIn m p s = some y := by
    unfold onSwap at himpl
    rw [hkind] at himpl
    exact himpl
  have heq : swapGivenIn m p s = downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := rfl
  rw [heq] at h2
  unfold downscaleDown at h2
  have hrne : p.rate s.tokenOut ≠ 0 := by
    intro hz
    unfold divDown at h2
    simp [hz] at h2
  have hup := divDown_upper_aux (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) y hrne h2
  have hle := netLess_le_net_aux p s
  have hmono1 := hmono.1
  have hprice_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := hmono1 _ _ _ _ _ hle
  have hmul_le : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := Nat.mul_le_mul_left _ hprice_le
  have hcomm : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := Nat.mul_comm _ _
  rw [hcomm] at hmul_le
  calc ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
      ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE := hmul_le
    _ < (y + 1) * p.rate s.tokenOut := hup

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c _ hkind hval himpl
  have h2 : swapGivenOut m p s = some c := by
    unfold onSwap at himpl
    rw [hkind] at himpl
    exact himpl
  unfold swapGivenOut at h2
  dsimp only at h2
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
  · rw [if_pos hlt] at h2
    have hcase : ∃ r0, downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 ∧ addSwapFeeAmount r0 p.fee = some c := by
      cases hdd : downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
      | none =>
        rw [hdd] at h2
        simp at h2
      | some r0 =>
        rw [hdd] at h2
        exact ⟨r0, rfl, h2⟩
    obtain ⟨r0, hdown, hadd⟩ := hcase
    unfold downscaleUp at hdown
    unfold addSwapFeeAmount at hadd
    rw [complement_eq_sub2] at hadd
    have hPdef : outPrice m p s = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := rfl
    have h1 : (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) * ONE ≤ r0 * p.rate s.tokenIn := divUp_lower_aux2 _ _ _ hdown
    have h2b : r0 * ONE ≤ c * (ONE - p.fee) := divUp_lower_aux2 _ _ _ hadd
    rw [hPdef]
    have e1 : ONE * ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE := by ac_rfl
    have e2 : r0 * p.rate s.tokenIn * ONE = r0 * ONE * p.rate s.tokenIn := by ac_rfl
    have stepA : (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE ≤ (r0 * p.rate s.tokenIn) * ONE := Nat.mul_le_mul_right _ h1
    have stepB : r0 * ONE * p.rate s.tokenIn ≤ c * (ONE - p.fee) * p.rate s.tokenIn := Nat.mul_le_mul_right _ h2b
    rw [e1]
    rw [e2] at stepA
    exact Nat.le_trans stepA stepB
  · rw [if_neg hlt] at h2
    simp at h2

theorem req_given_out_charges_at_most  : GivenOutChargesAtMost onSwap := by
  intro m p s c _ hkind hval himpl
  have h2 : swapGivenOut m p s = some c := by
    unfold onSwap at himpl; rw [hkind] at himpl; exact himpl
  unfold swapGivenOut at h2
  dsimp only at h2
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
  · rw [if_pos hlt] at h2
    obtain ⟨r0, hdown, hadd⟩ : ∃ r0, downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 ∧ addSwapFeeAmount r0 p.fee = some c := by
      cases hdd : downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
      | none => rw [hdd] at h2; simp at h2
      | some r0 => rw [hdd] at h2; exact ⟨r0, rfl, h2⟩
    have hdown' : divUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 := by
      unfold downscaleUp at hdown; exact hdown
    have hadd' : divUp r0 (complement p.fee) = some c := by
      unfold addSwapFeeAmount at hadd; exact hadd
    have hrne : p.rate s.tokenIn ≠ 0 := by
      intro hz; rw [hz] at hdown'; unfold divUp at hdown'; simp at hdown'
    have hcomp_ne : complement p.fee ≠ 0 := by
      intro hz; rw [hz] at hadd'; unfold divUp at hadd'; simp at hadd'
    have hCf : complement p.fee = ONE - p.fee := complement_eq_sub2 _
    have hONEpos : 0 < ONE := by unfold ONE; omega
    have hrate_pos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrne
    have hPeq : outPrice m p s = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := rfl
    rw [hPeq]
    have hgoal_eq : (c - 1) * (ONE - p.fee) * p.rate s.tokenIn = (c - 1) * complement p.fee * p.rate s.tokenIn := by rw [hCf]
    rw [hgoal_eq]
    by_cases hc0 : c = 0
    · subst hc0
      simp only [Nat.zero_sub, Nat.zero_mul]
      have harg : 0 < ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn := by omega
      have hRHS : 0 < ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) :=
        Nat.mul_pos hONEpos harg
      omega
    · have hr0ne := r0_ne_zero_of_c_ne_zero r0 (complement p.fee) c hadd' hcomp_ne hc0
      have hr0pos : 0 < r0 := Nat.pos_of_ne_zero hr0ne
      have hClt := charges_most_step1 r0 (complement p.fee) c hadd' hcomp_ne hc0
      have hRlt := charges_most_step2 (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) r0 hdown' hrne hr0pos
      exact charges_most_combine _ _ _ _ _ hONEpos hrate_pos hClt hRlt hr0pos
  · rw [if_neg hlt] at h2
    simp at h2

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hw hstep
  unfold step at hstep
  by_cases hv : Valid p s
  · simp only [hv, ↓reduceIte] at hstep
    cases himpl : onSwap m p s with
    | none => simp [himpl] at hstep
    | some c =>
      simp only [himpl] at hstep
      have hset : settle p s c = some p' := hstep
      unfold settle at hset
      by_cases hle : amountOut s c ≤ p.balance s.tokenOut
      · simp only [hle, ↓reduceIte] at hset
        cases hset
        cases hkind : s.kind with
        | givenIn =>
          have hval : Valid p s := hv
          obtain ⟨hne, hi, hj⟩ := hval
          have hne_symm : s.tokenOut ≠ s.tokenIn := Ne.symm hne
          have hon : swapGivenIn m p s = some c := by
            have h : onSwap m p s = some c := himpl
            unfold onSwap at h
            rw [hkind] at h
            exact h
          have heq : downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) = some c := by
            have e : swapGivenIn m p s = downscaleDown (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) (p.rate s.tokenOut) := rfl
            rw [e] at hon
            exact hon
          have hbound : c * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
            divDown_bound2 _ _ _ heq
          have hsound := hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) hne hi hj
          obtain ⟨hle_out, hinv⟩ := hsound
          have hamout : amountOut s c = c := by simp [amountOut, hkind]
          have hamin : amountIn s c = s.amount := by simp [amountIn, hkind]
          have hdom : ∀ k, k < p.n →
              update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + netInDown p s) s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) k
              ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k := by
            intro k hk
            have hi_le : scaledBalances p s.tokenIn + netInDown p s ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn := by
              have h1 : netInDown p s ≤ scaleDown s.amount (p.rate s.tokenIn) := plan0_netInDown_le_scaleDown p s
              have h2 : scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) + scaleDown s.amount (p.rate s.tokenIn) ≤ scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := plan0_test_add_le _ _ _
              have e1 : scaledBalances p s.tokenIn = scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) := rfl
              have e2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn = scaleDown (p.balance s.tokenIn + s.amount) (p.rate s.tokenIn) := by
                unfold scaledBalances scaleDown update2
                simp [hamin]
              rw [e1, e2]
              omega
            have hj_le : scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut := by
              have e : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut = scaleDown (p.balance s.tokenOut - c) (p.rate s.tokenOut) := by
                unfold scaledBalances update2
                simp [hamout, hne_symm]
              rw [e]
              have e2 : scaledBalances p s.tokenOut = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
              rw [e2]
              exact plan0_sub_le_tmp _ _ _ _ hbound hle_out
            have hother : ∀ k, k ≠ s.tokenIn → k ≠ s.tokenOut →
                (scaledBalances p) k ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k :=
              fun k hki hkj => hother_fix_test p s c k hki hkj
            have hgen := plan0_update2_le_of_parts (scaledBalances p) (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) s.tokenIn s.tokenOut (netInDown p s) (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) hne hi_le hj_le hother k
            exact hgen
          have hmono := hw.monotone _ _ (fun k hk => hdom k hk)
          have hval_eq1 : value m p = m.invariant (scaledBalances p) := rfl
          have hval_eq2 : value m { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } = m.invariant (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) := rfl
          rw [hval_eq1, hval_eq2]
          exact Nat.le_trans hinv hmono
        | givenOut =>
          have hval : Valid p s := hv
          obtain ⟨hne, hi, hj⟩ := hval
          have hne_symm : s.tokenOut ≠ s.tokenIn := Ne.symm hne
          have hon : swapGivenOut m p s = some c := by
            have h : onSwap m p s = some c := himpl
            unfold onSwap at h
            rw [hkind] at h
            exact h
          have hamout : amountOut s c = s.amount := by simp [amountOut, hkind]
          have hamin : amountIn s c = c := by simp [amountIn, hkind]
          unfold swapGivenOut at hon
          dsimp only at hon
          by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut
          · rw [if_pos hlt] at hon
            obtain ⟨r0, hdown, hadd⟩ : ∃ r0, downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 ∧ addSwapFeeAmount r0 p.fee = some c := by
              cases hdd : downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
              | none => rw [hdd] at hon; simp at hon
              | some r0 => rw [hdd] at hon; exact ⟨r0, rfl, hon⟩
            have hdown' : divUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some r0 := by
              unfold downscaleUp at hdown; exact hdown
            have hsound := hw.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) hne hi hj hlt
            have hcharge : m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ scaleDown c (p.rate s.tokenIn) :=
              testCharge _ _ _ _ _ hdown' hadd
            have hdom : ∀ k, k < p.n →
                update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k
                ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k := by
              intro k hk
              have hi_le : scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn := by
                have h2 : scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) + scaleDown c (p.rate s.tokenIn) ≤ scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := plan0_test_add_le _ _ _
                have e1 : scaledBalances p s.tokenIn = scaleDown (p.balance s.tokenIn) (p.rate s.tokenIn) := rfl
                have e2 : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenIn = scaleDown (p.balance s.tokenIn + c) (p.rate s.tokenIn) := by
                  unfold scaledBalances scaleDown update2
                  simp [hamin]
                rw [e1, e2]
                omega
              have hj_le : scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut := by
                have e : scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } s.tokenOut = scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) := by
                  unfold scaledBalances update2
                  simp [hamout, hne_symm]
                rw [e]
                have e2 : scaledBalances p s.tokenOut = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
                rw [e2]
                exact plan0_scaleDown_sub_scaleUp_le _ _ _
              have hother : ∀ k, k ≠ s.tokenIn → k ≠ s.tokenOut →
                  (scaledBalances p) k ≤ scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } k :=
                fun k hki hkj => hother_fix_test p s c k hki hkj
              have hgen := plan0_update2_le_of_parts (scaledBalances p) (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) s.tokenIn s.tokenOut (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (scaleUp s.amount (p.rate s.tokenOut)) hne hi_le hj_le hother k
              exact hgen
            have hmono := hw.monotone _ _ (fun k hk => hdom k hk)
            have hval_eq1 : value m p = m.invariant (scaledBalances p) := rfl
            have hval_eq2 : value m { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) } = m.invariant (scaledBalances { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) }) := rfl
            rw [hval_eq1, hval_eq2]
            exact Nat.le_trans hsound hmono
          · rw [if_neg hlt] at hon
            simp at hon
      · simp [hle] at hset
  · simp [hv] at hstep

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' hw h
  induction ss generalizing p p' with
  | nil =>
    simp only [run] at h
    cases h
    exact Nat.le_refl _
  | cons s ss ih =>
    simp only [run] at h
    cases hstep : step onSwap m p s with
    | none => simp [hstep] at h
    | some p1 =>
      simp [hstep] at h
      have hle1 : value m p ≤ value m p1 := req_swap_keeps_value m p s p1 hw hstep
      have hn : p1.n = p.n := by
        unfold step at hstep
        by_cases hv : Valid p s
        · simp [hv] at hstep
          cases himpl : onSwap m p s with
          | none => simp [himpl] at hstep
          | some c =>
            simp [himpl] at hstep
            unfold settle at hstep
            by_cases hle : amountOut s c ≤ p.balance s.tokenOut
            · simp [hle] at hstep
              subst hstep
              rfl
            · simp [hle] at hstep
        · simp [hv] at hstep
      have hw1 : WellBehaved m p1.n := hn ▸ hw
      have hle2 : value m p1 ≤ value m p' := ih p1 p' hw1 h
      exact Nat.le_trans hle1 hle2

end BalancerSwap

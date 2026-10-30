import BalancerSwap.Spec
namespace BalancerSwap
def ONE_UNUSED : Nat := 0
/-- `FixedPoint.mulDown`. -/
def mulDown (a b : Nat) : Nat := a * b / ONE
/-- `FixedPoint.mulUp`. -/
def mulUp (a b : Nat) : Nat := if a * b = 0 then 0 else (a * b - 1) / ONE + 1
/-- `FixedPoint.divDown`: reverts on division by zero. -/
def divDown (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some (a * ONE / b)
/-- `FixedPoint.divUp`: reverts on division by zero. -/
def divUp (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)
/-- `FixedPoint.complement`. -/
def complement (x : Nat) : Nat := if x < ONE then ONE - x else 0
/-- `_upscale`: `FixedPoint.mulDown(amount, scalingFactor)`. -/
def upscale (amount scalingFactor : Nat) : Nat := mulDown amount scalingFactor
/-- upscale rounding up (ceil). -/
def upscaleUp (amount scalingFactor : Nat) : Nat := (amount * scalingFactor + (ONE - 1)) / ONE
/-- `_upscaleArray` over the pool's balances. -/
def upscaleArray (p : Pool) : Nat → Nat := fun k => mulDown (p.balance k) (p.rate k)
/-- `_downscaleDown`. -/
def downscaleDown (amount scalingFactor : Nat) : Option Nat := divDown amount scalingFactor
/-- `_downscaleUp`. -/
def downscaleUp (amount scalingFactor : Nat) : Option Nat := divUp amount scalingFactor
/-- `_subtractSwapFeeAmount`: `amount.sub(amount.mulUp(fee))`. -/
def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none
/-- `_addSwapFeeAmount`: `amount.divUp(fee.complement())`. -/
def addSwapFeeAmount (amount fee : Nat) : Option Nat := divUp amount (complement fee)
/-- `_swapGivenIn`. -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  match subtractSwapFeeAmount s.amount p.fee with
  | none => none
  | some amount =>
    let balances := upscaleArray p
    let amount := upscale amount (p.rate s.tokenIn)
    let amountOut := m.outGivenIn balances s.tokenIn s.tokenOut amount
    downscaleDown amountOut (p.rate s.tokenOut)
/-- `_swapGivenOut` (fixed: round amount-out up, strict balance check). -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  let balances := upscaleArray p
  let amount := upscaleUp s.amount (p.rate s.tokenOut)
  if amount < balances s.tokenOut then
    match downscaleUp (m.inGivenOut balances s.tokenIn s.tokenOut amount) (p.rate s.tokenIn) with
    | none => none
    | some amountIn => addSwapFeeAmount amountIn p.fee
  else none
/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

def fooTest123 : Nat := 1

theorem myTestLemma123 : 1 + 1 = 2 := by rfl

theorem checkLib1 : True := by trivial
#check @Nat.mul_le_mul
#check @Nat.div_le_div_right
#check @Nat.mul_div_cancel
#check @Nat.div_mul_le_self
#check @Nat.mul_comm

theorem checkLib2 : True := by trivial
#check @Nat.div_add_mod
#check @Nat.mod_le
#check @Nat.div_le_iff_le_mul
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_div_left
#check @Nat.div_mul_le_self
#check @Nat.mul_div_assoc
#check @Nat.zero_lt_succ

theorem checkLib3 : True := by trivial
#check @Nat.mul_lt_mul_of_pos_left
#check @Nat.mul_le_mul_left
#check @Nat.mul_le_mul_right
#check @Nat.div_mul_le_self
#check @Nat.le_of_mul_le_mul_right
#check @Nat.le_of_mul_le_mul_left

theorem probeSig1 : True := True.intro
#check @Nat.mul_le_mul_left
#check @Nat.mul_le_mul_right
#check @Nat.div_le_div_right
#check @Nat.mul_div_cancel
#check ONE

theorem probeMulLe : forall (a b c : Nat), b ≤ c → a * b ≤ a * c := by intro a b c h; exact Nat.mul_le_mul_left a h

theorem tmp_check_div : forall (n : Nat), (n / ONE) * ONE ≤ n := fun n => Nat.div_mul_le_self n ONE
#check @Nat.div_mul_le_self
#check @Nat.mul_lt_mul_of_pos_right
#check @Nat.mul_lt_mul_of_pos_left
#check @Nat.lt_of_mul_lt_mul_right
#check @Nat.le_of_mul_le_mul_right

theorem tmp_divmono (a b k : Nat) (h : a ≤ b) : a / k ≤ b / k := Nat.div_le_div_right h

theorem help_divUp_some (a b : Nat) (hb : b ≠ 0) : ∃ v, divUp a b = some v := by
  unfold divUp; simp only [hb, ↓reduceIte]
  by_cases ha : a = 0 <;> simp [ha]

theorem help_downscaleUp_some (a r : Nat) (hr : r ≠ 0) : ∃ v, downscaleUp a r = some v := by
  unfold downscaleUp; exact help_divUp_some a r hr

theorem help_complement_lt (fee : Nat) (h : fee < ONE) : complement fee = ONE - fee := by
  unfold complement; simp [h]

theorem help_complement_ne (fee : Nat) (h : fee < ONE) : complement fee ≠ 0 := by
  rw [help_complement_lt fee h]; omega

theorem help_addFee_some (a fee : Nat) (h : fee < ONE) : ∃ v, addSwapFeeAmount a fee = some v := by
  unfold addSwapFeeAmount; exact help_divUp_some a (complement fee) (help_complement_ne fee h)

theorem help_scaleUp_mono2 {b a r : Nat} (h : b ≤ a) : scaleUp b r ≤ scaleUp a r := by
  unfold scaleUp
  apply Nat.div_le_div_right
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_right r h

theorem tmp_omega_test (a b : Nat) (h : a < b) : a ≤ b := by omega

theorem aux_ONE_pos : 0 < ONE := by unfold ONE; omega

theorem aux_mulUp_ge (a f : Nat) : a * f ≤ mulUp a f * ONE := by
  unfold mulUp
  by_cases h : a * f = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    have hdecomp : ONE * ((a * f - 1) / ONE) + (a * f - 1) % ONE = a * f - 1 :=
      Nat.div_add_mod _ _
    have hle : (a * f - 1) % ONE + 1 ≤ ONE :=
      Nat.succ_le_of_lt (Nat.mod_lt _ aux_ONE_pos)
    have hlast : ONE * ((a * f - 1) / ONE) + ONE = ((a * f - 1) / ONE + 1) * ONE := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ONE _]
    calc a * f = (a * f - 1) + 1 := by omega
      _ = ONE * ((a * f - 1) / ONE) + ((a * f - 1) % ONE + 1) := by omega
      _ ≤ ONE * ((a * f - 1) / ONE) + ONE := by
        exact Nat.add_le_add_left hle _
      _ = ((a * f - 1) / ONE + 1) * ONE := hlast

theorem probe_sigA : True := True.intro
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_iff_le_mul
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_div_right

theorem probe_sigB : True := True.intro
#check @Nat.le_div_iff_mul_le
#check @Nat.div_div_eq_div_mul
#check @Nat.div_mul_le_self
#check @Nat.mul_div_assoc

theorem aux_sub_some {a fee amt : Nat} (h : subtractSwapFeeAmount a fee = some amt) :
    mulUp a fee ≤ a ∧ amt = a - mulUp a fee := by
  unfold subtractSwapFeeAmount at h
  by_cases hc : mulUp a fee ≤ a
  · simp [hc] at h; exact ⟨hc, h.symm⟩
  · simp [hc] at h

theorem aux_amt_core (a fee amt : Nat) (h : subtractSwapFeeAmount a fee = some amt) :
    amt * ONE + a * fee ≤ a * ONE := by
  have hsub := aux_sub_some h
  have hmu_ge := aux_mulUp_ge a fee
  have hle : amt + mulUp a fee = a := by omega
  have h1 : (amt + mulUp a fee) * ONE = a * ONE := by rw [hle]
  have h2 : (amt + mulUp a fee) * ONE = amt * ONE + mulUp a fee * ONE := by
    rw [Nat.add_mul]
  rw [h2] at h1
  omega

theorem aux_upscale_eq (a r : Nat) : upscale a r = a * r / ONE := by
  unfold upscale mulDown; rfl

theorem aux_bal_eq (p : Pool) : upscaleArray p = scaledBalances p := by
  unfold upscaleArray scaledBalances scaleDown mulDown; rfl

theorem aux_down_le {o r y : Nat} (h : downscaleDown o r = some y) : y * r ≤ o * ONE := by
  unfold downscaleDown divDown at h
  by_cases hr : r = 0
  · simp [hr] at h
  · simp only [hr, ↓reduceIte] at h
    by_cases ho : o = 0
    · simp [ho] at h; subst h; simp
    · simp [ho] at h; subst h
      exact Nat.div_mul_le_self _ _

theorem tmp_eqDiv_test (K : Nat) : (K * ONE) / (ONE * ONE) = K / ONE := by
  have h1 : (K * ONE) / (ONE * ONE) = ((K * ONE) / ONE) / ONE := by
    rw [Nat.div_div_eq_div_mul]
  rw [h1]
  have h2 : (K * ONE) / ONE = K := Nat.mul_div_cancel K (by unfold ONE; omega)
  rw [h2]
#check @Nat.div_div_eq_div_mul
#check @Nat.mul_div_cancel

theorem aux_mulUp_lt (a f : Nat) : mulUp a f * ONE < a * f + ONE := by
  unfold mulUp
  by_cases h : a * f = 0
  · simp [h, aux_ONE_pos]
  · simp only [h, ↓reduceIte]
    have hpos : 0 < ONE := aux_ONE_pos
    have hle : ((a * f - 1) / ONE) * ONE ≤ a * f - 1 := Nat.div_mul_le_self _ _
    have hdecomp : ((a * f - 1) / ONE + 1) * ONE = ((a * f - 1) / ONE) * ONE + ONE := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hdecomp]
    have hpos2 : 0 < a * f := Nat.pos_of_ne_zero h
    omega

theorem aux_down_lt_succ3 {o r y : Nat} (h : downscaleDown o r = some y) :
    o * ONE < (y + 1) * r := by
  unfold downscaleDown divDown at h
  by_cases hr : r = 0
  · simp [hr] at h
  · simp only [hr, ↓reduceIte] at h
    by_cases ho : o = 0
    · subst ho
      simp at h
      subst h
      simp
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      exact hrpos
    · simp [ho] at h
      subst h
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hmod : (o * ONE) % r < r := Nat.mod_lt _ hrpos
      have hdecomp : r * ((o * ONE) / r) + (o * ONE) % r = o * ONE := Nat.div_add_mod _ _
      have hmul : ((o * ONE) / r + 1) * r = r * ((o * ONE) / r) + r := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm _ r]
      omega

theorem tmp_nat_sub_mul : True := True.intro
#check @Nat.mul_sub
#check @Nat.sub_mul
#check @Nat.mul_comm
#check @Nat.mul_assoc
#check @Nat.div_le_div_right
#check @Nat.mul_le_mul_right
#check @Nat.mul_le_mul_left

theorem tmp_submul_probe : True := True.intro
#check @Nat.sub_mul
#check @Nat.mul_sub
#check @Nat.mul_pred
#check @Nat.sub_add_comm

theorem tmp_sig_probe2 : True := True.intro
#check @Nat.div_le_iff_le_mul_add_pred
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_iff_le_mul
#check @Nat.mul_div_cancel
#check @Nat.div_div_eq_div_mul
#check @Nat.mul_sub
#check @Nat.sub_mul
#check @Nat.mul_div_assoc

theorem aux_scale_eq2 (a r : Nat) : (a * ONE * r) / (ONE * ONE) = a * r / ONE := by
  have hONE : 0 < ONE := aux_ONE_pos
  have h1 : (a * ONE * r) = (a * r) * ONE := by
    calc a * ONE * r = a * (ONE * r) := by rw [Nat.mul_assoc]
      _ = a * (r * ONE) := by rw [Nat.mul_comm ONE r]
      _ = (a * r) * ONE := by rw [Nat.mul_assoc]
  rw [h1]
  have h2 : ((a * r) * ONE) / (ONE * ONE) = (((a * r) * ONE) / ONE) / ONE := by
    rw [Nat.div_div_eq_div_mul]
  rw [h2]
  have h3 : ((a * r) * ONE) / ONE = a * r := Nat.mul_div_cancel _ hONE
  rw [h3]

theorem divUp_ge_test2 : 1 + 1 = 2 := by rfl

theorem aux_divUp_ge2 : 2 + 2 = 4 := by rfl

theorem aux_divUp_ge (a b v : Nat) (h : divUp a b = some v) : a * ONE ≤ v * b := by
  unfold divUp at h
  by_cases hb : b = 0
  · simp [hb] at h
  · simp only [hb, ↓reduceIte] at h
    by_cases ha : a = 0
    · subst ha
      simp at h
      subst h
      simp
    · simp [ha] at h
      subst h
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb
      have hmod : (a * ONE - 1) % b < b := Nat.mod_lt _ hbpos
      have hdecomp : b * ((a * ONE - 1) / b) + (a * ONE - 1) % b = a * ONE - 1 :=
        Nat.div_add_mod _ _
      have hmul : ((a * ONE - 1) / b + 1) * b = b * ((a * ONE - 1) / b) + b := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm _ b]
      have hONE : 0 < ONE := aux_ONE_pos
      have hApos : 0 < a * ONE := Nat.mul_pos (Nat.pos_of_ne_zero ha) hONE
      omega

theorem aux_upscaleUp_eq (a r : Nat) : upscaleUp a r = scaleUp a r := by
  unfold upscaleUp scaleUp
  rfl

theorem aux_complement_eq_of_ne (fee : Nat) (h : complement fee ≠ 0) :
    complement fee = ONE - fee := by
  unfold complement at h ⊢
  by_cases hf : fee < ONE
  · simp [hf]
  · simp [hf] at h

theorem aux_divUp_lt2 : ∀ (a b v : Nat), divUp a b = some v → 0 < a → (v - 1) * b < a * ONE := by
  intro a b v h ha
  unfold divUp at h
  by_cases hb : b = 0
  · simp [hb] at h
  · simp only [hb, ↓reduceIte] at h
    have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
    simp [ha0] at h
    subst h
    have hApos : 0 < a * ONE := Nat.mul_pos ha aux_ONE_pos
    have hcan : ((a * ONE - 1) / b + 1 - 1) = (a * ONE - 1) / b := Nat.add_sub_cancel _ _
    have hle : ((a * ONE - 1) / b) * b ≤ a * ONE - 1 := Nat.div_mul_le_self _ _
    calc ((a * ONE - 1) / b + 1 - 1) * b = ((a * ONE - 1) / b) * b := by rw [hcan]
      _ ≤ a * ONE - 1 := hle
      _ < a * ONE := Nat.sub_one_lt_of_le hApos (Nat.le_refl _)

theorem aux_downUp_lt_succ3 : ∀ (P R ai : Nat), divUp P R = some ai → R ≠ 0 → ai * R < P * ONE + R := by
  intro P R ai h hr
  by_cases hP : P = 0
  · subst hP
    unfold divUp at h
    simp only [hr, ↓reduceIte] at h
    simp at h
    subst h
    simp
    exact Nat.pos_of_ne_zero hr
  · have hPpos : 0 < P := Nat.pos_of_ne_zero hP
    have hlt : (ai - 1) * R < P * ONE := aux_divUp_lt2 P R ai h hPpos
    cases hai : ai with
    | zero =>
      subst hai
      simp at hlt
      omega
    | succ k =>
      rw [hai] at hlt
      have hexpand : (k + 1) * R = k * R + R := by rw [Nat.add_mul, Nat.one_mul]
      simp only [Nat.add_sub_cancel] at hlt
      omega

theorem check_mul_lt_sig : True := True.intro
#check @Nat.mul_lt_mul_of_pos_right
#check @Nat.mul_lt_mul_of_pos_left
#check @Nat.mul_right_comm
#check @Nat.mul_comm

theorem sig_probe_mul_lt : True := True.intro
#check @Nat.mul_lt_mul_of_pos_right
#check @Nat.mul_lt_mul_of_pos_left
#check @Nat.mul_le_mul
#check @Nat.mul_lt_mul_left
#check @Nat.mul_lt_mul_right

theorem req_given_out_charges_at_most_aux1 : ∀ (P R ai : Nat), divUp P R = some ai → R ≠ 0 → ai * R < P * ONE + R := aux_downUp_lt_succ3

theorem probeA : True := True.intro
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_iff_le_mul_add_pred
#check @Nat.add_mul_div_right
#check @Nat.add_mul_div_left
#check @Nat.mul_div_cancel
#check @Nat.div_mul_le_self
#check @Nat.mul_div_assoc
#check @Nat.div_add_mod

theorem probeB : True := True.intro
#check @Nat.mul_div_cancel
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.div_le_iff_le_mul_add_pred
#check @Nat.le_div_iff_mul_le
#check @Nat.sub_le_iff_le_add
#check @Nat.div_le_div_right

theorem t_floor_add_le (X Y : Nat) : X / ONE + Y / ONE ≤ (X + Y) / ONE := by
  unfold ONE
  omega

theorem t_sub_floor (B o : Nat) (h : o * 1000000000000000000 ≤ B) :
    (B - o * 1000000000000000000) / 1000000000000000000 = B / 1000000000000000000 - o := by
  omega

theorem t_floor_ge_sub_ceil (B S : Nat) :
    B / 1000000000000000000 - (S + (1000000000000000000 - 1)) / 1000000000000000000 ≤ (B - S) / 1000000000000000000 := by
  omega

theorem t_add_floor2 (B a amt r : Nat) (h : amt ≤ a) :
    B * r / 1000000000000000000 + amt * r / 1000000000000000000 ≤ (B + a) * r / 1000000000000000000 := by
  have h1 : amt * r ≤ a * r := Nat.mul_le_mul_right r h
  have h2 : B * r + amt * r ≤ (B + a) * r := by rw [Nat.add_mul]; omega
  have h3 : B * r / 1000000000000000000 + amt * r / 1000000000000000000 ≤ (B * r + amt * r) / 1000000000000000000 := by omega
  omega

theorem t_in_grow (B c P r : Nat) (h : P * 1000000000000000000 ≤ c * r) :
    B * r / 1000000000000000000 + P ≤ (B + c) * r / 1000000000000000000 := by
  have h2 : B * r + P * 1000000000000000000 ≤ (B + c) * r := by rw [Nat.add_mul]; omega
  omega

theorem t_after_in_le2 (B a amt r : Nat) (h : amt ≤ a) :
    B * r / ONE + amt * r / ONE ≤ (B + a) * r / ONE := by
  have hmul : (B + a) * r = B * r + a * r := Nat.add_mul B a r
  rw [hmul]
  have hle1 : amt * r ≤ a * r := Nat.mul_le_mul_right r h
  have hle2 : B * r / ONE + amt * r / ONE ≤ (B * r + amt * r) / ONE := by
    unfold ONE; omega
  have hle3 : (B * r + amt * r) / ONE ≤ (B * r + a * r) / ONE :=
    Nat.div_le_div_right (Nat.add_le_add_left hle1 _)
  omega

theorem t_after_in_geP2 (B c P r : Nat) (h : P * ONE ≤ c * r) :
    B * r / ONE + P ≤ (B + c) * r / ONE := by
  have hmul : (B + c) * r = B * r + c * r := Nat.add_mul B c r
  rw [hmul]
  have hle : B * r / ONE + P * ONE / ONE ≤ (B * r + P * ONE) / ONE := by
    unfold ONE; omega
  have hP : P * ONE / ONE = P := by unfold ONE; omega
  rw [hP] at hle
  have hle2 : (B * r + P * ONE) / ONE ≤ (B * r + c * r) / ONE :=
    Nat.div_le_div_right (Nat.add_le_add_left h _)
  omega

theorem t_after_out_le2 (B y r o : Nat) (_hy : y ≤ B) (hyr : y * r ≤ o * ONE) :
    B * r / ONE - o ≤ (B - y) * r / ONE := by
  have hsub : (B - y) * r = B * r - y * r := Nat.sub_mul B y r
  rw [hsub]
  unfold ONE at hyr ⊢
  omega

theorem t_after_out_ceil_le2 (B s r : Nat) (_hs : s ≤ B) :
    B * r / ONE - (s * r + (ONE - 1)) / ONE ≤ (B - s) * r / ONE := by
  have hsub : (B - s) * r = B * r - s * r := Nat.sub_mul B s r
  rw [hsub]
  unfold ONE
  omega

theorem probeC : True := True.intro
#check @Nat.le_of_mul_le_mul_right
#check @Nat.le_of_mul_le_mul_left
#check @Nat.mul_le_mul_right
#check @Nat.mul_le_mul_left
#check @Nat.mul_le_mul

theorem batch_n_eq_aux2 (m : PoolMath) (p : Pool) (ss : List Swap) (p' : Pool)
    (h : run onSwap m p ss = some p') : p'.n = p.n := by
  induction ss generalizing p p' with
  | nil =>
    simp [run] at h
    subst h
    rfl
  | cons s ss ih =>
    unfold run at h
    cases hstep : step onSwap m p s with
    | none =>
      simp [hstep] at h
    | some p1 =>
      simp [hstep] at h
      have h1 : p1.n = p.n := by
        unfold step at hstep
        by_cases hv : Valid p s
        · simp [hv] at hstep
          cases himpl : onSwap m p s with
          | none => simp [himpl] at hstep
          | some c =>
            simp [himpl] at hstep
            unfold settle at hstep
            by_cases hs : amountOut s c ≤ p.balance s.tokenOut
            · simp [hs] at hstep
              subst hstep
              rfl
            · simp [hs] at hstep
        · simp [hv] at hstep
      have h2 : p'.n = p1.n := ih _ _ h
      omega

theorem probe_div_lemmas : True := True.intro
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_iff_le_mul
#check @Nat.div_lt_iff_lt_mul
#check @Nat.lt_div_iff_mul_lt
#check @Nat.div_div_eq_div_mul

theorem probe_div2 : True := True.intro
#check @Nat.div_lt_iff_lt_mul
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_iff_le_mul
#check @Nat.mul_div_cancel
#check @Nat.div_mul_cancel
#check @Nat.div_lt_div_of_lt_of_dvd

theorem probe_mul_lt : True := True.intro
#check @Nat.mul_lt_mul_of_pos_left
#check @Nat.mul_lt_mul_of_pos_right
#check @Nat.mul_lt_mul_left
#check @Nat.mul_lt_mul_right
#check @Nat.le_of_mul_le_mul_right
#check @Nat.le_of_mul_le_mul_left
#check @Nat.div_mul_le_self
#check @Nat.mul_div_cancel

theorem test_div_lt_sig (x k y : Nat) (hk : 0 < k) : (x / k < y ↔ x < y * k) := Nat.div_lt_iff_lt_mul hk

theorem test_le_mul (a b : Nat) (h : a ≤ b) : a * ONE ≤ b * ONE := Nat.mul_le_mul_right ONE h

theorem test_strict1 (a fee : Nat) (ha : 0 < a) (hf : fee < ONE) : a * fee < a * ONE :=
  Nat.mul_lt_mul_of_pos_left hf ha

theorem test_strict2 (a fee : Nat) (ha : 0 < a) (hf : fee < ONE) : fee * a < ONE * a :=
  Nat.mul_lt_mul_of_pos_right hf ha

theorem probe_defs2 : True := True.intro
#check @Nat.div_mul_le_self
#check @Nat.div_add_mod
#check @Nat.mul_div_cancel
#check @Nat.div_le_iff_le_mul_add_pred
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_iff_le_mul

theorem aux_mulUp_le_of_fee_lt (a fee : Nat) (hfee : fee < ONE) : mulUp a fee ≤ a := by
  unfold mulUp
  by_cases h0 : a * fee = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    by_cases ha0 : a = 0
    · subst ha0; simp at h0
    · have haPos : 0 < a := Nat.pos_of_ne_zero ha0
      have hONEpos : 0 < ONE := aux_ONE_pos
      have hlt : a * fee < a * ONE := Nat.mul_lt_mul_of_pos_left hfee haPos
      have hlt2 : a * fee - 1 < a * ONE := by omega
      have hdivlt : (a * fee - 1) / ONE < a := (Nat.div_lt_iff_lt_mul hONEpos).mpr hlt2
      omega

theorem aux_sub_exists (a fee : Nat) (hfee : fee < ONE) :
    ∃ amt, subtractSwapFeeAmount a fee = some amt := by
  have hle : mulUp a fee ≤ a := aux_mulUp_le_of_fee_lt a fee hfee
  exact ⟨a - mulUp a fee, by unfold subtractSwapFeeAmount; simp [hle]⟩

theorem aux_down_some (o r : Nat) (hr : 0 < r) :
    ∃ y, downscaleDown o r = some y := by
  unfold downscaleDown divDown
  have hrne : r ≠ 0 := Nat.pos_iff_ne_zero.mp hr
  simp only [hrne, ↓reduceIte]
  by_cases ho : o = 0
  · exact ⟨0, by simp [ho]⟩
  · exact ⟨o * ONE / r, by simp [ho]⟩













theorem plan0_div_le_of_le_scaled : ∀ (o B r : Nat), 0 < r → o ≤ B * r / ONE → o * ONE / r ≤ B := by
  intro o B r hr hle
  have h1 : o * ONE ≤ (B * r / ONE) * ONE := Nat.mul_le_mul_right ONE hle
  have h2 : (B * r / ONE) * ONE ≤ B * r := Nat.div_mul_le_self _ _
  have h3 : o * ONE ≤ B * r := Nat.le_trans h1 h2
  have h4 : o * ONE / r ≤ B * r / r := Nat.div_le_div_right h3
  have h5 : B * r / r = B := Nat.mul_div_cancel B hr
  rwa [h5] at h4

theorem plan0_swapGivenIn_isSome : ∀ (m : PoolMath) (p : Pool) (s : Swap), p.fee < ONE → 0 < p.rate s.tokenOut → ∃ y, swapGivenIn m p s = some y := by
  intro m p s hfee hr
  obtain ⟨amt, hamt⟩ := aux_sub_exists s.amount p.fee hfee
  obtain ⟨y, hy⟩ := aux_down_some (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn))) (p.rate s.tokenOut) hr
  exact ⟨y, by unfold swapGivenIn; rw [hamt]; simpa using hy⟩

theorem plan0_swapGivenIn_decomp : ∀ (m : PoolMath) (p : Pool) (s : Swap) (y : Nat), swapGivenIn m p s = some y → ∃ x o, o = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x ∧ downscaleDown o (p.rate s.tokenOut) = some y := by
  intro m p s y h
  unfold swapGivenIn at h
  cases hamt : subtractSwapFeeAmount s.amount p.fee with
  | none => simp [hamt] at h
  | some amt =>
    simp [hamt] at h
    have hbal : upscaleArray p = scaledBalances p := aux_bal_eq p
    exact ⟨upscale amt (p.rate s.tokenIn), m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)), by rw [hbal], h⟩

theorem plan0_outGivenIn_le_scaled : ∀ (m : PoolMath) (p : Pool) (s : Swap) (x : Nat), WellBehaved m p.n → Valid p s → m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x ≤ scaledBalances p s.tokenOut := by
  intro m p s x hwb hvalid
  have h := hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x hvalid.1 hvalid.2.1 hvalid.2.2
  exact h.1

theorem tmp_probe_le_of_mul : True := True.intro
#check @Nat.le_of_mul_le_mul_right
#check @Nat.le_of_mul_le_mul_left

theorem plan0_downscaleDown_le_balance : ∀ (o y B r : Nat), downscaleDown o r = some y → 0 < r → o ≤ B * r / ONE → y ≤ B := by
  intro o y B r hsome hr hle
  have h1 : y * r ≤ o * ONE := aux_down_le hsome
  have hOle : o * ONE ≤ (B * r / ONE) * ONE := Nat.mul_le_mul_right ONE hle
  have hdiv : (B * r / ONE) * ONE ≤ B * r := Nat.div_mul_le_self _ _
  have h3 : y * r ≤ B * r := Nat.le_trans h1 (Nat.le_trans hOle hdiv)
  exact Nat.le_of_mul_le_mul_right h3 hr

theorem plan0_step_givenIn_isSome : ∀ (m : PoolMath) (p : Pool) (s : Swap) (y : Nat), s.kind = .givenIn → Valid p s → onSwap m p s = some y → y ≤ p.balance s.tokenOut → (step onSwap m p s).isSome := by
  intro m p s y hk hvalid hsome hle
  unfold step
  simp only [hvalid, ↓reduceIte, hsome]
  unfold settle
  simp only [amountOut, hk]
  simp only [hle, ↓reduceIte]
  rfl

theorem aux_scaleDown_le_scaleUp_of_lt {a B r : Nat} (h : B < a) :
    scaleDown B r ≤ scaleUp a r := by
  unfold scaleDown scaleUp
  apply Nat.div_le_div_right
  calc B * r ≤ a * r := Nat.mul_le_mul_right r (Nat.le_of_lt h)
    _ ≤ a * r + (ONE - 1) := Nat.le_add_right _ _

theorem aux_gim_amt_le_net2 (a fee amt : Nat) (h : subtractSwapFeeAmount a fee = some amt) :
    amt * ONE ≤ a * (ONE - fee) := by
  have hcore := aux_amt_core a fee amt h
  by_cases hfee : fee ≤ ONE
  · have hexpand : a * (ONE - fee) = a * ONE - a * fee := Nat.mul_sub a ONE fee
    rw [hexpand]
    omega
  · have hle1 : ONE ≤ fee := by omega
    have hzero : ONE - fee = 0 := Nat.sub_eq_zero_of_le hle1
    rw [hzero, Nat.mul_zero]
    have hle2 : a * ONE ≤ a * fee := Nat.mul_le_mul (Nat.le_refl a) hle1
    omega

theorem aux_gim_upscale_le_net2 (p : Pool) (s : Swap) (amt : Nat)
    (h : subtractSwapFeeAmount s.amount p.fee = some amt) :
    upscale amt (p.rate s.tokenIn) ≤ netInDown p s := by
  have hle : amt * ONE ≤ s.amount * (ONE - p.fee) :=
    aux_gim_amt_le_net2 s.amount p.fee amt h
  have hmul : (amt * p.rate s.tokenIn) * ONE ≤ s.amount * (ONE - p.fee) * p.rate s.tokenIn := by
    have h1 : (amt * p.rate s.tokenIn) * ONE = (amt * ONE) * p.rate s.tokenIn := by ac_rfl
    rw [h1]
    exact Nat.mul_le_mul_right (p.rate s.tokenIn) hle
  have heqU : upscale amt (p.rate s.tokenIn) = (amt * p.rate s.tokenIn) / ONE := by
    rw [aux_upscale_eq]
  have heqN : netInDown p s = (s.amount * (ONE - p.fee) * p.rate s.tokenIn) / (ONE * ONE) := by
    rfl
  have heqMid : ((amt * p.rate s.tokenIn) * ONE) / (ONE * ONE) = (amt * p.rate s.tokenIn) / ONE := by
    have h1 : ((amt * p.rate s.tokenIn) * ONE) / (ONE * ONE) =
      (((amt * p.rate s.tokenIn) * ONE) / ONE) / ONE := by
      rw [Nat.div_div_eq_div_mul]
    rw [h1]
    have h2 : ((amt * p.rate s.tokenIn) * ONE) / ONE = amt * p.rate s.tokenIn :=
      Nat.mul_div_cancel _ aux_ONE_pos
    rw [h2]
  rw [heqU, heqN, ← heqMid]
  exact Nat.div_le_div_right hmul

theorem gim_lower_aux2 : ∀ (A f amt : Nat), subtractSwapFeeAmount A f = some amt → (A * (ONE - f) - ONE) ≤ amt * ONE := by
  intro A f amt h
  have hsub := aux_sub_some h
  obtain ⟨hle, heq⟩ := hsub
  have hge := aux_mulUp_ge A f
  have hlt := aux_mulUp_lt A f
  have ham : amt + mulUp A f = A := by omega
  by_cases hf : f ≤ ONE
  · have e1 : A * (ONE - f) = A * ONE - A * f := Nat.mul_sub A ONE f
    rw [e1]
    have hAf_le : A * f ≤ A * ONE := Nat.mul_le_mul_left A hf
    -- amt*ONE = A*ONE - mulUp*ONE
    have eAmt : amt * ONE = A * ONE - mulUp A f * ONE := by
      have : (amt + mulUp A f) * ONE = A * ONE := by rw [ham]
      rw [Nat.add_mul] at this
      omega
    rw [eAmt]
    -- need A*ONE - A*f - ONE ≤ A*ONE - mulUp*ONE
    -- from mulUp*ONE < A*f + ONE
    omega
  · have hf2 : ONE ≤ f := by omega
    have e0 : ONE - f = 0 := Nat.sub_eq_zero_of_le hf2
    rw [e0, Nat.mul_zero, Nat.zero_sub]
    exact Nat.zero_le _

theorem gim_upscale_ge_netLess : ∀ (p : Pool) (s : Swap) (amt : Nat), subtractSwapFeeAmount s.amount p.fee = some amt → netInLessOneDown p s ≤ upscale amt (p.rate s.tokenIn) := by
  intro p s amt h
  have hK : (s.amount * (ONE - p.fee) - ONE) ≤ amt * ONE := gim_lower_aux2 s.amount p.fee amt h
  have hKr : (s.amount * (ONE - p.fee) - ONE) * p.rate s.tokenIn ≤ (amt * ONE) * p.rate s.tokenIn :=
    Nat.mul_le_mul_right _ hK
  have hle : ((s.amount * (ONE - p.fee) - ONE) * p.rate s.tokenIn) / (ONE * ONE) ≤ ((amt * ONE) * p.rate s.tokenIn) / (ONE * ONE) :=
    Nat.div_le_div_right hKr
  have eR : ((amt * ONE) * p.rate s.tokenIn) / (ONE * ONE) = upscale amt (p.rate s.tokenIn) := by
    unfold upscale mulDown
    have e1 : (amt * ONE) * p.rate s.tokenIn = (amt * p.rate s.tokenIn) * ONE := by ac_rfl
    rw [e1]
    have e2 : ((amt * p.rate s.tokenIn) * ONE) / (ONE * ONE) = (((amt * p.rate s.tokenIn) * ONE) / ONE) / ONE := by
      rw [Nat.div_div_eq_div_mul]
    rw [e2]
    have e3 : ((amt * p.rate s.tokenIn) * ONE) / ONE = amt * p.rate s.tokenIn :=
      Nat.mul_div_cancel _ aux_ONE_pos
    rw [e3]
  rw [eR] at hle
  -- netInLessOneDown unfolds to same LHS
  have eL : netInLessOneDown p s = ((s.amount * (ONE - p.fee) - ONE) * p.rate s.tokenIn) / (ONE * ONE) := rfl
  rw [eL]
  exact hle

theorem req_swap_keeps_value_aux_test : True := True.intro
#check @Nat.le_of_mul_le_mul_right
#check @Nat.mul_right_comm
#check @Nat.add_mul
#check @Nat.mul_sub

theorem probe_settle_eq (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') : amountOut s c ≤ p.balance s.tokenOut := by
  unfold settle at h
  by_cases hout : amountOut s c ≤ p.balance s.tokenOut
  · exact hout
  · simp [hout] at h

theorem probe_settle_eq2 (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') :
    p' = ({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) } : Pool) := by
  have hle : amountOut s c ≤ p.balance s.tokenOut := probe_settle_eq p s c p' h
  unfold settle at h
  simp [hle] at h
  exact h.symm

theorem gim_amt_le_amount (a fee amt : Nat) (h : subtractSwapFeeAmount a fee = some amt) : amt ≤ a := by
  have hsub := aux_sub_some h
  omega

theorem gim_bal_in_ge (B a amt r : Nat) (h : amt ≤ a) :
    B * r / ONE + amt * r / ONE ≤ (B + a) * r / ONE :=
  t_after_in_le2 B a amt r h

theorem gim_bal_out_ge (B y r o : Nat) (hy : y ≤ B) (hyr : y * r ≤ o * ONE) :
    B * r / ONE - o ≤ (B - y) * r / ONE :=
  t_after_out_le2 B y r o hy hyr

theorem gout_bal_in_ge (B c P r : Nat) (h : P * ONE ≤ c * r) :
    B * r / ONE + P ≤ (B + c) * r / ONE :=
  t_in_grow B c P r h

theorem gout_bal_out_ge (B s r : Nat) (hs : s ≤ B) :
    B * r / ONE - (s * r + (ONE - 1)) / ONE ≤ (B - s) * r / ONE :=
  t_after_out_ceil_le2 B s r hs

theorem swapKeeps_scaled_after (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') (k : Nat) :
    scaledBalances p' k = (update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) k) * p.rate k / ONE := by
  have heq := probe_settle_eq2 p s c p' h
  have hbal : p'.balance = update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) := by
    rw [heq]
  have hrate : p'.rate = p.rate := by rw [heq]
  unfold scaledBalances scaleDown
  rw [hbal, hrate]

theorem sk_complement_le_ONE (fee : Nat) : complement fee ≤ ONE := by
  unfold complement
  by_cases h : fee < ONE
  · simp [h]
  · simp [h]

theorem sk_ai_le_c {ai comp c : Nat} (hcomp_le : comp ≤ ONE)
    (h : divUp ai comp = some c) : ai ≤ c := by
  have hge : ai * ONE ≤ c * comp := aux_divUp_ge ai comp c h
  have h2 : c * comp ≤ c * ONE := Nat.mul_le_mul_left c hcomp_le
  have h3 : ai * ONE ≤ c * ONE := Nat.le_trans hge h2
  have hpos : 0 < ONE := aux_ONE_pos
  exact Nat.le_of_mul_le_mul_right h3 hpos

theorem sk_P_le_c_mul {P rIn ai comp c : Nat}
    (hdown : divUp P rIn = some ai) (hfee : divUp ai comp = some c)
    (hcomp_le : comp ≤ ONE) : P * ONE ≤ c * rIn := by
  have hge1 : P * ONE ≤ ai * rIn := aux_divUp_ge P rIn ai hdown
  have hai_le : ai ≤ c := sk_ai_le_c hcomp_le hfee
  have h2 : ai * rIn ≤ c * rIn := Nat.mul_le_mul_right rIn hai_le
  exact Nat.le_trans hge1 h2

theorem sk_gin_mid_le (m : PoolMath) (p : Pool) (s : Swap) (x o : Nat)
    (hwb : WellBehaved m p.n) (hv : Valid p s) :
    o = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x →
    o ≤ scaledBalances p s.tokenOut :=
  fun heq => heq ▸ (plan0_outGivenIn_le_scaled m p s x hwb hv)

theorem sk_settle_n (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') : p'.n = p.n := by
  have heq := probe_settle_eq2 p s c p' h
  have : p'.n = ({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) } : Pool).n := by rw [heq]
  simpa using this

theorem sk_settle_bal (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') (k : Nat) :
    p'.balance k = update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) k := by
  have heq := probe_settle_eq2 p s c p' h
  have hb : p'.balance = update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) := by rw [heq]
  rw [hb]

theorem sk_settle_rate (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') (k : Nat) : p'.rate k = p.rate k := by
  have heq := probe_settle_eq2 p s c p' h
  have hr : p'.rate = p.rate := by rw [heq]
  rw [hr]

theorem step_some_unpack (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool)
    (h : step onSwap m p s = some p') :
    Valid p s ∧ ∃ c, onSwap m p s = some c ∧ settle p s c = some p' := by
  unfold step at h
  by_cases hv : Valid p s
  · simp only [hv, ↓reduceIte] at h
    cases hc : onSwap m p s with
    | none =>
      simp [hc] at h
    | some c =>
      simp [hc] at h
      exact ⟨hv, c, rfl, h⟩
  · simp [hv] at h



theorem plan1_givenOut_pointwise : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool) (P ai c : Nat),
    Valid p s → s.kind = .givenOut →
    P = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) →
    downscaleUp P (p.rate s.tokenIn) = some ai →
    addSwapFeeAmount ai p.fee = some c →
    settle p s c = some p' →
    ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
        s.tokenOut (scaledBalances p s.tokenOut -
          scaleUp s.amount (p.rate s.tokenOut)) k ≤ scaledBalances p' k := by
  intro m p s p' P ai c hv hk hP hdown hfee hset k hkn
  have hAi : amountIn s c = c := by simp [amountIn, hk]
  have hAo : amountOut s c = s.amount := by simp [amountOut, hk]
  have hle_settle : amountOut s c ≤ p.balance s.tokenOut := probe_settle_eq p s c p' hset
  rw [hAo] at hle_settle
  have hs_le : s.amount ≤ p.balance s.tokenOut := hle_settle
  have hscale : scaledBalances p' k =
      (update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) k) * p.rate k / ONE := by
    exact swapKeeps_scaled_after p s c p' hset k
  rw [hAi, hAo] at hscale
  have hdown' : divUp P (p.rate s.tokenIn) = some ai := by
    unfold downscaleUp at hdown
    exact hdown
  have hfee' : divUp ai (complement p.fee) = some c := by
    unfold addSwapFeeAmount at hfee
    exact hfee
  have hcomp_le : complement p.fee ≤ ONE := sk_complement_le_ONE p.fee
  have hPle : P * ONE ≤ c * p.rate s.tokenIn := sk_P_le_c_mul hdown' hfee' hcomp_le
  by_cases hki : k = s.tokenIn
  · subst hki
    have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
        s.tokenOut (scaledBalances p s.tokenOut -
          scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn =
        scaledBalances p s.tokenIn + P := by simp [update2]
    rw [hL]
    have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
        s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenIn =
        p.balance s.tokenIn + c := by simp [update2]
    rw [hscale, hRbal]
    unfold scaledBalances scaleDown
    exact gout_bal_in_ge _ _ _ _ hPle
  · by_cases hkj : k = s.tokenOut
    · subst hkj
      have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
          s.tokenOut (scaledBalances p s.tokenOut -
            scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut =
          scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
        simp [update2, hki]
      rw [hL]
      have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenOut =
          p.balance s.tokenOut - s.amount := by simp [update2, hki]
      rw [hscale, hRbal]
      unfold scaledBalances scaleDown
      exact gout_bal_out_ge _ _ _ hs_le
    · have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
          s.tokenOut (scaledBalances p s.tokenOut -
            scaleUp s.amount (p.rate s.tokenOut)) k =
          scaledBalances p k := by simp [update2, hki, hkj]
      rw [hL]
      have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) k = p.balance k := by
        simp [update2, hki, hkj]
      rw [hscale, hRbal]
      exact Nat.le_refl _






theorem plan1_givenIn_pointwise : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool) (amt x o c : Nat),
    Valid p s → s.kind = .givenIn →
    subtractSwapFeeAmount s.amount p.fee = some amt →
    x = upscale amt (p.rate s.tokenIn) →
    o = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x →
    downscaleDown o (p.rate s.tokenOut) = some c →
    settle p s c = some p' →
    ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + x)
        s.tokenOut (scaledBalances p s.tokenOut - o) k ≤ scaledBalances p' k := by
  intro m p s p' amt x o c hv hk hsub hx ho hdown hset k hkn
  have hneq : s.tokenIn ≠ s.tokenOut := hv.1
  have h_amt_le : amt ≤ s.amount := gim_amt_le_amount _ _ _ hsub
  have hAi : amountIn s c = s.amount := by simp [amountIn, hk]
  have hAo : amountOut s c = c := by simp [amountOut, hk]
  have hscale : scaledBalances p' k =
      (update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) k) * p.rate k / ONE := by
    exact swapKeeps_scaled_after p s c p' hset k
  rw [hAi, hAo] at hscale
  have hx_eq : x = amt * p.rate s.tokenIn / ONE := by rw [hx, aux_upscale_eq]
  have hc_le : c ≤ p.balance s.tokenOut := by
    have hle := probe_settle_eq p s c p' hset
    rw [hAo] at hle
    exact hle
  have hdown_le : c * p.rate s.tokenOut ≤ o * ONE := aux_down_le hdown
  by_cases hki : k = s.tokenIn
  · subst hki
    have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + x)
        s.tokenOut (scaledBalances p s.tokenOut - o) s.tokenIn =
        scaledBalances p s.tokenIn + x := by simp [update2]
    rw [hL]
    have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
        s.tokenOut (p.balance s.tokenOut - c) s.tokenIn =
        p.balance s.tokenIn + s.amount := by simp [update2]
    rw [hscale, hRbal]
    unfold scaledBalances scaleDown
    rw [hx_eq]
    exact gim_bal_in_ge _ _ _ _ h_amt_le
  · by_cases hkj : k = s.tokenOut
    · subst hkj
      have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + x)
          s.tokenOut (scaledBalances p s.tokenOut - o) s.tokenOut =
          scaledBalances p s.tokenOut - o := by
        simp [update2, hki]
      rw [hL]
      have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
          s.tokenOut (p.balance s.tokenOut - c) s.tokenOut =
          p.balance s.tokenOut - c := by simp [update2, hki]
      rw [hscale, hRbal]
      unfold scaledBalances scaleDown
      exact gim_bal_out_ge _ _ _ _ hc_le hdown_le
    · have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + x)
          s.tokenOut (scaledBalances p s.tokenOut - o) k =
          scaledBalances p k := by simp [update2, hki, hkj]
      rw [hL]
      have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
          s.tokenOut (p.balance s.tokenOut - c) k = p.balance k := by
        simp [update2, hki, hkj]
      rw [hscale, hRbal]
      exact Nat.le_refl _

theorem plan1_givenIn_value : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool),
    WellBehaved m p.n → s.kind = .givenIn →
    step onSwap m p s = some p' → value m p ≤ value m p' := by
  intro m p s p' hwb hk hstep
  have hstepU := step_some_unpack m p s p' hstep
  obtain ⟨hv, c, honSwap, hsettle⟩ := hstepU
  have honSwapU : swapGivenIn m p s = some c := by
    unfold onSwap at honSwap
    rw [hk] at honSwap
    exact honSwap
  unfold swapGivenIn at honSwapU
  cases hamt : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    simp [hamt] at honSwapU
  | some amt =>
    simp [hamt] at honSwapU
    have hbal : upscaleArray p = scaledBalances p := aux_bal_eq p
    have ho_eq : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) := by
      rw [hbal]
    rw [ho_eq] at honSwapU
    have hsound := hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) hv.1 hv.2.1 hv.2.2
    have hpt : ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + (upscale amt (p.rate s.tokenIn)))
        s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn))) k ≤ scaledBalances p' k := by
      have h := plan1_givenIn_pointwise m p s p' amt (upscale amt (p.rate s.tokenIn)) (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn))) c hv hk hamt rfl rfl honSwapU hsettle
      exact h
    have hmono_le : m.invariant
        (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + (upscale amt (p.rate s.tokenIn)))
          s.tokenOut (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)))) ≤ m.invariant (scaledBalances p') :=
      hwb.monotone _ _ hpt
    unfold value
    exact Nat.le_trans hsound.2 hmono_le

theorem plan1_givenOut_value : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool),
    WellBehaved m p.n → s.kind = .givenOut →
    step onSwap m p s = some p' → value m p ≤ value m p' := by
  intro m p s p' hwb hk hstep
  have hstepU := step_some_unpack m p s p' hstep
  obtain ⟨hv, c, honSwap, hsettle⟩ := hstepU
  have honSwapU : swapGivenOut m p s = some c := by
    unfold onSwap at honSwap
    rw [hk] at honSwap
    exact honSwap
  have hbal : upscaleArray p = scaledBalances p := aux_bal_eq p
  unfold swapGivenOut at honSwapU
  simp only at honSwapU
  by_cases hlt : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · simp only [hlt, ↓reduceIte] at honSwapU
    cases hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      simp [hdown] at honSwapU
    | some ai =>
      simp [hdown] at honSwapU
      have hfee : addSwapFeeAmount ai p.fee = some c := honSwapU
      have hAeqB : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) =
        m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) := by
        rw [hbal, aux_upscaleUp_eq]
      have hlt2 : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut := by
        have h1 : upscaleUp s.amount (p.rate s.tokenOut) = scaleUp s.amount (p.rate s.tokenOut) :=
          aux_upscaleUp_eq _ _
        have h2 : upscaleArray p s.tokenOut = scaledBalances p s.tokenOut := by rw [hbal]
        rw [h1] at hlt
        rw [h2] at hlt
        exact hlt
      have hsound := hwb.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) hv.1 hv.2.1 hv.2.2 hlt2
      have hdownS : downscaleUp (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some ai := by
        rw [← hAeqB]
        exact hdown
      have hpt : ∀ k, k < p.n →
        update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn +
          m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)))
          s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k
          ≤ scaledBalances p' k :=
        plan1_givenOut_pointwise m p s p'
          (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)))
          ai c hv hk rfl hdownS hfee hsettle
      have hmono_le : m.invariant
        (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn +
          m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)))
          s.tokenOut (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut))) ≤
        m.invariant (scaledBalances p') :=
        hwb.monotone _ _ hpt
      unfold value
      exact Nat.le_trans hsound hmono_le
  · simp only [hlt, ↓reduceIte] at honSwapU
    cases honSwapU

theorem plan1_givenOut_pointwise_v2 : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool) (P ai c : Nat),
    Valid p s → s.kind = .givenOut →
    P = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) →
    downscaleUp P (p.rate s.tokenIn) = some ai →
    addSwapFeeAmount ai p.fee = some c →
    settle p s c = some p' →
    ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
        s.tokenOut (scaledBalances p s.tokenOut -
          scaleUp s.amount (p.rate s.tokenOut)) k ≤ scaledBalances p' k := by
  intro m p s p' P ai c hv hk hP hdown hfee hset k hkn
  have hAi : amountIn s c = c := by simp [amountIn, hk]
  have hAo : amountOut s c = s.amount := by simp [amountOut, hk]
  have hle_settle : amountOut s c ≤ p.balance s.tokenOut := probe_settle_eq p s c p' hset
  rw [hAo] at hle_settle
  have hs_le : s.amount ≤ p.balance s.tokenOut := hle_settle
  have hscale : scaledBalances p' k =
      (update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) k) * p.rate k / ONE := by
    exact swapKeeps_scaled_after p s c p' hset k
  rw [hAi, hAo] at hscale
  have hdown' : divUp P (p.rate s.tokenIn) = some ai := by
    unfold downscaleUp at hdown
    exact hdown
  have hfee' : divUp ai (complement p.fee) = some c := by
    unfold addSwapFeeAmount at hfee
    exact hfee
  have hcomp_le : complement p.fee ≤ ONE := sk_complement_le_ONE p.fee
  have hPle : P * ONE ≤ c * p.rate s.tokenIn := sk_P_le_c_mul hdown' hfee' hcomp_le
  by_cases hki : k = s.tokenIn
  · subst hki
    have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
        s.tokenOut (scaledBalances p s.tokenOut -
          scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn =
        scaledBalances p s.tokenIn + P := by simp [update2]
    rw [hL]
    have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
        s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenIn =
        p.balance s.tokenIn + c := by simp [update2]
    rw [hscale, hRbal]
    unfold scaledBalances scaleDown
    exact gout_bal_in_ge _ _ _ _ hPle
  · by_cases hkj : k = s.tokenOut
    · subst hkj
      have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
          s.tokenOut (scaledBalances p s.tokenOut -
            scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut =
          scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
        simp [update2, hki]
      rw [hL]
      have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenOut =
          p.balance s.tokenOut - s.amount := by simp [update2, hki]
      rw [hscale, hRbal]
      unfold scaledBalances scaleDown
      exact gout_bal_out_ge _ _ _ hs_le
    · have hL : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
          s.tokenOut (scaledBalances p s.tokenOut -
            scaleUp s.amount (p.rate s.tokenOut)) k =
          scaledBalances p k := by simp [update2, hki, hkj]
      rw [hL]
      have hRbal : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) k = p.balance k := by
        simp [update2, hki, hkj]
      rw [hscale, hRbal]
      exact Nat.le_refl _

theorem req_given_in_succeeds        : GivenInSucceeds onSwap := by
  intro m p s hwb hk hvalid hrOut hfee
  obtain ⟨y, hySwap⟩ := plan0_swapGivenIn_isSome m p s hfee hrOut
  have honSwap : onSwap m p s = some y := by
    unfold onSwap
    rw [hk]
    exact hySwap
  obtain ⟨x, o, ho_eq, hdown⟩ := plan0_swapGivenIn_decomp m p s y hySwap
  have hOutLe : o ≤ (p.balance s.tokenOut) * p.rate s.tokenOut / ONE := by
    rw [ho_eq]
    have hle := plan0_outGivenIn_le_scaled m p s x hwb hvalid
    unfold scaledBalances scaleDown at hle
    exact hle
  have hyLe : y ≤ p.balance s.tokenOut :=
    plan0_downscaleDown_le_balance o y (p.balance s.tokenOut) (p.rate s.tokenOut) hdown hrOut hOutLe
  exact plan0_step_givenIn_isSome m p s y hk hvalid honSwap hyLe

theorem req_given_out_succeeds       : GivenOutSucceeds onSwap := by
  intro m p s hwb hk hvalid hRin hfee hscale
  have hRin_ne : p.rate s.tokenIn ≠ 0 := Nat.pos_iff_ne_zero.mp hRin
  have hbal_eq : upscaleArray p = scaledBalances p := aux_bal_eq p
  have hlt : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut := by
    rw [aux_upscaleUp_eq, hbal_eq]
    unfold scaledBalances
    exact hscale
  obtain ⟨ai, hai⟩ := help_downscaleUp_some (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) hRin_ne
  obtain ⟨c, hc⟩ := help_addFee_some ai p.fee hfee
  have hswap : swapGivenOut m p s = some c := by
    unfold swapGivenOut
    simp only [hlt, ↓reduceIte, hai, hc]
  have honSwap : onSwap m p s = some c := by
    unfold onSwap
    rw [hk]
    exact hswap
  have ham_le : s.amount ≤ p.balance s.tokenOut := by
    by_cases hle : s.amount ≤ p.balance s.tokenOut
    · exact hle
    · have hlt2 : p.balance s.tokenOut < s.amount := by omega
      have hle2 := aux_scaleDown_le_scaleUp_of_lt (r := p.rate s.tokenOut) hlt2
      omega
  have hamOut : amountOut s c ≤ p.balance s.tokenOut := by
    unfold amountOut
    rw [hk]
    exact ham_le
  have hstep_eq : step onSwap m p s = settle p s c := by
    unfold step
    simp only [hvalid, ↓reduceIte, honSwap]
  rw [hstep_eq]
  unfold settle
  simp only [hamOut, ↓reduceIte]
  rfl

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hk hvalid hsome
  unfold onSwap at hsome
  rw [hk] at hsome
  simp only at hsome
  unfold swapGivenIn at hsome
  cases hamt : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    simp [hamt] at hsome
  | some amt =>
    simp [hamt] at hsome
    have hbal : upscaleArray p = scaledBalances p := aux_bal_eq p
    have hup_le : upscale amt (p.rate s.tokenIn) ≤ netInDown p s :=
      aux_gim_upscale_le_net2 p s amt hamt
    have hmono_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
      hmono.1 _ _ _ _ _ hup_le
    have hdown : downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn))) (p.rate s.tokenOut) = some y := hsome
    rw [hbal] at hdown
    have h1 : y * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) * ONE :=
      aux_down_le hdown
    have h2 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) ≤
      ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
      Nat.mul_le_mul_left ONE hmono_le
    have heq : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) * ONE =
      ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) := Nat.mul_comm _ _
    rw [heq] at h1
    exact Nat.le_trans h1 h2

theorem req_given_in_pays_at_least   : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hk hvalid hsome
  unfold onSwap at hsome
  rw [hk] at hsome
  simp only at hsome
  unfold swapGivenIn at hsome
  cases hamt : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    simp [hamt] at hsome
  | some amt =>
    simp [hamt] at hsome
    have hbal : upscaleArray p = scaledBalances p := aux_bal_eq p
    have hup_ge : netInLessOneDown p s ≤ upscale amt (p.rate s.tokenIn) :=
      gim_upscale_ge_netLess p s amt hamt
    have hmono_le : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) :=
      hmono.1 _ _ _ _ _ hup_ge
    have hdown : downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn))) (p.rate s.tokenOut) = some y := hsome
    rw [hbal] at hdown
    have hlt : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn))) * ONE < (y + 1) * p.rate s.tokenOut :=
      aux_down_lt_succ3 hdown
    have hle2 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
      ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) :=
      Nat.mul_le_mul_left ONE hmono_le
    have ecomm : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) * ONE =
      ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale amt (p.rate s.tokenIn)) := Nat.mul_comm _ _
    rw [ecomm] at hlt
    omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hk hvalid hsome
  unfold onSwap at hsome
  rw [hk] at hsome
  simp only at hsome
  unfold swapGivenOut at hsome
  dsimp only at hsome
  by_cases hlt : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · simp only [hlt, ↓reduceIte] at hsome
    cases hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      simp [hdown] at hsome
    | some ai =>
      simp [hdown] at hsome
      have hfee : addSwapFeeAmount ai p.fee = some c := hsome
      unfold addSwapFeeAmount at hfee
      have hcomp : complement p.fee ≠ 0 := by
        intro hz
        rw [hz] at hfee
        unfold divUp at hfee
        simp at hfee
      have hcompEq : complement p.fee = ONE - p.fee := aux_complement_eq_of_ne p.fee hcomp
      have h2 : ai * ONE ≤ c * complement p.fee := aux_divUp_ge ai (complement p.fee) c hfee
      rw [hcompEq] at h2
      have h1 : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) * ONE ≤ ai * p.rate s.tokenIn :=
        aux_divUp_ge _ _ _ hdown
      have hA : (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE ≤
        (ai * p.rate s.tokenIn) * ONE := Nat.mul_le_mul h1 (Nat.le_refl ONE)
      have hB : (ai * ONE) * p.rate s.tokenIn ≤
        (c * (ONE - p.fee)) * p.rate s.tokenIn := Nat.mul_le_mul h2 (Nat.le_refl _)
      have eMid : (ai * p.rate s.tokenIn) * ONE = (ai * ONE) * p.rate s.tokenIn :=
        Nat.mul_right_comm _ _ _
      have eLHS : ONE * ONE * outPrice m p s =
        (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE := by
        unfold outPrice
        rw [← aux_bal_eq p, ← aux_upscaleUp_eq]
        ac_rfl
      rw [eLHS]
      omega
  · simp only [hlt, ↓reduceIte] at hsome
    cases hsome

theorem req_given_out_charges_at_most  : GivenOutChargesAtMost onSwap := by
  intro m p s c hmono hk hvalid hsome
  unfold onSwap at hsome
  rw [hk] at hsome
  simp only at hsome
  unfold swapGivenOut at hsome
  dsimp only at hsome
  by_cases hlt : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · simp only [hlt, ↓reduceIte] at hsome
    cases hdown : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      simp [hdown] at hsome
    | some ai =>
      simp [hdown] at hsome
      have hfee : addSwapFeeAmount ai p.fee = some c := hsome
      have hRne : p.rate s.tokenIn ≠ 0 := by
        intro hz
        unfold downscaleUp divUp at hdown
        simp [hz] at hdown
      have hCne : complement p.fee ≠ 0 := by
        intro hz
        unfold addSwapFeeAmount divUp at hfee
        simp [hz] at hfee
      have hcompEq : complement p.fee = ONE - p.fee := aux_complement_eq_of_ne p.fee hCne
      have hRpos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hRne
      have hdown2 : divUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some ai := hdown
      have hfee2 : divUp ai (complement p.fee) = some c := hfee
      have hOutEq : outPrice m p s = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) := by
        unfold outPrice
        rw [← aux_bal_eq p, ← aux_upscaleUp_eq]
      have h1 : ai * p.rate s.tokenIn <
        m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn :=
        aux_downUp_lt_succ3 _ _ _ hdown2 hRne
      have hONEpos : 0 < ONE := aux_ONE_pos
      have hRHSpos : 0 < ONE * (ONE * outPrice m p s + p.rate s.tokenIn) := by
        rw [hOutEq]
        apply Nat.mul_pos hONEpos
        omega
      by_cases hai0 : ai = 0
      · subst hai0
        unfold divUp at hfee2
        simp only [hCne, ↓reduceIte] at hfee2
        simp at hfee2
        subst hfee2
        simp [hRHSpos]
      · have haiPos : 0 < ai := Nat.pos_of_ne_zero hai0
        have hlt2 : (c - 1) * complement p.fee < ai * ONE :=
          aux_divUp_lt2 ai (complement p.fee) c hfee2 haiPos
        have step1 : (c - 1) * complement p.fee * p.rate s.tokenIn <
          ai * ONE * p.rate s.tokenIn :=
          Nat.mul_lt_mul_of_pos_right hlt2 hRpos
        have e2 : ai * ONE * p.rate s.tokenIn = ai * p.rate s.tokenIn * ONE :=
          Nat.mul_right_comm ai ONE (p.rate s.tokenIn)
        rw [e2] at step1
        have step2 : ai * p.rate s.tokenIn * ONE <
          (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (upscaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
          Nat.mul_lt_mul_of_pos_right h1 hONEpos
        have htrans : (c - 1) * complement p.fee * p.rate s.tokenIn <
          (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (upscaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
          Nat.lt_trans step1 step2
        have e3 : (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (upscaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE =
          ONE * (ONE * outPrice m p s + p.rate s.tokenIn) := by
          rw [hOutEq]
          rw [Nat.mul_comm
            (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) ONE]
          rw [Nat.mul_comm
            (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (upscaleUp s.amount (p.rate s.tokenOut))) ONE]
        rw [e3] at htrans
        rw [hcompEq] at htrans
        exact htrans
  · simp only [hlt, ↓reduceIte] at hsome
    cases hsome

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hwb hstep
  cases hk : s.kind with
  | givenIn =>
    exact plan1_givenIn_value m p s p' hwb hk hstep
  | givenOut =>
    exact plan1_givenOut_value m p s p' hwb hk hstep

theorem req_batch_keeps_value        : BatchKeepsValue onSwap := by
  intro m p ss p' hwb hrun
  induction ss generalizing p p' with
  | nil =>
    simp [run] at hrun
    subst hrun
    exact Nat.le_refl _
  | cons s ss ih =>
    unfold run at hrun
    cases hstep : step onSwap m p s with
    | none =>
      simp [hstep] at hrun
    | some p1 =>
      simp [hstep] at hrun
      have hn : p1.n = p.n := by
        unfold step at hstep
        by_cases hv : Valid p s
        · simp [hv] at hstep
          cases himpl : onSwap m p s with
          | none => simp [himpl] at hstep
          | some c =>
            simp [himpl] at hstep
            unfold settle at hstep
            by_cases hs : amountOut s c ≤ p.balance s.tokenOut
            · simp [hs] at hstep
              subst hstep
              rfl
            · simp [hs] at hstep
        · simp [hv] at hstep
      have hle1 : value m p ≤ value m p1 := req_swap_keeps_value m p s p1 hwb hstep
      have hwb1 : WellBehaved m p1.n := hn ▸ hwb
      have hle2 : value m p1 ≤ value m p' := ih p1 p' hwb1 hrun
      exact Nat.le_trans hle1 hle2

end BalancerSwap

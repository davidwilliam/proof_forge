import BalancerSwap.Spec
namespace BalancerSwap

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

/-- `_swapGivenOut` (fixed: upscale exact amount out with rounding up, and
revert unless the upscaled amount is strictly below the balance). -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  let balances := upscaleArray p
  let amount := scaleUp s.amount (p.rate s.tokenOut)
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

def fooTest : Nat := 1

def fooTest2 : Nat := ONE
#check @Nat.div_le_div_right
#check @Nat.mul_le_mul
#check @Nat.div_add_mod

def probeA : Nat := 2
#check @Nat.div_mul_le_self
#check @Nat.mul_div_cancel
#check @Nat.div_le_div_right
#check @Nat.mul_le_mul
#check @Nat.le_of_lt

def probeB : Nat := 3
#check ONE
#check scaleDown
#check scaleUp
#check netInDown

theorem foo_thm : 1 + 1 = 2 := rfl

theorem foo_thm2 : 1 + 1 = 2 := rfl

theorem thm_a1 (a b : Nat) (h : a ≤ b) : a ≤ b := h

theorem thm_a2 (a : Nat) : 0 ≤ a := Nat.zero_le a

theorem thm_a3 (a b : Nat) (h : a < b) : a ≤ b := Nat.le_of_lt h

theorem thm_b1 (a b : Nat) (h : a ≤ b) : a ≤ b := by exact h

theorem thm_c1 (p : Prop) (h : p) : p := by assumption

theorem thm_c2 (a : Nat) : a = a := by rfl

theorem thm_c3 (a b : Nat) (h : a = b) : b = a := by simp_all

theorem thm_c4 (a b : Nat) (h : a ≤ b) : a ≤ b := by omega

theorem thm_t1 (p : Prop) (h : ¬¬ p) : p := by classical exact Classical.byContradiction h

theorem thm_d1 : True := by trivial

theorem thm_d2 (a b : Nat) (h : a ≤ b) : a ≤ b := by omega

theorem thm_d3 (a b : Nat) : a = b ∨ a ≠ b := by omega

theorem thm_e1 (a b : Nat) (h : a = b) : a = b := by rw [h]

theorem thm_e2 (a b : Nat) : a + b = b + a := by omega

theorem thm_e3 (f : Nat → Nat) (a : Nat) : f a = f a := by rfl

theorem probe_div_le (a b k : Nat) (h : a ≤ b) : a / k ≤ b / k := by
  exact Nat.div_le_div_right h
#check @Nat.div_le_div_right
#check @Nat.mul_le_mul
#check @Nat.div_add_mod
#check @Nat.mod_lt

theorem probe2 : True := trivial

theorem probe_div_mul_le (n k : Nat) : n / k * k ≤ n := by
  exact Nat.div_mul_le_self n k

theorem probe_mul_div_cancel (a b : Nat) (hb : 0 < b) : a * b / b = a := by
  exact Nat.mul_div_cancel a hb

theorem probe_mod_lt (n k : Nat) (hk : 0 < k) : n % k < k := by
  exact Nat.mod_lt n hk

theorem helper_down_lt3 (N r : Nat) (hr : 0 < r) :
    N * ONE < ((N * ONE / r) + 1) * r := by
  have hdm : r * (N * ONE / r) + (N * ONE) % r = N * ONE := Nat.div_add_mod _ _
  have h2 : (N * ONE) % r < r := Nat.mod_lt _ hr
  have heq : ((N * ONE / r) + 1) * r = (N * ONE / r) * r + r := by
    rw [Nat.add_mul, Nat.one_mul]
  have hcomm : (N * ONE / r) * r = r * (N * ONE / r) := by
    rw [Nat.mul_comm]
  omega

theorem helper_ONE_pos : 0 < ONE := by
  unfold ONE
  omega

theorem helper_ONE_ne : ONE ≠ 0 := by
  unfold ONE
  omega
#check @Nat.mul_div_mul_right

theorem probe_sig1 : True := trivial
#check @Nat.div_le_div_right
#check @Nat.mul_le_mul
#check @Nat.mul_div_mul_right
#check @Nat.div_add_mod
#check @Nat.add_mul
#check @Nat.mul_add
#check @Nat.sub_mul
#check @Nat.mul_sub

theorem divUp_lower_lemma (a b q : Nat) (hb : 0 < b) (h : divUp a b = some q) :
    a * ONE ≤ q * b := by
  unfold divUp at h
  by_cases hb0 : b = 0
  · omega
  · simp [hb0] at h
    by_cases ha0 : a = 0
    · simp [ha0] at h
      subst h
      simp [ha0]
    · simp [ha0] at h
      subst h
      have hONE : 0 < ONE := by unfold ONE; omega
      have haONE : 0 < a * ONE := Nat.mul_pos (Nat.pos_of_ne_zero ha0) hONE
      have hsub : (a * ONE - 1) + 1 = a * ONE := Nat.sub_add_cancel (Nat.succ_le_of_lt haONE)
      have hmod : b * ((a * ONE - 1) / b) + (a * ONE - 1) % b = a * ONE - 1 :=
        Nat.div_add_mod _ _
      have hlt : (a * ONE - 1) % b < b := Nat.mod_lt _ hb
      have hqb : ((a * ONE - 1) / b + 1) * b = b * ((a * ONE - 1) / b) + b := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((a * ONE - 1) / b) b]
      omega

theorem divUp_some_pos (a b q : Nat) (h : divUp a b = some q) : 0 < b := by
  unfold divUp at h
  by_cases hb0 : b = 0
  · simp [hb0] at h
  · omega

theorem probe_compl (fee : Nat) (h : fee < ONE) : complement fee = ONE - fee := by
  unfold complement
  simp [h]

theorem probe_add (a fee : Nat) : addSwapFeeAmount a fee = divUp a (complement fee) := by rfl

theorem probe_down (a r : Nat) : downscaleUp a r = divUp a r := by rfl

theorem combine_test (P aIn c r fee : Nat)
    (h1 : P * ONE ≤ aIn * r) (h2 : aIn * ONE ≤ c * (ONE - fee)) :
    ONE * ONE * P ≤ c * (ONE - fee) * r := by
  have h3 : (P * ONE) * ONE ≤ (aIn * r) * ONE :=
    Nat.mul_le_mul_right ONE h1
  have h4 : (aIn * ONE) * r ≤ (c * (ONE - fee)) * r :=
    Nat.mul_le_mul_right r h2
  have e1 : ONE * ONE * P = (P * ONE) * ONE := by
    calc ONE * ONE * P = ONE * (ONE * P) := by rw [Nat.mul_assoc]
      _ = ONE * (P * ONE) := by rw [Nat.mul_comm ONE P]
      _ = P * ONE * ONE := by rw [Nat.mul_comm ONE (P * ONE)]
  have e2 : (aIn * r) * ONE = (aIn * ONE) * r := by
    calc (aIn * r) * ONE = aIn * (r * ONE) := by rw [Nat.mul_assoc]
      _ = aIn * (ONE * r) := by rw [Nat.mul_comm r ONE]
      _ = (aIn * ONE) * r := by rw [← Nat.mul_assoc]
  have e3 : (c * (ONE - fee)) * r = c * (ONE - fee) * r := by rw [Nat.mul_assoc]
  omega

theorem compl_pos_lem (fee : Nat) (h : 0 < complement fee) : fee < ONE := by
  unfold complement at h
  by_cases hf : fee < ONE
  · exact hf
  · simp [hf] at h

theorem compl_eq_lem (fee : Nat) (h : fee < ONE) : complement fee = ONE - fee := by
  unfold complement; simp [h]

theorem downscale_pos_lem (a r aIn : Nat) (h : downscaleUp a r = some aIn) : 0 < r := by
  have : divUp a r = some aIn := h
  exact divUp_some_pos a r aIn this

theorem addfee_pos_lem (a fee c : Nat) (h : addSwapFeeAmount a fee = some c) :
    0 < complement fee := by
  have : divUp a (complement fee) = some c := h
  exact divUp_some_pos a (complement fee) c this

theorem fee_combine_lem2 (P aIn c r fee : Nat)
    (h1 : P * ONE ≤ aIn * r)
    (h2 : aIn * ONE ≤ c * (ONE - fee)) :
    ONE * ONE * P ≤ c * (ONE - fee) * r := by
  have h3 : (P * ONE) * ONE ≤ (aIn * r) * ONE :=
    Nat.mul_le_mul_right ONE h1
  have h4 : (aIn * ONE) * r ≤ (c * (ONE - fee)) * r :=
    Nat.mul_le_mul_right r h2
  have e1 : ONE * ONE * P = (P * ONE) * ONE := by
    calc ONE * ONE * P = ONE * (ONE * P) := by rw [Nat.mul_assoc]
      _ = ONE * (P * ONE) := by rw [Nat.mul_comm ONE P]
      _ = P * ONE * ONE := by rw [Nat.mul_comm ONE (P * ONE)]
  have e2 : (aIn * r) * ONE = (aIn * ONE) * r := by
    calc (aIn * r) * ONE = aIn * (r * ONE) := by rw [Nat.mul_assoc]
      _ = aIn * (ONE * r) := by rw [Nat.mul_comm r ONE]
      _ = (aIn * ONE) * r := by rw [← Nat.mul_assoc]
  have e3 : (c * (ONE - fee)) * r = c * (ONE - fee) * r := by rw [Nat.mul_assoc]
  omega

theorem divUp_upper_aux2 (a b q : Nat) (hb : 0 < b) (h : divUp a b = some q) :
    q * b < a * ONE + b := by
  unfold divUp at h
  by_cases hb0 : b = 0
  · omega
  · simp [hb0] at h
    by_cases ha0 : a = 0
    · simp [ha0] at h
      subst h
      simp [ha0]
      exact hb
    · simp [ha0] at h
      subst h
      have hONE : 0 < ONE := helper_ONE_pos
      have haONE : 0 < a * ONE := Nat.mul_pos (Nat.pos_of_ne_zero ha0) hONE
      have hle : (a * ONE - 1) / b * b ≤ a * ONE - 1 := Nat.div_mul_le_self _ _
      have hexpand : ((a * ONE - 1) / b + 1) * b = (a * ONE - 1) / b * b + b := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [hexpand]
      have hsub : (a * ONE - 1) + 1 = a * ONE := Nat.sub_add_cancel (Nat.succ_le_of_lt haONE)
      omega

theorem upscale_eq_scaled_test (p : Pool) : upscaleArray p = scaledBalances p := rfl

theorem onSwap_givenOut_eq (m : PoolMath) (p : Pool) (s : Swap) (h : s.kind = .givenOut) :
    onSwap m p s = swapGivenOut m p s := by
  unfold onSwap
  rw [h]

theorem probe_mul_strict_b (a b k : Nat) (h : a < b) (hk : 0 < k) : a * k < b * k := by
  exact (Nat.mul_lt_mul_right hk).mpr h

theorem c_mul_expand_aux (c comp : Nat) (hcpos : 0 < c) :
    c * comp = (c - 1) * comp + comp := by
  have hsub : c - 1 + 1 = c := Nat.sub_add_cancel hcpos
  have h1 : (c - 1 + 1) * comp = (c - 1) * comp + comp := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hsub] at h1
  exact h1

theorem div_add_le_test (a b : Nat) : a / ONE + b / ONE ≤ (a + b) / ONE := by
  unfold ONE
  omega

theorem sub_div_ge_test (X Z Y : Nat) (h : Z ≤ Y * 1000000000000000000) :
    X / 1000000000000000000 - Y ≤ (X - Z) / 1000000000000000000 := by
  omega

theorem ceil_mul_ge_test (S r : Nat) : S * r ≤ scaleUp S r * ONE := by
  unfold scaleUp ONE
  omega
#check @Nat.div_add_mod
#check @Nat.le_div_iff_mul_le
#check @Nat.div_le_div_right

theorem probe_divcancel (q K : Nat) (hK : 0 < K) : q * K / K = q := by
  exact Nat.mul_div_cancel q hK
#check @Nat.mul_div_cancel
#check @Nat.mul_div_cancel_left

theorem floor_add_ge_aux2 (A B K : Nat) (hK : 0 < K) :
    A / K + B / K ≤ (A + B) / K := by
  have hA : A / K * K ≤ A := Nat.div_mul_le_self A K
  have hB : B / K * K ≤ B := Nat.div_mul_le_self B K
  have hsum : (A / K + B / K) * K ≤ A + B := by
    have e : (A / K + B / K) * K = A / K * K + B / K * K := by rw [Nat.add_mul]
    rw [e]
    exact Nat.add_le_add hA hB
  have hdiv : (A / K + B / K) * K / K ≤ (A + B) / K :=
    Nat.div_le_div_right hsum
  have heq : (A / K + B / K) * K / K = A / K + B / K :=
    Nat.mul_div_cancel _ hK
  rw [heq] at hdiv
  exact hdiv

theorem sub_floor_ONE_lemma (A Z M : Nat) (h1 : Z ≤ M * ONE) (h2 : Z ≤ A) :
    A / ONE - M ≤ (A - Z) / ONE := by
  unfold ONE at *
  omega

theorem settle_some_eq_aux3 (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') :
    amountOut s c ≤ p.balance s.tokenOut ∧
    { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) } = p' := by
  unfold settle at h
  by_cases hle : amountOut s c ≤ p.balance s.tokenOut
  · simp [hle] at h
    exact ⟨hle, h⟩
  · simp [hle] at h

theorem step_preserves_n_aux2 (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool)
    (h : step onSwap m p s = some p') : p'.n = p.n := by
  unfold step at h
  by_cases hv : Valid p s
  · simp [hv] at h
    cases himpl : onSwap m p s with
    | none =>
      simp [himpl] at h
    | some c =>
      simp [himpl] at h
      unfold settle at h
      by_cases hle : amountOut s c ≤ p.balance s.tokenOut
      · simp [hle] at h
        subst h
        rfl
      · simp [hle] at h
  · simp [hv] at h

theorem probe_div_lt_tmp : True := trivial

theorem probe_lt_mul_tmp : True := trivial

theorem mulUp_fee_le_aux2 (a fee : Nat) (hfee : fee < ONE) : mulUp a fee ≤ a := by
  unfold mulUp
  by_cases h0 : a * fee = 0
  · simp [h0]
  · simp [h0]
    by_cases ha : a = 0
    · simp [ha] at h0
    · by_cases hfee0 : fee = 0
      · simp [hfee0] at h0
      · have hfeeONE : fee ≤ ONE := Nat.le_of_lt hfee
        have hNle : a * fee ≤ a * ONE := Nat.mul_le_mul_left a hfeeONE
        have hdiv_mul_le : (a * fee - 1) / ONE * ONE ≤ a * fee - 1 :=
          Nat.div_mul_le_self _ _
        unfold ONE at hNle hdiv_mul_le ⊢
        omega

theorem subFee_some_aux2 (amt fee : Nat) (hfee : fee < ONE) :
    (subtractSwapFeeAmount amt fee).isSome = true := by
  unfold subtractSwapFeeAmount
  have hle : mulUp amt fee ≤ amt := mulUp_fee_le_aux2 amt fee hfee
  simp [hle]

theorem divDown_le_balance_aux (Ao B r y : Nat) (hr : 0 < r)
    (hle : Ao ≤ B * r / ONE) (hdiv : divDown Ao r = some y) : y ≤ B := by
  unfold divDown at hdiv
  have hne : r ≠ 0 := by omega
  simp [hne] at hdiv
  by_cases hAo : Ao = 0
  · simp [hAo] at hdiv
    subst hdiv
    exact Nat.zero_le B
  · simp [hAo] at hdiv
    subst hdiv
    -- need Ao * ONE / r ≤ B
    have h1 : Ao * ONE ≤ (B * r / ONE) * ONE := Nat.mul_le_mul_right ONE hle
    have h2 : (B * r / ONE) * ONE ≤ B * r := Nat.div_mul_le_self _ _
    have h3 : Ao * ONE ≤ B * r := Nat.le_trans h1 h2
    have h4 : Ao * ONE / r ≤ (B * r) / r := Nat.div_le_div_right h3
    have h5 : (B * r) / r = B := Nat.mul_div_cancel B hr
    -- need rewrite B*r vs ... note h3 uses B*r; h5 is B*r/r? need commutativity? B*r same.
    rw [h5] at h4
    exact h4

theorem givenIn_step_probe (m : PoolMath) (p : Pool) (s : Swap) (hv : Valid p s) :
    (step onSwap m p s).isSome = true ∨ True := by
  unfold step
  rw [if_pos hv]
  exact Or.inr trivial

theorem divDown_some_auxA (a r : Nat) (hr : 0 < r) : ∃ y, divDown a r = some y := by
  unfold divDown
  have hne : r ≠ 0 := by omega
  simp [hne]
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]

theorem givenOut_amount_le_balance_aux (a b r : Nat) (hr : 0 < r)
    (hlt : scaleUp a r < scaleDown b r) : a ≤ b := by
  have hONE : 0 < ONE := helper_ONE_pos
  have hceil : a * r ≤ scaleUp a r * ONE := ceil_mul_ge_test a r
  have hfloor : scaleDown b r * ONE ≤ b * r := Nat.div_mul_le_self _ _
  have hlt_mul : scaleUp a r * ONE < scaleDown b r * ONE := by
    exact (Nat.mul_lt_mul_right hONE).mpr hlt
  have hneg : ¬ b < a := by
    intro hba
    have hbr : b * r < a * r := (Nat.mul_lt_mul_right hr).mpr hba
    omega
  omega

theorem divUp_some_exists_aux (a b : Nat) (hb : 0 < b) : ∃ q, divUp a b = some q := by
  unfold divUp
  have hne : b ≠ 0 := by omega
  simp [hne]
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]

theorem upscaleArray_eq_scaleDown_aux (p : Pool) (k : Nat) :
    upscaleArray p k = scaleDown (p.balance k) (p.rate k) := by
  unfold upscaleArray mulDown scaleDown
  rfl

theorem downscaleUp_some_exists_aux (a r : Nat) (hr : 0 < r) : ∃ y, downscaleUp a r = some y := by
  unfold downscaleUp
  exact divUp_some_exists_aux a r hr

theorem addFee_some_exists_aux (a fee : Nat) (hfee : fee < ONE) : ∃ c, addSwapFeeAmount a fee = some c := by
  unfold addSwapFeeAmount
  have hcomp : 0 < complement fee := by
    rw [compl_eq_lem fee hfee]
    unfold ONE at hfee ⊢
    omega
  exact divUp_some_exists_aux a (complement fee) hcomp

theorem rateOut_pos_of_lt_aux2 (a b r : Nat)
    (hlt : scaleUp a r < scaleDown b r) : 0 < r := by
  have hne : r ≠ 0 := by
    intro hzero
    subst hzero
    unfold scaleUp scaleDown ONE at hlt
    omega
  exact Nat.pos_of_ne_zero hne

theorem probe_go_unfold (m : PoolMath) (p : Pool) (s : Swap) :
    swapGivenOut m p s =
    (let balances := upscaleArray p
     ; let amount := scaleUp s.amount (p.rate s.tokenOut)
     ; if amount < balances s.tokenOut then
        match downscaleUp (m.inGivenOut balances s.tokenIn s.tokenOut amount) (p.rate s.tokenIn) with
        | none => none
        | some amountIn => addSwapFeeAmount amountIn p.fee
       else none) := by
  rfl

theorem mulUp_lower_aux (a b : Nat) : a * b ≤ mulUp a b * ONE := by
  unfold mulUp
  by_cases h0 : a * b = 0
  · simp [h0]
  · simp [h0]
    have hONE : 0 < ONE := helper_ONE_pos
    have hsub : (a * b - 1) + 1 = a * b := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0))
    have hdm : ONE * ((a * b - 1) / ONE) + (a * b - 1) % ONE = a * b - 1 := Nat.div_add_mod _ _
    have hlt : (a * b - 1) % ONE < ONE := Nat.mod_lt _ hONE
    have hexp : ((a * b - 1) / ONE + 1) * ONE = (a * b - 1) / ONE * ONE + ONE := by
      rw [Nat.add_mul, Nat.one_mul]
    have hcomm : (a * b - 1) / ONE * ONE = ONE * ((a * b - 1) / ONE) := by
      rw [Nat.mul_comm]
    omega

theorem divDown_le_aux (Ao r y : Nat) (h : divDown Ao r = some y) :
    y * r ≤ Ao * ONE := by
  unfold divDown at h
  by_cases hr : r = 0
  · simp [hr] at h
  · simp [hr] at h
    by_cases hAo : Ao = 0
    · simp [hAo] at h
      subst h
      simp [hAo]
    · simp [hAo] at h
      subst h
      have hle : (Ao * ONE / r) * r ≤ Ao * ONE := Nat.div_mul_le_self _ _
      have hcomm : (Ao * ONE / r) * r = (Ao * ONE / r) * r := rfl
      -- need y*r = (Ao*ONE/r)*r
      exact hle

theorem probe_sub_mul_check (a b c : Nat) : (a - b) * c = a * c - b * c := by
  exact Nat.sub_mul a b c

theorem probe_mul_sub_check (a b c : Nat) : a * (b - c) = a * b - a * c := by
  exact Nat.mul_sub a b c

theorem tmp_notge (a b : Nat) (h : ¬ a ≤ b) : b < a := by
  omega

theorem tmp_contra (A fee amt : Nat) (h : (none : Option Nat) = some amt) : amt * ONE ≤ A * (ONE - fee) := by
  cases h

theorem mul_lt_left_probe (A fee : Nat) (hA : 0 < A) (hf : ONE < fee) : A * ONE < A * fee := by
  exact (Nat.mul_lt_mul_left hA).mpr hf

theorem tmp_by_contra_test (A : Nat) (h : ¬ A = 0) : 0 < A := by
  omega

theorem tmp_or_test (A : Nat) : A = 0 ∨ 0 < A := by
  omega

theorem mulUp_bound_upper (a fee : Nat) : mulUp a fee * ONE ≤ a * fee + ONE := by
  unfold mulUp
  by_cases h0 : a * fee = 0
  · simp [h0]
  · simp [h0]
    have hle : (a * fee - 1) / ONE * ONE ≤ a * fee - 1 := Nat.div_mul_le_self _ _
    have hexpand : ((a * fee - 1) / ONE + 1) * ONE = (a * fee - 1) / ONE * ONE + ONE := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hexpand]
    have hpos : 0 < a * fee := Nat.pos_of_ne_zero h0
    have hsub : (a * fee - 1) + 1 = a * fee := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    omega
#check mulUp_bound_upper

theorem subtract_some_eq2 (amt fee net : Nat) (h : subtractSwapFeeAmount amt fee = some net) :
    mulUp amt fee ≤ amt ∧ net = amt - mulUp amt fee := by
  unfold subtractSwapFeeAmount at h
  by_cases hle : mulUp amt fee ≤ amt
  · simp [hle] at h
    exact ⟨hle, h.symm⟩
  · simp [hle] at h

theorem net_ge_aux2 (amt fee net : Nat) (hnet : net = amt - mulUp amt fee) :
    amt * (ONE - fee) - ONE ≤ net * ONE := by
  have hUp : mulUp amt fee * ONE ≤ amt * fee + ONE := mulUp_bound_upper amt fee
  have hmul : net * ONE = amt * ONE - mulUp amt fee * ONE := by
    rw [hnet, Nat.sub_mul]
  have hmul2 : amt * (ONE - fee) = amt * ONE - amt * fee := by
    exact Nat.mul_sub amt ONE fee
  omega

theorem divDown_upper_aux3 (Ao r y : Nat) (hr : 0 < r) (h : divDown Ao r = some y) :
    Ao * ONE < (y + 1) * r := by
  unfold divDown at h
  have hne : r ≠ 0 := by omega
  simp [hne] at h
  by_cases hAo : Ao = 0
  · simp [hAo] at h
    subst h
    simp [hAo]
    omega
  · simp [hAo] at h
    subst h
    exact helper_down_lt3 Ao r hr

theorem onSwap_givenIn_eq2 (m : PoolMath) (p : Pool) (s : Swap) (h : s.kind = .givenIn) :
    onSwap m p s = swapGivenIn m p s := by
  unfold onSwap
  rw [h]

theorem upscale_is_div (a r : Nat) : upscale a r = a * r / ONE := by rfl

theorem netLess_le_upscale_aux (p : Pool) (s : Swap) (net : Nat) :
    (s.amount * (ONE - p.fee) - ONE) ≤ net * ONE →
    netInLessOneDown p s ≤ upscale net (p.rate s.tokenIn) := by
  intro hle
  unfold netInLessOneDown upscale mulDown
  have h1 : (s.amount * (ONE - p.fee) - ONE) * p.rate s.tokenIn ≤ (net * ONE) * p.rate s.tokenIn :=
    Nat.mul_le_mul_right _ hle
  have h2 : (s.amount * (ONE - p.fee) - ONE) * p.rate s.tokenIn / (ONE * ONE) ≤
      (net * ONE) * p.rate s.tokenIn / (ONE * ONE) :=
    Nat.div_le_div_right h1
  have heq : (net * ONE) * p.rate s.tokenIn / (ONE * ONE) = net * p.rate s.tokenIn / ONE := by
    have e1 : (net * ONE) * p.rate s.tokenIn = (net * p.rate s.tokenIn) * ONE := by
      calc (net * ONE) * p.rate s.tokenIn = net * (ONE * p.rate s.tokenIn) := by rw [Nat.mul_assoc]
        _ = net * (p.rate s.tokenIn * ONE) := by rw [Nat.mul_comm ONE (p.rate s.tokenIn)]
        _ = (net * p.rate s.tokenIn) * ONE := by rw [← Nat.mul_assoc]
    rw [e1]
    exact Nat.mul_div_mul_right _ ONE helper_ONE_pos
  rw [heq] at h2
  exact h2

theorem divDown_rate_pos (Ao r y : Nat) (h : divDown Ao r = some y) : 0 < r := by
  unfold divDown at h
  by_cases hr : r = 0
  · simp [hr] at h
  · omega

theorem swapGivenIn_unfold2 (m : PoolMath) (p : Pool) (s : Swap) (net : Nat)
    (hsub : subtractSwapFeeAmount s.amount p.fee = some net) :
    swapGivenIn m p s =
    downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn))) (p.rate s.tokenOut) := by
  unfold swapGivenIn
  rw [hsub]

theorem probe_le_div_iff (x y k : Nat) (hk : 0 < k) : x ≤ y / k ↔ x * k ≤ y := by
  exact ⟨fun h => Nat.le_trans (Nat.mul_le_mul_right k h) (Nat.div_mul_le_self y k), fun h => Nat.le_div_iff_mul_le hk |>.mpr h⟩
#check @Nat.le_div_iff_mul_le
#check @Nat.div_add_mod
#check @Nat.add_mul_div_right

theorem step_some_unpack (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool)
    (h : step onSwap m p s = some p') :
    Valid p s ∧ ∃ c, onSwap m p s = some c ∧ settle p s c = some p' := by
  unfold step at h
  by_cases hv : Valid p s
  · simp [hv] at h
    cases hc : onSwap m p s with
    | none => simp [hc] at h
    | some c =>
      simp [hc] at h
      exact ⟨hv, c, rfl, h⟩
  · simp [hv] at h

theorem swapGivenIn_some_unpack (m : PoolMath) (p : Pool) (s : Swap) (y : Nat)
    (h : swapGivenIn m p s = some y) :
    ∃ net Ao, subtractSwapFeeAmount s.amount p.fee = some net ∧
      Ao = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) ∧
      divDown Ao (p.rate s.tokenOut) = some y := by
  unfold swapGivenIn at h
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none => simp [hsub] at h
  | some net =>
    simp [hsub] at h
    exact ⟨net, _, rfl, rfl, h⟩

theorem swapGivenOut_some_unpack (m : PoolMath) (p : Pool) (s : Swap) (c : Nat)
    (h : swapGivenOut m p s = some c) :
    ∃ U P aIn, U = scaleUp s.amount (p.rate s.tokenOut) ∧
      U < upscaleArray p s.tokenOut ∧
      P = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut U ∧
      divUp P (p.rate s.tokenIn) = some aIn ∧
      divUp aIn (complement p.fee) = some c := by
  have hbr : swapGivenOut m p s =
      (if scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut then
        match divUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
        | none => none
        | some aIn => divUp aIn (complement p.fee)
       else none) := rfl
  rw [hbr] at h
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · rw [if_pos hlt] at h
    cases hdiv : divUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none => simp [hdiv] at h
    | some aIn =>
      simp [hdiv] at h
      exact ⟨_, _, aIn, rfl, hlt, rfl, hdiv, h⟩
  · rw [if_neg hlt] at h
    cases h

theorem scaleDown_sub_ceil_le2 (B a r : Nat) (hle2 : a ≤ B) :
    scaleDown B r - scaleUp a r ≤ scaleDown (B - a) r := by
  unfold scaleDown scaleUp ONE at *
  have hmul : (B - a) * r = B * r - a * r := Nat.sub_mul B a r
  have hle2' : a ≤ B := hle2
  omega

theorem scaleDown_add_floor_ge2 (B c r : Nat) (P : Nat) (hP2 : P * ONE ≤ c * r) :
    scaleDown B r + P ≤ scaleDown (B + c) r := by
  unfold scaleDown ONE at *
  have hmul2 : (B + c) * r = B * r + c * r := Nat.add_mul B c r
  have hP2' : P * 1000000000000000000 ≤ c * r := hP2
  omega

theorem floor_add_le_add2 (B c r P : Nat) (hP2 : P * ONE ≤ c * r) :
    B * r / ONE + P ≤ (B + c) * r / ONE := by
  have hmul2 : (B + c) * r = B * r + c * r := Nat.add_mul B c r
  have hP2' : P * ONE ≤ c * r := hP2
  unfold ONE at hP2' ⊢
  omega

theorem le_floor_of_mul_le2 (P c r : Nat) (h2 : P * ONE ≤ c * r) : P ≤ c * r / ONE := by
  have h3 : P ≤ c * r / ONE := (Nat.le_div_iff_mul_le helper_ONE_pos).mpr h2
  exact h3

theorem aIn_le_c_of_fee2 (aIn c fee : Nat) (h : aIn * ONE ≤ c * (ONE - fee)) : aIn ≤ c := by
  have hle2 : c * (ONE - fee) ≤ c * ONE := Nat.mul_le_mul_left c (Nat.sub_le ONE fee)
  have htrans : aIn * ONE ≤ c * ONE := Nat.le_trans h hle2
  have hdiv : aIn * ONE / ONE ≤ (c * ONE) / ONE := Nat.div_le_div_right htrans
  have hl : aIn * ONE / ONE = aIn := Nat.mul_div_cancel aIn helper_ONE_pos
  have hr : (c * ONE) / ONE = c := Nat.mul_div_cancel c helper_ONE_pos
  omega

theorem scaledBalances_after_settle (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') (k : Nat) :
    scaledBalances p' k = scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) k) (p.rate k) := by
  have hset := settle_some_eq_aux3 p s c p' h
  have heq : { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) } = p' := hset.2
  have hb : p'.balance = update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) := by rw [← heq]
  have hr : p'.rate = p.rate := by rw [← heq]
  unfold scaledBalances scaleDown
  rw [hb, hr]

theorem net_le_amount2 (amt fee net : Nat) (h : subtractSwapFeeAmount amt fee = some net) : net ≤ amt := by
  have hpair := subtract_some_eq2 amt fee net h
  omega

theorem update2_at_i (b : Nat → Nat) (i x j y : Nat) : update2 b i x j y i = x := by
  unfold update2
  simp

theorem update2_at_j (b : Nat → Nat) (i x j y : Nat) (h : j ≠ i) : update2 b i x j y j = y := by
  unfold update2
  simp [h]

theorem update2_at_other (b : Nat → Nat) (i x j y k : Nat) (hi : k ≠ i) (hj : k ≠ j) :
    update2 b i x j y k = b k := by
  unfold update2
  simp [hi, hj]

theorem cancel_probe (a c k : Nat) (h : a * k ≤ c * k) (hk : 0 < k) : a ≤ c := by
  exact Nat.le_of_mul_le_mul_right h hk
#check @Nat.le_of_mul_le_mul_right

theorem floor_add_of_mul_le (B c r P : Nat) (h : P * ONE ≤ c * r) :
    B * r / ONE + P ≤ (B + c) * r / ONE := by
  have hmul : (B + c) * r = B * r + c * r := Nat.add_mul B c r
  have hle : P * ONE ≤ c * r := h
  unfold ONE at hle ⊢
  omega

theorem sub_floor_of_mul_le (B y r Ao : Nat) (hleBal : y ≤ B) (hdiv : y * r ≤ Ao * ONE) :
    B * r / ONE - Ao ≤ (B - y) * r / ONE := by
  have hmul : (B - y) * r = B * r - y * r := Nat.sub_mul B y r
  have hle1 : y * r ≤ Ao * ONE := hdiv
  have hle2 : y * r ≤ B * r := Nat.mul_le_mul_right r hleBal
  unfold ONE at hle1 ⊢
  omega

theorem net_mul_bound_aux4 (amt fee net : Nat)
    (h : subtractSwapFeeAmount amt fee = some net) :
    net * ONE ≤ amt * (ONE - fee) := by
  have hpair := subtract_some_eq2 amt fee net h
  have heq := hpair.2
  have hUp : amt * fee ≤ mulUp amt fee * ONE := mulUp_lower_aux amt fee
  have hmul : net * ONE = amt * ONE - mulUp amt fee * ONE := by
    rw [heq, Nat.sub_mul]
  have hmul2 : amt * (ONE - fee) = amt * ONE - amt * fee := Nat.mul_sub amt ONE fee
  rw [hmul, hmul2]
  exact Nat.sub_le_sub_left hUp _

theorem upscale_net_le_netInDown_aux3 (p : Pool) (s : Swap) (net : Nat) :
    net * ONE ≤ s.amount * (ONE - p.fee) →
    upscale net (p.rate s.tokenIn) ≤ netInDown p s := by
  intro hle
  unfold upscale mulDown netInDown
  have hONE : 0 < ONE := helper_ONE_pos
  have hOO : 0 < ONE * ONE := Nat.mul_pos hONE hONE
  have hA : (net * p.rate s.tokenIn) * ONE = (net * ONE) * p.rate s.tokenIn := by
    calc (net * p.rate s.tokenIn) * ONE
        = net * (p.rate s.tokenIn * ONE) := by rw [Nat.mul_assoc]
      _ = net * (ONE * p.rate s.tokenIn) := by rw [Nat.mul_comm (p.rate s.tokenIn) ONE]
      _ = (net * ONE) * p.rate s.tokenIn := by rw [← Nat.mul_assoc]
  have hAr : (net * p.rate s.tokenIn) * ONE ≤ s.amount * (ONE - p.fee) * p.rate s.tokenIn := by
    rw [hA]
    exact Nat.mul_le_mul_right _ hle
  have hq : net * p.rate s.tokenIn / ONE * ONE ≤ net * p.rate s.tokenIn :=
    Nat.div_mul_le_self _ _
  have hq2 : net * p.rate s.tokenIn / ONE * (ONE * ONE) ≤ s.amount * (ONE - p.fee) * p.rate s.tokenIn := by
    have e : net * p.rate s.tokenIn / ONE * (ONE * ONE)
        = (net * p.rate s.tokenIn / ONE * ONE) * ONE := by rw [Nat.mul_assoc]
    rw [e]
    exact Nat.le_trans (Nat.mul_le_mul_right ONE hq) hAr
  exact (Nat.le_div_iff_mul_le hOO).mpr hq2

theorem req_swap_keeps_value_aux_test1 (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') :
    p'.rate = p.rate := by
  have hset := settle_some_eq_aux3 p s c p' h
  obtain ⟨hle, heq⟩ := hset
  calc p'.rate = ({ p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s c) } : Pool).rate := by rw [heq]
    _ = p.rate := rfl

theorem fee_floor_bound2 (P c r fee : Nat)
    (h : ONE * ONE * P ≤ c * (ONE - fee) * r) : P * ONE ≤ c * r := by
  have hONE : 0 < ONE := helper_ONE_pos
  have hsub_le : ONE - fee ≤ ONE := Nat.sub_le ONE fee
  have hle1 : c * (ONE - fee) * r ≤ c * ONE * r := by
    have hle : c * (ONE - fee) ≤ c * ONE := Nat.mul_le_mul_left c hsub_le
    exact Nat.mul_le_mul_right r hle
  have hle2 : c * ONE * r = (c * r) * ONE := by
    calc c * ONE * r = c * (ONE * r) := by rw [Nat.mul_assoc]
      _ = c * (r * ONE) := by rw [Nat.mul_comm ONE r]
      _ = (c * r) * ONE := by rw [← Nat.mul_assoc]
  rw [hle2] at hle1
  have hle3 : ONE * ONE * P = (P * ONE) * ONE := by
    calc ONE * ONE * P = ONE * (ONE * P) := by rw [Nat.mul_assoc]
      _ = ONE * (P * ONE) := by rw [Nat.mul_comm ONE P]
      _ = P * ONE * ONE := by rw [Nat.mul_comm ONE (P * ONE)]
  rw [hle3] at h
  have hle4 : (P * ONE) * ONE ≤ (c * r) * ONE := Nat.le_trans h hle1
  exact Nat.le_of_mul_le_mul_right hle4 hONE

theorem amountIn_eq_givenIn (s : Swap) (c : Nat) (hkind : s.kind = .givenIn) :
    amountIn s c = s.amount := by unfold amountIn; rw [hkind]

theorem amountOut_eq_givenIn (s : Swap) (c : Nat) (hkind : s.kind = .givenIn) :
    amountOut s c = c := by unfold amountOut; rw [hkind]

theorem amountIn_eq_givenOut (s : Swap) (c : Nat) (hkind : s.kind = .givenOut) :
    amountIn s c = c := by unfold amountIn; rw [hkind]

theorem amountOut_eq_givenOut (s : Swap) (c : Nat) (hkind : s.kind = .givenOut) :
    amountOut s c = s.amount := by unfold amountOut; rw [hkind]

theorem scaled_at_in_eq (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') :
    scaledBalances p' s.tokenIn =
      scaleDown (p.balance s.tokenIn + amountIn s c) (p.rate s.tokenIn) := by
  have heq := scaledBalances_after_settle p s c p' h s.tokenIn
  have hupd : update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) s.tokenIn =
        p.balance s.tokenIn + amountIn s c :=
    update2_at_i p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c)
  rw [hupd] at heq
  exact heq

theorem scaled_at_out_eq (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p')
    (hne : s.tokenIn ≠ s.tokenOut) :
    scaledBalances p' s.tokenOut =
      scaleDown (p.balance s.tokenOut - amountOut s c) (p.rate s.tokenOut) := by
  have heq := scaledBalances_after_settle p s c p' h s.tokenOut
  have hne2 : s.tokenOut ≠ s.tokenIn := fun hcontra => hne hcontra.symm
  have hupd : update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) s.tokenOut =
        p.balance s.tokenOut - amountOut s c :=
    update2_at_j p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c) s.tokenOut (p.balance s.tokenOut - amountOut s c) hne2
  rw [hupd] at heq
  exact heq

theorem scaled_at_other_eq (p : Pool) (s : Swap) (c : Nat) (p' : Pool)
    (h : settle p s c = some p') (k : Nat) (hi : k ≠ s.tokenIn) (hj : k ≠ s.tokenOut) :
    scaledBalances p' k = scaledBalances p k := by
  have heq := scaledBalances_after_settle p s c p' h k
  have hupd : update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
        s.tokenOut (p.balance s.tokenOut - amountOut s c) k = p.balance k :=
    update2_at_other p.balance s.tokenIn _ s.tokenOut _ k hi hj
  rw [hupd] at heq
  exact heq

theorem req_given_in_succeeds        : GivenInSucceeds onSwap := by
  unfold GivenInSucceeds
  intro m p s hwb hkind hvalid hrateOut hfee
  have hle_fee : mulUp s.amount p.fee ≤ s.amount := mulUp_fee_le_aux2 s.amount p.fee hfee
  have hsub : subtractSwapFeeAmount s.amount p.fee = some (s.amount - mulUp s.amount p.fee) := by
    unfold subtractSwapFeeAmount
    simp [hle_fee]
  obtain ⟨net, hnet_eq⟩ : ∃ net, subtractSwapFeeAmount s.amount p.fee = some net :=
    ⟨_, hsub⟩
  have hbal_eq : upscaleArray p = scaledBalances p := rfl
  let amtIn : Nat := upscale net (p.rate s.tokenIn)
  let Ao : Nat := m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut amtIn
  have hAo_def : Ao = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) := rfl
  obtain ⟨y, hy⟩ : ∃ y, divDown Ao (p.rate s.tokenOut) = some y :=
    divDown_some_auxA Ao (p.rate s.tokenOut) hrateOut
  have hswap : swapGivenIn m p s = some y := by
    have h1 := swapGivenIn_unfold2 m p s net hnet_eq
    rw [h1]
    unfold downscaleDown
    rw [← hAo_def]
    exact hy
  have hon : onSwap m p s = some y := by
    rw [onSwap_givenIn_eq2 m p s hkind, hswap]
  have hi_lt : s.tokenIn < p.n := hvalid.2.1
  have hj_lt : s.tokenOut < p.n := hvalid.2.2
  have hne : s.tokenIn ≠ s.tokenOut := hvalid.1
  have hsound := hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut amtIn hne hi_lt hj_lt
  have hAo_le : Ao ≤ scaledBalances p s.tokenOut := by
    rw [hAo_def, hbal_eq]
    exact hsound.1
  have hscale : scaledBalances p s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
  have hleAo : Ao ≤ p.balance s.tokenOut * p.rate s.tokenOut / ONE := by
    rw [← hscale]
    exact hAo_le
  have hy_le : y ≤ p.balance s.tokenOut :=
    divDown_le_balance_aux Ao (p.balance s.tokenOut) (p.rate s.tokenOut) y hrateOut hleAo hy
  have hsettle : (settle p s y).isSome = true := by
    unfold settle amountOut
    rw [hkind]
    simp [hy_le]
  have hstep : (step onSwap m p s).isSome = true := by
    unfold step
    simp [hvalid, hon, hsettle]
  exact hstep

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  unfold GivenOutSucceeds
  intro m p s hwb hkind hvalid hrateIn hfee hlt
  have hrOut : 0 < p.rate s.tokenOut :=
    rateOut_pos_of_lt_aux2 s.amount (p.balance s.tokenOut) (p.rate s.tokenOut) hlt
  have hbal_eq : upscaleArray p s.tokenOut = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) :=
    upscaleArray_eq_scaleDown_aux p s.tokenOut
  have hcond : scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut := by
    rw [hbal_eq]
    exact hlt
  have hle : s.amount ≤ p.balance s.tokenOut :=
    givenOut_amount_le_balance_aux s.amount (p.balance s.tokenOut) (p.rate s.tokenOut) hrOut hlt
  obtain ⟨aIn, haIn⟩ := downscaleUp_some_exists_aux
    (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)))
    (p.rate s.tokenIn) hrateIn
  obtain ⟨c, hc⟩ := addFee_some_exists_aux aIn p.fee hfee
  have hgo : swapGivenOut m p s = some c := by
    rw [probe_go_unfold]
    simp only [hcond, ite_true, haIn, hc]
  have hon : onSwap m p s = some c := by
    rw [onSwap_givenOut_eq m p s hkind, hgo]
  have hsettle : (settle p s c).isSome = true := by
    unfold settle amountOut
    rw [hkind]
    simp [hle]
  have hstep : (step onSwap m p s).isSome = true := by
    unfold step
    simp [hvalid, hon, hsettle]
  exact hstep

theorem req_given_in_pays_at_most    : GivenInPaysAtMost onSwap := by
  unfold GivenInPaysAtMost
  intro m p s y hmono hkind hvalid hon
  have hon2 : swapGivenIn m p s = some y := by
    have heq : onSwap m p s = swapGivenIn m p s := onSwap_givenIn_eq2 m p s hkind
    rw [heq] at hon
    exact hon
  obtain ⟨net, Ao, hsub, hAo_eq, hdiv⟩ := swapGivenIn_some_unpack m p s y hon2
  have hle_net : net * ONE ≤ s.amount * (ONE - p.fee) :=
    net_mul_bound_aux4 s.amount p.fee net hsub
  have hle_up : upscale net (p.rate s.tokenIn) ≤ netInDown p s :=
    upscale_net_le_netInDown_aux3 p s net hle_net
  have hprice : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
    hmono.1 (scaledBalances p) s.tokenIn s.tokenOut _ _ hle_up
  have hAo_le : Ao ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
    have hbal : upscaleArray p = scaledBalances p := rfl
    rw [hAo_eq, hbal]
    exact hprice
  have hdivle : y * p.rate s.tokenOut ≤ Ao * ONE := divDown_le_aux Ao (p.rate s.tokenOut) y hdiv
  have h2 : Ao * ONE ≤ (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) * ONE :=
    Nat.mul_le_mul_right ONE hAo_le
  have h3 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)) * ONE =
      ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := Nat.mul_comm _ _
  omega

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  unfold GivenInPaysAtLeast
  intro m p s y hmono hkind hvalid hon
  have hon2 : swapGivenIn m p s = some y := by
    have heq : onSwap m p s = swapGivenIn m p s := onSwap_givenIn_eq2 m p s hkind
    rw [heq] at hon
    exact hon
  unfold swapGivenIn at hon2
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    simp [hsub] at hon2
  | some net =>
    simp [hsub] at hon2
    have hsubeq : net = s.amount - mulUp s.amount p.fee := by
      have ⟨hle, heq2⟩ := subtract_some_eq2 s.amount p.fee net hsub
      exact heq2
    have hdiv2 : divDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn))) (p.rate s.tokenOut) = some y := hon2
    have hrpos : 0 < p.rate s.tokenOut := divDown_rate_pos _ _ y hdiv2
    have hAo : (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn))) * ONE < (y + 1) * p.rate s.tokenOut :=
      divDown_upper_aux3 _ _ y hrpos hdiv2
    have hnet : s.amount * (ONE - p.fee) - ONE ≤ net * ONE := by
      rw [hsubeq]
      exact net_ge_aux2 s.amount p.fee (s.amount - mulUp s.amount p.fee) rfl
    have hleA : netInLessOneDown p s ≤ upscale net (p.rate s.tokenIn) :=
      netLess_le_upscale_aux p s net hnet
    have hprice2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) :=
      hmono.1 (scaledBalances p) s.tokenIn s.tokenOut _ _ hleA
    have hbal : upscaleArray p = scaledBalances p := rfl
    have hprice : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
        m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) := by
      rw [hbal]
      exact hprice2
    have hmul : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤
        ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) :=
      Nat.mul_le_mul_left ONE hprice
    have hcomm : ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) =
        (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn))) * ONE := by
      rw [Nat.mul_comm]
    omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  unfold GivenOutChargesAtLeast outPrice
  intro m p s c hmono hkind hvalid hon
  have hswap : swapGivenOut m p s = some c := by
    have heq := onSwap_givenOut_eq m p s hkind
    rw [heq] at hon
    exact hon
  have hbridge : swapGivenOut m p s =
      (if scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut then
        match divUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
        | none => none
        | some aIn => divUp aIn (complement p.fee)
       else none) := rfl
  rw [hbridge] at hswap
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · rw [if_pos hlt] at hswap
    cases hdiv : divUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      rw [hdiv] at hswap
      simp at hswap
    | some aIn =>
      rw [hdiv] at hswap
      simp at hswap
      have hrpos : 0 < p.rate s.tokenIn := divUp_some_pos _ _ _ hdiv
      have hcompPos : 0 < complement p.fee := divUp_some_pos _ _ _ hswap
      have hfee : p.fee < ONE := compl_pos_lem _ hcompPos
      have hcompEq : complement p.fee = ONE - p.fee := compl_eq_lem _ hfee
      have h1 : (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) * ONE ≤ aIn * p.rate s.tokenIn :=
        divUp_lower_lemma _ _ _ hrpos hdiv
      have h2a : aIn * ONE ≤ c * complement p.fee :=
        divUp_lower_lemma _ _ _ hcompPos hswap
      rw [hcompEq] at h2a
      have hsame : upscaleArray p = scaledBalances p := rfl
      rw [hsame] at h1
      exact fee_combine_lem2 (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) aIn c (p.rate s.tokenIn) p.fee h1 h2a
  · rw [if_neg hlt] at hswap
    cases hswap

theorem req_given_out_charges_at_most  : GivenOutChargesAtMost onSwap := by
  unfold GivenOutChargesAtMost outPrice
  intro m p s c hmono hkind hvalid hon
  have hswap : swapGivenOut m p s = some c := by
    have heq := onSwap_givenOut_eq m p s hkind
    rw [heq] at hon
    exact hon
  have hbridge : swapGivenOut m p s =
      (if scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut then
        match divUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
        | none => none
        | some aIn => divUp aIn (complement p.fee)
       else none) := rfl
  rw [hbridge] at hswap
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · rw [if_pos hlt] at hswap
    cases hdiv : divUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      rw [hdiv] at hswap
      simp at hswap
    | some aIn =>
      rw [hdiv] at hswap
      simp at hswap
      have hrpos : 0 < p.rate s.tokenIn := divUp_some_pos _ _ _ hdiv
      have hcompPos : 0 < complement p.fee := divUp_some_pos _ _ _ hswap
      have hfee : p.fee < ONE := compl_pos_lem _ hcompPos
      have hcompEq : complement p.fee = ONE - p.fee := compl_eq_lem _ hfee
      have hONEpos : 0 < ONE := helper_ONE_pos
      have hUp1 : aIn * p.rate s.tokenIn <
          m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn :=
        divUp_upper_aux2 _ _ _ hrpos hdiv
      have hUp2c : c * complement p.fee < aIn * ONE + complement p.fee :=
        divUp_upper_aux2 _ _ _ hcompPos hswap
      have hsame : upscaleArray p = scaledBalances p := rfl
      rw [hsame] at hUp1
      have hRHS_eq : ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn)
          = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE := by
        calc ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn)
            = ONE * (ONE * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) + ONE * p.rate s.tokenIn := by rw [Nat.mul_add]
          _ = (ONE * ONE) * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + ONE * p.rate s.tokenIn := by rw [Nat.mul_assoc]
          _ = (ONE * ONE) * m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn * ONE := by rw [Nat.mul_comm ONE (p.rate s.tokenIn)]
          _ = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * (ONE * ONE) + p.rate s.tokenIn * ONE := by rw [Nat.mul_comm (ONE * ONE) _]
          _ = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE + p.rate s.tokenIn * ONE := by rw [Nat.mul_assoc]
          _ = (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE := by rw [Nat.add_mul]
      rw [hRHS_eq]
      by_cases hc0 : c = 0
      · subst hc0
        simp
        have hinner : 0 < m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn := by
          omega
        exact Nat.mul_pos hinner hONEpos
      · have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
        have hexpand : c * complement p.fee = (c - 1) * complement p.fee + complement p.fee := by
          exact c_mul_expand_aux c (complement p.fee) hcpos
        have hXlt : (c - 1) * complement p.fee < aIn * ONE := by omega
        have hXR : ((c - 1) * complement p.fee) * p.rate s.tokenIn < (aIn * ONE) * p.rate s.tokenIn :=
          (Nat.mul_lt_mul_right hrpos).mpr hXlt
        have hYeq : (aIn * ONE) * p.rate s.tokenIn = (aIn * p.rate s.tokenIn) * ONE := by
          calc (aIn * ONE) * p.rate s.tokenIn = aIn * (ONE * p.rate s.tokenIn) := by rw [Nat.mul_assoc]
            _ = aIn * (p.rate s.tokenIn * ONE) := by rw [Nat.mul_comm ONE (p.rate s.tokenIn)]
            _ = (aIn * p.rate s.tokenIn) * ONE := by rw [← Nat.mul_assoc]
        rw [hYeq] at hXR
        have hYR : (aIn * p.rate s.tokenIn) * ONE <
            (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
          (Nat.mul_lt_mul_right hONEpos).mpr hUp1
        have htrans : ((c - 1) * complement p.fee) * p.rate s.tokenIn <
            (m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
          Nat.lt_trans hXR hYR
        have eL : ((c - 1) * complement p.fee) * p.rate s.tokenIn = (c - 1) * (ONE - p.fee) * p.rate s.tokenIn := by
          rw [hcompEq]
        rw [← eL]
        exact htrans
  · rw [if_neg hlt] at hswap
    cases hswap

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  unfold SwapKeepsValue value
  intro m p s p' hwb hstep
  obtain ⟨hvalid, c, hon, hset⟩ := step_some_unpack m p s p' hstep
  have hne : s.tokenIn ≠ s.tokenOut := hvalid.1
  have hi_lt : s.tokenIn < p.n := hvalid.2.1
  have hj_lt : s.tokenOut < p.n := hvalid.2.2
  have hsetpair := settle_some_eq_aux3 p s c p' hset
  have hle_out : amountOut s c ≤ p.balance s.tokenOut := hsetpair.1
  cases hkind : s.kind with
  | givenIn =>
    have hon2 : swapGivenIn m p s = some c := by
      have heq : onSwap m p s = swapGivenIn m p s := onSwap_givenIn_eq2 m p s hkind
      rw [heq] at hon
      exact hon
    obtain ⟨net, Ao, hsub, hAo_eq, hdiv⟩ := swapGivenIn_some_unpack m p s c hon2
    have hbal : upscaleArray p = scaledBalances p := rfl
    rw [hbal] at hAo_eq
    have hsound := hwb.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) hne hi_lt hj_lt
    have hInv_le_mid : m.invariant (scaledBalances p) ≤ m.invariant (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + upscale net (p.rate s.tokenIn)) s.tokenOut (scaledBalances p s.tokenOut - Ao)) := by
      rw [hAo_eq]
      exact hsound.2
    have hmid_le : ∀ k, k < p.n → (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + upscale net (p.rate s.tokenIn)) s.tokenOut (scaledBalances p s.tokenOut - Ao)) k ≤ scaledBalances p' k := by
      intro k hk
      by_cases hki : k = s.tokenIn
      · subst hki
        rw [update2_at_i]
        have hBi : scaledBalances p s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
        have hBpi : scaledBalances p' s.tokenIn = scaleDown (p.balance s.tokenIn + amountIn s c) (p.rate s.tokenIn) := scaled_at_in_eq p s c p' hset
        have hAmtIn : amountIn s c = s.amount := amountIn_eq_givenIn s c hkind
        rw [hAmtIn] at hBpi
        have hnet_le : net ≤ s.amount := net_le_amount2 s.amount p.fee net hsub
        have hONEpos : 0 < ONE := helper_ONE_pos
        have hfloor : p.balance s.tokenIn * p.rate s.tokenIn / ONE + net * p.rate s.tokenIn / ONE ≤ (p.balance s.tokenIn * p.rate s.tokenIn + net * p.rate s.tokenIn) / ONE :=
          floor_add_ge_aux2 _ _ ONE hONEpos
        have hmul_eq : p.balance s.tokenIn * p.rate s.tokenIn + net * p.rate s.tokenIn = (p.balance s.tokenIn + net) * p.rate s.tokenIn := by
          rw [Nat.add_mul]
        have hmul_le : (p.balance s.tokenIn + net) * p.rate s.tokenIn ≤ (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left hnet_le _)
        have hdiv_le : (p.balance s.tokenIn + net) * p.rate s.tokenIn / ONE ≤ (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE :=
          Nat.div_le_div_right hmul_le
        have hup_eq : upscale net (p.rate s.tokenIn) = net * p.rate s.tokenIn / ONE := rfl
        rw [hBi, hup_eq] at *
        unfold scaleDown at hBpi
        rw [hBpi]
        calc p.balance s.tokenIn * p.rate s.tokenIn / ONE + net * p.rate s.tokenIn / ONE
            ≤ (p.balance s.tokenIn * p.rate s.tokenIn + net * p.rate s.tokenIn) / ONE := hfloor
          _ = (p.balance s.tokenIn + net) * p.rate s.tokenIn / ONE := by rw [hmul_eq]
          _ ≤ (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE := hdiv_le
      · by_cases hkj : k = s.tokenOut
        · subst hkj
          have hupd : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + upscale net (p.rate s.tokenIn)) s.tokenOut (scaledBalances p s.tokenOut - Ao) s.tokenOut = scaledBalances p s.tokenOut - Ao :=
            update2_at_j (scaledBalances p) s.tokenIn _ s.tokenOut _ (fun h => hne h.symm)
          rw [hupd]
          have hBpout : scaledBalances p' s.tokenOut = scaleDown (p.balance s.tokenOut - amountOut s c) (p.rate s.tokenOut) :=
            scaled_at_out_eq p s c p' hset hne
          have hAmtOut : amountOut s c = c := amountOut_eq_givenIn s c hkind
          rw [hAmtOut] at hBpout
          have hdivle : c * p.rate s.tokenOut ≤ Ao * ONE := divDown_le_aux Ao (p.rate s.tokenOut) c hdiv
          have hyle : c ≤ p.balance s.tokenOut := by
            have htmp : amountOut s c ≤ p.balance s.tokenOut := hle_out
            rw [hAmtOut] at htmp
            exact htmp
          have hsub_lem : p.balance s.tokenOut * p.rate s.tokenOut / ONE - Ao ≤ (p.balance s.tokenOut - c) * p.rate s.tokenOut / ONE :=
            sub_floor_of_mul_le (p.balance s.tokenOut) c (p.rate s.tokenOut) Ao hyle hdivle
          have hBj : scaledBalances p s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
          rw [hBj]
          unfold scaleDown at hBpout
          rw [hBpout]
          exact hsub_lem
        · have hupd : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + upscale net (p.rate s.tokenIn)) s.tokenOut (scaledBalances p s.tokenOut - Ao) k = scaledBalances p k :=
            update2_at_other (scaledBalances p) s.tokenIn _ s.tokenOut _ k hki hkj
          rw [hupd]
          have hother : scaledBalances p' k = scaledBalances p k :=
            scaled_at_other_eq p s c p' hset k hki hkj
          rw [← hother]
          exact Nat.le_refl _
    have hmono := hwb.monotone (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + upscale net (p.rate s.tokenIn)) s.tokenOut (scaledBalances p s.tokenOut - Ao)) (scaledBalances p') hmid_le
    exact Nat.le_trans hInv_le_mid hmono
  | givenOut =>
    have hon2 : swapGivenOut m p s = some c := by
      have heq := onSwap_givenOut_eq m p s hkind
      rw [heq] at hon
      exact hon
    obtain ⟨U, P, aIn, hU_eq, hUlt, hP_eq, hdiv1, hdiv2⟩ := swapGivenOut_some_unpack m p s c hon2
    have hbal_eq : upscaleArray p s.tokenOut = scaledBalances p s.tokenOut := rfl
    rw [hbal_eq] at hUlt
    have hUlt2 : U < scaledBalances p s.tokenOut := hUlt
    have hP_is : P = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut U := by
      calc P = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut U := hP_eq
        _ = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut U := rfl
    have hsound0 := hwb.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut U hne hi_lt hj_lt hUlt2
    have hsound : m.invariant (scaledBalances p) ≤ m.invariant (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P) s.tokenOut (scaledBalances p s.tokenOut - U)) := by
      rw [hP_is]
      exact hsound0
    have hrpos : 0 < p.rate s.tokenIn := divUp_some_pos _ _ _ hdiv1
    have hcompPos : 0 < complement p.fee := divUp_some_pos _ _ _ hdiv2
    have hfee : p.fee < ONE := compl_pos_lem _ hcompPos
    have hcompEq : complement p.fee = ONE - p.fee := compl_eq_lem _ hfee
    have h1 : P * ONE ≤ aIn * p.rate s.tokenIn := divUp_lower_lemma _ _ _ hrpos hdiv1
    have h2a0 : aIn * ONE ≤ c * complement p.fee := divUp_lower_lemma _ _ _ hcompPos hdiv2
    rw [hcompEq] at h2a0
    have hcomb : ONE * ONE * P ≤ c * (ONE - p.fee) * p.rate s.tokenIn :=
      fee_combine_lem2 P aIn c (p.rate s.tokenIn) p.fee h1 h2a0
    have hPbound : P * ONE ≤ c * p.rate s.tokenIn :=
      fee_floor_bound2 P c (p.rate s.tokenIn) p.fee hcomb
    have hmid_le : ∀ k, k < p.n → (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P) s.tokenOut (scaledBalances p s.tokenOut - U)) k ≤ scaledBalances p' k := by
      intro k hk
      by_cases hki : k = s.tokenIn
      · subst hki
        rw [update2_at_i]
        have hBpi : scaledBalances p' s.tokenIn = scaleDown (p.balance s.tokenIn + amountIn s c) (p.rate s.tokenIn) := scaled_at_in_eq p s c p' hset
        have hAmtIn : amountIn s c = c := amountIn_eq_givenOut s c hkind
        rw [hAmtIn] at hBpi
        have hfloor : p.balance s.tokenIn * p.rate s.tokenIn / ONE + P ≤ (p.balance s.tokenIn + c) * p.rate s.tokenIn / ONE :=
          floor_add_of_mul_le (p.balance s.tokenIn) c (p.rate s.tokenIn) P hPbound
        have hBi : scaledBalances p s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
        rw [hBi]
        unfold scaleDown at hBpi
        rw [hBpi]
        exact hfloor
      · by_cases hkj : k = s.tokenOut
        · subst hkj
          have hupd : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P) s.tokenOut (scaledBalances p s.tokenOut - U) s.tokenOut = scaledBalances p s.tokenOut - U :=
            update2_at_j (scaledBalances p) s.tokenIn _ s.tokenOut _ (fun h => hne h.symm)
          rw [hupd]
          have hBpout : scaledBalances p' s.tokenOut = scaleDown (p.balance s.tokenOut - amountOut s c) (p.rate s.tokenOut) :=
            scaled_at_out_eq p s c p' hset hne
          have hAmtOut : amountOut s c = s.amount := amountOut_eq_givenOut s c hkind
          rw [hAmtOut] at hBpout
          have hamt_le : s.amount ≤ p.balance s.tokenOut := by
            have htmp : amountOut s c ≤ p.balance s.tokenOut := hle_out
            rw [hAmtOut] at htmp
            exact htmp
          have hBj : scaledBalances p s.tokenOut = scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) := rfl
          have hUeq : U = scaleUp s.amount (p.rate s.tokenOut) := hU_eq
          have hsub_lem : scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) - scaleUp s.amount (p.rate s.tokenOut) ≤ scaleDown (p.balance s.tokenOut - s.amount) (p.rate s.tokenOut) :=
            scaleDown_sub_ceil_le2 (p.balance s.tokenOut) s.amount (p.rate s.tokenOut) hamt_le
          rw [hBj, hUeq]
          unfold scaleDown at hBpout
          rw [hBpout]
          exact hsub_lem
        · have hupd : update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P) s.tokenOut (scaledBalances p s.tokenOut - U) k = scaledBalances p k :=
            update2_at_other (scaledBalances p) s.tokenIn _ s.tokenOut _ k hki hkj
          rw [hupd]
          have hother : scaledBalances p' k = scaledBalances p k :=
            scaled_at_other_eq p s c p' hset k hki hkj
          rw [← hother]
          exact Nat.le_refl _
    have hmono := hwb.monotone (update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P) s.tokenOut (scaledBalances p s.tokenOut - U)) (scaledBalances p') hmid_le
    exact Nat.le_trans hsound hmono

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  unfold BatchKeepsValue
  intro m p ss p' hwbrun hrun
  induction ss generalizing p p' with
  | nil =>
    simp [run] at hrun
    subst hrun
    exact Nat.le_refl _
  | cons s ss ih =>
    have hrun2 : run onSwap m p (s :: ss) =
        match step onSwap m p s with
        | some p_mid => run onSwap m p_mid ss
        | none => none := rfl
    rw [hrun2] at hrun
    cases hst : step onSwap m p s with
    | none =>
      simp [hst] at hrun
    | some p_mid =>
      simp [hst] at hrun
      have hn : p_mid.n = p.n := step_preserves_n_aux2 m p s p_mid hst
      have hw_mid : WellBehaved m p_mid.n := by rw [hn]; exact hwbrun
      have hswap : value m p ≤ value m p_mid := req_swap_keeps_value m p s p_mid hwbrun hst
      have hrest : value m p_mid ≤ value m p' := ih p_mid p' hw_mid hrun
      exact Nat.le_trans hswap hrest

end BalancerSwap

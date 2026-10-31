import BalancerSwap.Spec

namespace BalancerSwap

/-! ## FixedPoint -/

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

/-! ## BasePool -/

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

/-! ## BaseGeneralPool -/

/-- `_swapGivenIn`. -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  match subtractSwapFeeAmount s.amount p.fee with
  | none => none
  | some amount =>
    downscaleDown
      (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale amount (p.rate s.tokenIn)))
      (p.rate s.tokenOut)

/-- `_swapGivenOut`. The amount out is rounded up to a whole 18-decimal unit before
pricing, and the trade is refused unless it is strictly below the pool balance. -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut then
    match downscaleUp
      (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)))
      (p.rate s.tokenIn) with
    | none => none
    | some amountIn => addSwapFeeAmount amountIn p.fee
  else none

/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

/-! ## Helper facts about rounding -/

private theorem one_pos : 0 < ONE := by decide

private theorem one_ne_zero : ONE ≠ 0 := by
  intro h
  have := one_pos
  omega

/-- The balances the wrapper prices with are the balances the spec values. -/
private theorem balances_eq (p : Pool) : upscaleArray p = scaledBalances p := rfl

/-- Trivial successor bounds, proved in a clean context. -/
private theorem succ_sub_le (x : Nat) : x + 1 - 1 ≤ x + 1 := by omega

/-- Given-in token-in side: the pool's scaled balance grows by at least the priced amount. -/
private theorem givenIn_i_le (B R A A' : Nat) (hle : A' ≤ A) :
    B * R / ONE + A' * R / ONE ≤ (B + A) * R / ONE := by
  have g1 : B * R / ONE + A' * R / ONE ≤ (B * R + A' * R) / ONE := add_div_le _ _
  have g2 : B * R + A' * R ≤ (B + A) * R := by
    have e : (B + A) * R = B * R + A * R := Nat.add_mul _ _ _
    have h2 : A' * R ≤ A * R := Nat.mul_le_mul_right R hle
    omega
  exact Nat.le_trans g1 (div_mono_one _ _ g2)

/-- Given-in token-out side: the pool's scaled balance shrinks by at most the priced amount. -/
private theorem givenIn_j_le (B R y G : Nat)
    (hyR : y * R ≤ G * ONE)
    (hle : G ≤ B * R / ONE)
    (hyB : y ≤ B) :
    B * R / ONE - G ≤ (B - y) * R / ONE := by
  apply le_div_of_mul_le _ _ _ one_pos
  have e1 : (B * R / ONE - G) * ONE + G * ONE = B * R / ONE * ONE := by
    have e : (B * R / ONE - G) + G = B * R / ONE := Nat.sub_add_cancel hle
    have e2 : ((B * R / ONE - G) + G) * ONE = B * R / ONE * ONE := by rw [e]
    rw [Nat.add_mul] at e2
    exact e2
  have e2 : (B - y) * R + y * R = B * R := by
    have e : (B - y) + y = B := Nat.sub_add_cancel hyB
    have e3 : ((B - y) + y) * R = B * R := by rw [e]
    rw [Nat.add_mul] at e3
    exact e3
  have g1 : B * R / ONE * ONE ≤ B * R := Nat.div_mul_le_self _ _
  have g2 : G * ONE ≤ B * R / ONE * ONE := Nat.mul_le_mul_right ONE hle
  have g4 : y * R ≤ B * R := Nat.mul_le_mul_right R hyB
  omega

/-- The fee-adjusted charge covers the price, scaled. -/
private theorem charge_core {P D c R E : Nat}
    (hDlo : P * ONE ≤ D * R) (hclo : D * ONE ≤ c * E) :
    ONE * ONE * P ≤ c * E * R := by
  have h1 : (P * ONE) * ONE ≤ (D * R) * ONE := Nat.mul_le_mul_right ONE hDlo
  have e1 : (D * R) * ONE = (D * ONE) * R := by
    rw [Nat.mul_assoc D R ONE, Nat.mul_comm R ONE, ← Nat.mul_assoc D ONE R]
  have h2 : (D * ONE) * R ≤ (c * E) * R := Nat.mul_le_mul_right _ hclo
  have e2 : ONE * ONE * P = (P * ONE) * ONE := by
    rw [Nat.mul_comm (ONE * ONE) P, ← Nat.mul_assoc]
  omega

/-- Given-out token-in side: the pool's scaled balance grows by at least the price. -/
private theorem givenOut_i_le (B R P c E : Nat)
    (hcore : ONE * ONE * P ≤ c * E * R)
    (hE : E ≤ ONE) :
    B * R / ONE + P ≤ (B + c) * R / ONE := by
  have hPR : P * ONE ≤ c * R := by
    have h1 : (P * ONE) * ONE ≤ (c * R) * ONE := by
      have e : (P * ONE) * ONE = ONE * ONE * P := by
        rw [Nat.mul_assoc P ONE ONE, Nat.mul_comm P (ONE * ONE)]
      have h2 : (c * E) * R ≤ (c * R) * ONE := by
        have h3 : (c * E) * R ≤ (c * ONE) * R :=
          Nat.mul_le_mul_right R (Nat.mul_le_mul_left c hE)
        have e3 : (c * ONE) * R = (c * R) * ONE := by
          rw [Nat.mul_assoc c ONE R, Nat.mul_comm ONE R, ← Nat.mul_assoc c R ONE]
        omega
      omega
    exact le_of_mul_le_mul_right' _ _ _ one_pos h1
  have hPdiv : P ≤ c * R / ONE := le_div_of_mul_le _ _ _ one_pos hPR
  have g1 : B * R / ONE + P ≤ (B * R + c * R) / ONE := by
    have g1a : B * R / ONE + P ≤ B * R / ONE + c * R / ONE :=
      Nat.add_le_add (Nat.le_refl _) hPdiv
    have g1b : B * R / ONE + c * R / ONE ≤ (B * R + c * R) / ONE := add_div_le _ _
    exact Nat.le_trans g1a g1b
  have g2 : B * R + c * R ≤ (B + c) * R := by
    have e : (B + c) * R = B * R + c * R := Nat.add_mul _ _ _
    omega
  exact Nat.le_trans g1 (div_mono_one _ _ g2)

private theorem succ_sub_le_self (x : Nat) : x + 1 - 1 ≤ x := by omega

/-- `a < (a / d + 1) * d` for positive `d`. -/
private theorem lt_succ_mul_of_pos (a d : Nat) (hd : 0 < d) : a < (a / d + 1) * d := by
  have h1 := Nat.div_add_mod a d
  have h2 := Nat.mod_lt a hd
  have h3 : (a / d + 1) * d = d * (a / d) + d := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a / d) d]
  omega

/-- From `x * k ≤ y` conclude `x ≤ y / k`. -/
private theorem le_div_of_mul_le (x y k : Nat) (hk : 0 < k) (h : x * k ≤ y) :
    x ≤ y / k := by
  rcases Nat.lt_or_ge (y / k) x with hlt | hge
  · exfalso
    have h1 : y / k + 1 ≤ x := hlt
    have h2 : (y / k + 1) * k ≤ x * k := Nat.mul_le_mul_right k h1
    have h3 : y < (y / k + 1) * k := lt_succ_mul_of_pos y k hk
    omega
  · exact hge

/-- Strict inequality survives multiplication on the right. -/
private theorem strict_mul_right {u v r : Nat} (h : u < v) (hr : 0 < r) :
    u * r < v * r := by
  have h1 : u + 1 ≤ v := h
  have h2 : (u + 1) * r ≤ v * r := Nat.mul_le_mul_right r h1
  have h3 : (u + 1) * r = u * r + r := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The spec's ceiling: `x ≤ ((x - 1) / b + 1) * b`. -/
private theorem divUp_ge' (x b : Nat) (hx : 0 < x) (hb : 0 < b) :
    x ≤ ((x - 1) / b + 1) * b := by
  have h1 := Nat.div_add_mod (x - 1) b
  have h2 := Nat.mod_lt (x - 1) hb
  have h3 : ((x - 1) / b + 1) * b = b * ((x - 1) / b) + b := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((x - 1) / b) b]
  have h4 : x - 1 + 1 = x := Nat.sub_add_cancel hx
  omega

/-- The spec's ceiling times the divisor stays below `x + b`. -/
private theorem divUp_lt' (x b : Nat) (hx : 0 < x) (hb : 0 < b) :
    ((x - 1) / b + 1) * b < x + b := by
  have h := Nat.div_mul_le_self (x - 1) b
  have h3 : ((x - 1) / b + 1) * b = (x - 1) / b * b + b := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- `(a + (d - 1)) / d` times `d` covers `a`. -/
private theorem ceil_ge' (a d : Nat) (hd : 0 < d) : a ≤ (a + (d - 1)) / d * d := by
  have h1 := Nat.div_add_mod (a + (d - 1)) d
  have h2 := Nat.mod_lt (a + (d - 1)) hd
  rw [Nat.mul_comm]
  omega

/-- Lower bound for the spec's `scaleUp`: `a * r ≤ scaleUp a r * ONE`. -/
private theorem scaleUp_ge (a r : Nat) : a * r ≤ scaleUp a r * ONE := by
  unfold scaleUp
  exact ceil_ge' (a * r) ONE one_pos

/-- Upper bound for the spec's `scaleUp`. -/
private theorem scaleUp_lt (a r : Nat) : scaleUp a r * ONE < a * r + ONE := by
  unfold scaleUp
  have h := Nat.div_mul_le_self (a * r + (ONE - 1)) ONE
  have hO := one_pos
  omega

/-- `mulUp` bracket: `a * b ≤ mulUp a b * ONE < a * b + ONE`. -/
private theorem mulUp_bounds (a b : Nat) :
    a * b ≤ mulUp a b * ONE ∧ mulUp a b * ONE < a * b + ONE := by
  unfold mulUp
  by_cases h : a * b = 0
  · rw [ite_eq_left h, h]
    exact ⟨Nat.zero_le _, one_pos⟩
  · rw [ite_eq_right h]
    have hb := one_pos
    have hx : 0 < a * b := Nat.pos_of_ne_zero h
    exact ⟨divUp_ge' (a * b) ONE hx hb, divUp_lt' (a * b) ONE hx hb⟩

/-- From `divUp a b = some q` with `0 < b`: `a * ONE ≤ q * b`, and the matching
upper bound when `0 < a`. -/
private theorem divUp_bounds {a b q : Nat} (hb : 0 < b) (h : divUp a b = some q) :
    a * ONE ≤ q * b ∧ (q - 1) * b < a * ONE + b ∧ (0 < a → (q - 1) * b < a * ONE) := by
  unfold divUp at h
  rw [ite_eq_right (show b ≠ 0 by omega)] at h
  by_cases ha : a = 0
  · rw [ite_eq_left ha] at h
    cases h
    rw [ha]
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · have h1 : (0 - 1) * b = 0 := by simp
      have h2 : (0 : Nat) * ONE + b = b := by simp
      omega
    · intro h0
      exact absurd h0 (by decide)
  · rw [ite_eq_right ha] at h
    cases h
    have hx : 0 < a * ONE := by
      have hO := one_pos
      have h1 : 0 < a := Nat.pos_of_ne_zero ha
      have h2 : 0 < a * ONE := Nat.mul_pos h1 hO
      exact h2
    refine ⟨divUp_ge' (a * ONE) b hx hb, ?_, ?_⟩
    · have hU := divUp_lt' (a * ONE) b hx hb
      have hO := one_pos
      have hle2inner : (a * ONE - 1) / b + 1 - 1 ≤ (a * ONE - 1) / b + 1 :=
        succ_sub_le _
      have hle2 : ((a * ONE - 1) / b + 1 - 1) * b ≤ ((a * ONE - 1) / b + 1) * b :=
        Nat.mul_le_mul_right b hle2inner
      omega
    · intro _
      have hL := Nat.div_mul_le_self (a * ONE - 1) b
      have hO := one_pos
      have hx' : 0 < a * ONE := hx
      have hle3inner : (a * ONE - 1) / b + 1 - 1 ≤ (a * ONE - 1) / b :=
        succ_sub_le_self _
      have hle3m : ((a * ONE - 1) / b + 1 - 1) * b ≤ ((a * ONE - 1) / b) * b :=
        Nat.mul_le_mul_right b hle3inner
      omega

/-- From `divDown a b = some q` with `0 < b`: `q * b ≤ a * ONE`. -/
private theorem divDown_bound {a b q : Nat} (hb : 0 < b) (h : divDown a b = some q) :
    q * b ≤ a * ONE := by
  unfold divDown at h
  rw [ite_eq_right (show b ≠ 0 by omega)] at h
  by_cases ha : a = 0
  · rw [ite_eq_left ha] at h
    cases h
    simp
  · rw [ite_eq_right ha] at h
    cases h
    exact Nat.div_mul_le_self _ _

/-- `divDown` always answers when the divisor is positive. -/
private theorem divDown_some (a b : Nat) (hb : 0 < b) : ∃ q, divDown a b = some q := by
  unfold divDown
  rw [ite_eq_right (show b ≠ 0 by omega)]
  by_cases ha : a = 0
  · rw [ite_eq_left ha]; exact ⟨0, rfl⟩
  · rw [ite_eq_right ha]; exact ⟨a * ONE / b, rfl⟩

/-- A positive complement means the fee is below one. -/
private theorem fee_lt_of_compl (f e : Nat) (hc : complement f = e) (he : 0 < e) :
    f < ONE := by
  unfold complement at hc
  by_cases h : f < ONE
  · exact h
  · rw [ite_eq_right h] at hc
    omega

/-- The complement unfolds when the fee is below one. -/
private theorem compl_eq_of_lt (f : Nat) (hf : f < ONE) : complement f = ONE - f := by
  unfold complement
  rw [ite_eq_left hf]

/-- The fee charge fits in the amount when the fee is below one. -/
private theorem feeUp_le_of_fee_lt (a f : Nat) (hf : f < ONE) : mulUp a f ≤ a := by
  unfold mulUp
  by_cases h : a * f = 0
  · rw [ite_eq_left h]; exact Nat.zero_le a
  · rw [ite_eq_right h]
    have hfa : a * f ≤ a * ONE := Nat.mul_le_mul_left a (by omega)
    have key : (a * f - 1) / ONE < a := by
      rcases Nat.lt_or_ge ((a * f - 1) / ONE) a with hlt | hge
      · exact hlt
      · exfalso
        have h3 : a * ONE ≤ ((a * f - 1) / ONE) * ONE :=
          Nat.mul_le_mul_right ONE hge
        have hL := Nat.div_mul_le_self (a * f - 1) ONE
        omega
    exact key

/-- `subtractSwapFeeAmount` answers when the fee is below one. -/
private theorem subFee_some (a f : Nat) (hf : f < ONE) :
    subtractSwapFeeAmount a f = some (a - mulUp a f) := by
  unfold subtractSwapFeeAmount
  rw [ite_eq_left (feeUp_le_of_fee_lt a f hf)]

/-- The Vault move used by a successful step. -/
private theorem settle_some {p : Pool} {s : Swap} {q : Nat}
    (h : amountOut s q ≤ p.balance s.tokenOut) :
    ∃ p', settle p s q = some p' := by
  unfold settle
  rw [ite_eq_left h]
  exact ⟨_, rfl⟩

/-- A successful step keeps the token count. -/
private theorem step_n (impl : Impl) (m : PoolMath) (p : Pool) (s : Swap) (q : Pool)
    (h : step impl m p s = some q) : q.n = p.n := by
  unfold step at h
  by_cases hv : Valid p s
  · rw [ite_eq_left hv] at h
    cases him : impl m p s with
    | none =>
      simp [him] at h
    | some c =>
      simp only [him] at h
      unfold settle at h
      by_cases hs : amountOut s c ≤ p.balance s.tokenOut
      · rw [ite_eq_left hs] at h
        cases h
        rfl
      · rw [ite_eq_right hs] at h
        simp at h
  · rw [ite_eq_right hv] at h
    simp at h

/-- `onSwap` on a given-in request. -/
private theorem onSwap_givenIn (m : PoolMath) (p : Pool) (s : Swap)
    (hk : s.kind = .givenIn) : onSwap m p s = swapGivenIn m p s := by
  unfold onSwap
  rw [hk]

/-- `onSwap` on a given-out request. -/
private theorem onSwap_givenOut (m : PoolMath) (p : Pool) (s : Swap)
    (hk : s.kind = .givenOut) : onSwap m p s = swapGivenOut m p s := by
  unfold onSwap
  rw [hk]

/-- The raw amount in of a given-in swap is the request amount. -/
private theorem amountIn_givenIn (s : Swap) (q : Nat) (hk : s.kind = .givenIn) :
    amountIn s q = s.amount := by
  unfold amountIn
  rw [hk]

/-- The raw amount out of a given-in swap is the quote. -/
private theorem amountOut_givenIn (s : Swap) (q : Nat) (hk : s.kind = .givenIn) :
    amountOut s q = q := by
  unfold amountOut
  rw [hk]

/-- The raw amount in of a given-out swap is the quote. -/
private theorem amountIn_givenOut (s : Swap) (q : Nat) (hk : s.kind = .givenOut) :
    amountIn s q = q := by
  unfold amountIn
  rw [hk]

/-- The raw amount out of a given-out swap is the request amount. -/
private theorem amountOut_givenOut (s : Swap) (q : Nat) (hk : s.kind = .givenOut) :
    amountOut s q = s.amount := by
  unfold amountOut
  rw [hk]

/-- A successful fee subtraction bounds the fee charge. -/
private theorem subFee_le {a f A' : Nat} (h : subtractSwapFeeAmount a f = some A') :
    mulUp a f ≤ a ∧ A' = a - mulUp a f := by
  unfold subtractSwapFeeAmount at h
  by_cases hc : mulUp a f ≤ a
  · rw [ite_eq_left hc] at h
    cases h
    exact ⟨hc, rfl⟩
  · rw [ite_eq_right hc] at h
    simp at h

/-- A successful `divDown` forces a positive divisor. -/
private theorem divDown_pos {a b q : Nat} (h : divDown a b = some q) : 0 < b := by
  unfold divDown at h
  by_cases hb : b = 0
  · rw [ite_eq_left hb] at h
    simp at h
  · exact Nat.pos_of_ne_zero hb

/-- A successful `divDown` is the floor division. -/
private theorem divDown_eq {a b q : Nat} (hb : 0 < b) (h : divDown a b = some q) :
    q = a * ONE / b := by
  unfold divDown at h
  rw [ite_eq_right (show b ≠ 0 by omega)] at h
  by_cases ha : a = 0
  · rw [ite_eq_left ha] at h
    cases h
    rw [ha]
    simp
  · rw [ite_eq_right ha] at h
    cases h
    rfl

/-- Invert a successful `_swapGivenIn`. -/
private theorem swapGivenIn_some (m : PoolMath) (p : Pool) (s : Swap) (y : Nat)
    (h : swapGivenIn m p s = some y) :
    ∃ A' XG, subtractSwapFeeAmount s.amount p.fee = some A' ∧
      XG = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale A' (p.rate s.tokenIn)) ∧
      downscaleDown XG (p.rate s.tokenOut) = some y := by
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    have hnone : swapGivenIn m p s = none := by
      unfold swapGivenIn
      rw [hsub]
    rw [hnone] at h
    simp at h
  | some A' =>
    have hbody : swapGivenIn m p s =
        downscaleDown
          (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
            (upscale A' (p.rate s.tokenIn)))
          (p.rate s.tokenOut) := by
      unfold swapGivenIn
      rw [hsub]
    rw [hbody] at h
    exact ⟨A', _, rfl, rfl, h⟩

/-- Invert a successful `_swapGivenOut`. -/
private theorem swapGivenOut_some (m : PoolMath) (p : Pool) (s : Swap) (c : Nat)
    (h : swapGivenOut m p s = some c) :
    ∃ P D, scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut ∧
      P = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) ∧
      downscaleUp P (p.rate s.tokenIn) = some D ∧
      addSwapFeeAmount D p.fee = some c := by
  have hunf : swapGivenOut m p s =
      (if scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut then
        match downscaleUp
          (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)))
          (p.rate s.tokenIn) with
        | none => none
        | some amountIn => addSwapFeeAmount amountIn p.fee
      else none) := rfl
  rw [hunf] at h
  by_cases hlt : scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · rw [ite_eq_left hlt] at h
    cases he : downscaleUp
        (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)))
        (p.rate s.tokenIn) with
    | none =>
      simp [he] at h
    | some D =>
      simp only [he] at h
      exact ⟨_, D, hlt, rfl, he, h⟩
  · rw [ite_eq_right hlt] at h
    simp at h

/-- A successful `divUp` forces a positive divisor. -/
private theorem divUp_pos {a b q : Nat} (h : divUp a b = some q) : 0 < b := by
  unfold divUp at h
  by_cases hb : b = 0
  · rw [ite_eq_left hb] at h
    simp at h
  · exact Nat.pos_of_ne_zero hb

/-- `divUp` of zero is zero. -/
private theorem divUp_zero {b q : Nat} (h : divUp 0 b = some q) : q = 0 := by
  unfold divUp at h
  by_cases hb : b = 0
  · rw [ite_eq_left hb] at h
    simp at h
  · rw [ite_eq_right hb, ite_eq_left rfl] at h
    cases h
    rfl

/-- Cancel a common positive multiplier on the right. -/
private theorem le_of_mul_le_mul_right' (x y b : Nat) (hb : 0 < b)
    (h : x * b ≤ y * b) : x ≤ y := by
  rcases Nat.lt_or_ge y x with hlt | hge
  · exfalso
    have h1 : (y + 1) * b ≤ x * b := Nat.mul_le_mul_right b hlt
    have h2 : (y + 1) * b = y * b + b := by rw [Nat.add_mul, Nat.one_mul]
    omega
  · exact hge

/-- Cross-multiplied comparison gives a comparison of floors. -/
private theorem div_le_div_of_mul_le (a b c d : Nat) (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  apply le_div_of_mul_le _ _ _ hd
  apply le_of_mul_le_mul_right' _ _ _ hb
  have h1 : ((a / b) * d) * b = ((a / b) * b) * d := by
    rw [Nat.mul_assoc, Nat.mul_comm d b, ← Nat.mul_assoc]
  have h2 := Nat.div_mul_le_self a b
  have h3 : ((a / b) * b) * d ≤ a * d := Nat.mul_le_mul_right d h2
  omega

/-- When the fee charge fits, a positive fee forces the amount to vanish. -/
private theorem zero_of_feeUp (a f : Nat) (hle : mulUp a f ≤ a)
    (hf1 : ¬ f ≤ ONE) : a = 0 := by
  have hf2 : ONE < f := by omega
  have h1 : a * (ONE + 1) ≤ a * f := Nat.mul_le_mul_left a hf2
  have e : a * (ONE + 1) = a * ONE + a := Nat.mul_succ a ONE
  have g1 := (mulUp_bounds a f).1
  have g2 : mulUp a f * ONE ≤ a * ONE := Nat.mul_le_mul_right ONE hle
  omega

/-- The wrapped fee-adjusted amount is below the spec's net amount. -/
private theorem upscale_subFee_le (a f r : Nat) (hle : mulUp a f ≤ a) :
    upscale (a - mulUp a f) r ≤ a * (ONE - f) * r / (ONE * ONE) := by
  by_cases hf1 : f ≤ ONE
  · have hfa : a * f ≤ a * ONE := Nat.mul_le_mul_left a hf1
    have hAf : (a - mulUp a f) * ONE + a * f ≤ a * ONE := by
      have g1 := (mulUp_bounds a f).1
      have g2 : (a - mulUp a f) + mulUp a f = a := Nat.sub_add_cancel hle
      have g3 : ((a - mulUp a f) + mulUp a f) * ONE = a * ONE := by rw [g2]
      rw [Nat.add_mul] at g3
      omega
    have hsplit : a * ONE = a * (ONE - f) + a * f := by
      have e : a * (ONE - f) = a * ONE - a * f := Nat.mul_sub a ONE f
      omega
    have hX2 : (a - mulUp a f) * ONE ≤ a * (ONE - f) := by omega
    have hX1 : upscale (a - mulUp a f) r * ONE ≤ (a - mulUp a f) * r := by
      show ((a - mulUp a f) * r / ONE) * ONE ≤ _
      exact Nat.div_mul_le_self _ _
    have hgoal : upscale (a - mulUp a f) r * (ONE * ONE) ≤ a * (ONE - f) * r := by
      have h1 : upscale (a - mulUp a f) r * ONE * ONE ≤
          ((a - mulUp a f) * r) * ONE :=
        Nat.mul_le_mul_right ONE hX1
      have e1 : ((a - mulUp a f) * r) * ONE = ((a - mulUp a f) * ONE) * r := by
        rw [Nat.mul_assoc, Nat.mul_comm r ONE, ← Nat.mul_assoc]
      have h2 : ((a - mulUp a f) * ONE) * r ≤ (a * (ONE - f)) * r :=
        Nat.mul_le_mul_right r hX2
      have e2 : upscale (a - mulUp a f) r * (ONE * ONE) =
          upscale (a - mulUp a f) r * ONE * ONE :=
        (Nat.mul_assoc _ _ _).symm
      omega
    exact le_div_of_mul_le _ _ _ (Nat.mul_pos one_pos one_pos) hgoal
  · have ha0 := zero_of_feeUp a f hle hf1
    subst ha0
    simp [upscale, mulDown, mulUp]

/-- The spec's lower net amount is below the wrapped fee-adjusted amount. -/
private theorem netLess_le_upscale (a f r : Nat) (hle : mulUp a f ≤ a) :
    (a * (ONE - f) - ONE) * r / (ONE * ONE) ≤ upscale (a - mulUp a f) r := by
  by_cases hf1 : f ≤ ONE
  · have hfa : a * f ≤ a * ONE := Nat.mul_le_mul_left a hf1
    have hB := mulUp_bounds a f
    have hA : (a - mulUp a f) * ONE + mulUp a f * ONE = a * ONE := by
      have e : ((a - mulUp a f) + mulUp a f) * ONE = a * ONE := by
        rw [Nat.sub_add_cancel hle]
      rw [Nat.add_mul] at e
      exact e
    have hN : a * (ONE - f) = a * ONE - a * f := Nat.mul_sub a ONE f
    have hleN : a * (ONE - f) ≤ (a - mulUp a f) * ONE + ONE := by omega
    have hsub : a * (ONE - f) - ONE ≤ (a - mulUp a f) * ONE := by omega
    have key : (a * (ONE - f) - ONE) * ONE ≤ (a - mulUp a f) * (ONE * ONE) := by
      have eA : (a - mulUp a f) * (ONE * ONE) = ((a - mulUp a f) * ONE) * ONE := by
        rw [← Nat.mul_assoc]
      rw [eA]
      exact Nat.mul_le_mul_right ONE hsub
    have e1 : ((a * (ONE - f) - ONE) * r) * ONE =
        ((a * (ONE - f) - ONE) * ONE) * r := by
      rw [Nat.mul_assoc, Nat.mul_comm r ONE, ← Nat.mul_assoc]
    have e2 : ((a - mulUp a f) * r) * (ONE * ONE) =
        ((a - mulUp a f) * (ONE * ONE)) * r := by
      rw [Nat.mul_assoc, Nat.mul_comm r (ONE * ONE), ← Nat.mul_assoc]
    have hmul : ((a * (ONE - f) - ONE) * r) * ONE ≤
        ((a - mulUp a f) * r) * (ONE * ONE) := by
      have h3 : ((a * (ONE - f) - ONE) * ONE) * r ≤
          ((a - mulUp a f) * (ONE * ONE)) * r :=
        Nat.mul_le_mul_right r key
      omega
    exact div_le_div_of_mul_le _ _ _ _ (Nat.mul_pos one_pos one_pos) one_pos hmul
  · have ha0 := zero_of_feeUp a f hle hf1
    subst ha0
    simp [upscale, mulDown, mulUp]

theorem req_given_in_pays_at_most : GivenInPaysAtMost onSwap := by
  intro m p s q hpm hk hv him
  unfold Valid at hv
  obtain ⟨hne, hi, hj⟩ := hv
  have heq : swapGivenIn m p s = some q := by
    rw [← onSwap_givenIn m p s hk]
    exact him
  obtain ⟨A', XG, hsub, rfl, hy⟩ := swapGivenIn_some m p s q heq
  have hleA := (subFee_le hsub).1
  have hAeq := (subFee_le hsub).2
  have hXle : upscale A' (p.rate s.tokenIn) ≤ netInDown p s := by
    rw [hAeq]
    exact upscale_subFee_le s.amount p.fee (p.rate s.tokenIn) hleA
  have hpmA : (∀ (b : Nat → Nat) (i j x y : Nat),
      x ≤ y → m.outGivenIn b i j x ≤ m.outGivenIn b i j y) ∧
      (∀ (b : Nat → Nat) (i j x y : Nat),
      x ≤ y → m.inGivenOut b i j x ≤ m.inGivenOut b i j y) := hpm
  obtain ⟨hout, hin⟩ := hpmA
  have hmono : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale A' (p.rate s.tokenIn)) ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
    rw [balances_eq]
    exact hout _ _ _ _ _ hXle
  have hrOut : 0 < p.rate s.tokenOut := divDown_pos hy
  have e1 : q * p.rate s.tokenOut ≤
      m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale A' (p.rate s.tokenIn)) * ONE :=
    divDown_bound hrOut hy
  have e2 : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale A' (p.rate s.tokenIn)) * ONE ≤
      m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
    Nat.mul_le_mul_right ONE hmono
  have e3 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE =
      ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
    Nat.mul_comm _ _
  omega

theorem req_given_in_pays_at_least : GivenInPaysAtLeast onSwap := by
  intro m p s q hpm hk hv him
  unfold Valid at hv
  obtain ⟨hne, hi, hj⟩ := hv
  have heq : swapGivenIn m p s = some q := by
    rw [← onSwap_givenIn m p s hk]
    exact him
  obtain ⟨A', XG, hsub, rfl, hy⟩ := swapGivenIn_some m p s q heq
  have hleA := (subFee_le hsub).1
  have hAeq := (subFee_le hsub).2
  have hXge : netInLessOneDown p s ≤ upscale A' (p.rate s.tokenIn) := by
    rw [hAeq]
    exact netLess_le_upscale s.amount p.fee (p.rate s.tokenIn) hleA
  have hpmA : (∀ (b : Nat → Nat) (i j x y : Nat),
      x ≤ y → m.outGivenIn b i j x ≤ m.outGivenIn b i j y) ∧
      (∀ (b : Nat → Nat) (i j x y : Nat),
      x ≤ y → m.inGivenOut b i j x ≤ m.inGivenOut b i j y) := hpm
  obtain ⟨hout, hin⟩ := hpmA
  have hmono : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
      (netInLessOneDown p s) ≤
      m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale A' (p.rate s.tokenIn)) := by
    rw [balances_eq]
    exact hout _ _ _ _ _ hXge
  have hrOut : 0 < p.rate s.tokenOut := divDown_pos hy
  have hey : q = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale A' (p.rate s.tokenIn)) * ONE / p.rate s.tokenOut :=
    divDown_eq hrOut hy
  have hfl : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale A' (p.rate s.tokenIn)) * ONE <
      (q + 1) * p.rate s.tokenOut := by
    rw [hey]
    exact lt_succ_mul_of_pos _ _ hrOut
  have e1 : ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
      (netInLessOneDown p s) ≤
      ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale A' (p.rate s.tokenIn)) :=
    Nat.mul_le_mul_left ONE hmono
  have e2 : ONE * m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale A' (p.rate s.tokenIn)) =
      m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale A' (p.rate s.tokenIn)) * ONE :=
    Nat.mul_comm _ _
  omega

theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hpm hk hv him
  unfold Valid at hv
  obtain ⟨hne, hi, hj⟩ := hv
  have heq : swapGivenOut m p s = some c := by
    rw [← onSwap_givenOut m p s hk]
    exact him
  obtain ⟨P, D, hlt, rfl, hD, hc⟩ := swapGivenOut_some m p s c heq
  have hrIn : 0 < p.rate s.tokenIn := divUp_pos hD
  have hcompl : 0 < complement p.fee := divUp_pos hc
  have hfee : p.fee < ONE := fee_lt_of_compl _ _ rfl hcompl
  have hcE : complement p.fee = ONE - p.fee := compl_eq_of_lt _ hfee
  have hc' : divUp D (ONE - p.fee) = some c := by
    rw [← hcE]
    exact hc
  have hEpos : 0 < ONE - p.fee := by omega
  obtain ⟨hDlo, hDhi, hDhi'⟩ := divUp_bounds hrIn hD
  obtain ⟨hclo, hchi, hchi'⟩ := divUp_bounds hEpos hc'
  have eP : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) = outPrice m p s := by
    unfold outPrice
    rw [balances_eq]
  rw [← eP]
  have h1 : (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE ≤
      (D * p.rate s.tokenIn) * ONE :=
    Nat.mul_le_mul_right ONE hDlo
  have e1 : (D * p.rate s.tokenIn) * ONE = (D * ONE) * p.rate s.tokenIn := by
    rw [Nat.mul_assoc D (p.rate s.tokenIn) ONE, Nat.mul_comm (p.rate s.tokenIn) ONE,
      ← Nat.mul_assoc D ONE (p.rate s.tokenIn)]
  have h2 : (D * ONE) * p.rate s.tokenIn ≤ (c * (ONE - p.fee)) * p.rate s.tokenIn :=
    Nat.mul_le_mul_right _ hclo
  have e2 : ONE * ONE *
      m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) =
      (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) * ONE) * ONE := by
    rw [Nat.mul_comm (ONE * ONE) _, ← Nat.mul_assoc]
  omega

theorem req_given_out_charges_at_most : GivenOutChargesAtMost onSwap := by
  intro m p s c hpm hk hv him
  unfold Valid at hv
  obtain ⟨hne, hi, hj⟩ := hv
  have heq : swapGivenOut m p s = some c := by
    rw [← onSwap_givenOut m p s hk]
    exact him
  obtain ⟨P, D, hlt, rfl, hD, hc⟩ := swapGivenOut_some m p s c heq
  have hrIn : 0 < p.rate s.tokenIn := divUp_pos hD
  have hcompl : 0 < complement p.fee := divUp_pos hc
  have hfee : p.fee < ONE := fee_lt_of_compl _ _ rfl hcompl
  have hcE : complement p.fee = ONE - p.fee := compl_eq_of_lt _ hfee
  have hc' : divUp D (ONE - p.fee) = some c := by
    rw [← hcE]
    exact hc
  have hEpos : 0 < ONE - p.fee := by omega
  obtain ⟨hDlo, hDhi, hDhi'⟩ := divUp_bounds hrIn hD
  obtain ⟨hclo, hchi, hchi'⟩ := divUp_bounds hEpos hc'
  have eP : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) = outPrice m p s := by
    unfold outPrice
    rw [balances_eq]
  rw [← eP]
  by_cases hP0 : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) = 0
  · have hDz : downscaleUp 0 (p.rate s.tokenIn) = some D := by
      rw [hP0] at hD
      exact hD
    have hD0 : D = 0 := divUp_zero hDz
    subst hD0
    have hc0 : c = 0 := divUp_zero hc'
    subst hc0
    rw [hP0]
    have hL : ((0 : Nat) - 1) * (ONE - p.fee) * p.rate s.tokenIn = 0 := by simp
    rw [hL]
    exact Nat.mul_pos one_pos (by omega)
  · have hGpos : 0 < m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) :=
      Nat.pos_of_ne_zero hP0
    have hDpos : 0 < D := by
      have h1 : 0 < m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE :=
        Nat.mul_pos hGpos one_pos
      have h2 : 0 < D * p.rate s.tokenIn := by omega
      rcases Nat.eq_zero_or_pos D with hD0 | hDpos
      · exfalso
        rw [hD0] at h2
        simp at h2
      · exact hDpos
    have hA : (c - 1) * (ONE - p.fee) < D * ONE := hchi' hDpos
    have hB : (c - 1) * (ONE - p.fee) * p.rate s.tokenIn <
        (D * ONE) * p.rate s.tokenIn :=
      strict_mul_right hA hrIn
    have eM : (D * ONE) * p.rate s.tokenIn =
        (D * p.rate s.tokenIn) * ONE := by
      rw [Nat.mul_assoc D ONE (p.rate s.tokenIn),
        Nat.mul_comm ONE (p.rate s.tokenIn),
        ← Nat.mul_assoc D (p.rate s.tokenIn) ONE]
    have eD : D * p.rate s.tokenIn =
        (D - 1) * p.rate s.tokenIn + p.rate s.tokenIn := by
      have e : (D - 1) + 1 = D := Nat.sub_add_cancel hDpos
      have e2 : ((D - 1) + 1) * p.rate s.tokenIn = D * p.rate s.tokenIn := by
        rw [e]
      rw [Nat.add_mul, Nat.one_mul] at e2
      exact e2.symm
    have h3 : D * p.rate s.tokenIn <
        m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn := by
      omega
    have h4 : (D * p.rate s.tokenIn) * ONE <
        (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE :=
      strict_mul_right h3 one_pos
    have eN : (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) * ONE =
        ONE * (ONE *
          m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) + p.rate s.tokenIn) := by
      rw [Nat.mul_comm (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut)) * ONE + p.rate s.tokenIn) ONE,
        Nat.mul_comm (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
            (scaleUp s.amount (p.rate s.tokenOut))) ONE]
    omega

/-- `divUp` always answers when the divisor is positive. -/
private theorem divUp_some (a b : Nat) (hb : 0 < b) : ∃ q, divUp a b = some q := by
  unfold divUp
  rw [ite_eq_right (show b ≠ 0 by omega)]
  by_cases ha : a = 0
  · rw [ite_eq_left ha]; exact ⟨0, rfl⟩
  · rw [ite_eq_right ha]; exact ⟨(a * ONE - 1) / b + 1, rfl⟩

/-- Floors respect the numerator order. -/
private theorem div_mono_one (a b : Nat) (h : a ≤ b) : a / ONE ≤ b / ONE := by
  apply le_div_of_mul_le _ _ _ one_pos
  have h1 := Nat.div_mul_le_self a ONE
  omega

/-- Floors split over addition. -/
private theorem add_div_le (u w : Nat) :
    u / ONE + w / ONE ≤ (u + w) / ONE := by
  apply le_div_of_mul_le _ _ _ one_pos
  have h1 := Nat.div_mul_le_self u ONE
  have h2 := Nat.div_mul_le_self w ONE
  have e : (u / ONE + w / ONE) * ONE = u / ONE * ONE + w / ONE * ONE :=
    Nat.add_mul _ _ _
  omega

/-- Invert a successful Vault step. -/
private theorem step_some_inv {impl : Impl} {m : PoolMath} {p : Pool} {s : Swap}
    {p' : Pool} (h : step impl m p s = some p') :
    Valid p s ∧ ∃ c, impl m p s = some c ∧ settle p s c = some p' := by
  unfold step at h
  by_cases hv : Valid p s
  · rw [ite_eq_left hv] at h
    refine ⟨hv, ?_⟩
    have hne : impl m p s ≠ none := by
      intro hcon
      rw [hcon] at h
      simp at h
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists.mp hne
    rw [← hc] at h
    exact ⟨c, hc.symm, h⟩
  · rw [ite_eq_right hv] at h
    simp at h

theorem req_given_out_succeeds : GivenOutSucceeds onSwap := by
  intro m p s hwb hk hv hr hf hscale
  have hlt : scaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut := by
    rw [balances_eq]
    exact hscale
  have hR : 0 < p.rate s.tokenOut := by
    by_cases hR0 : p.rate s.tokenOut = 0
    · exfalso
      have e1 : scaleUp s.amount (p.rate s.tokenOut) = 0 := by
        rw [hR0]
        unfold scaleUp
        have z1 : s.amount * 0 + (ONE - 1) = ONE - 1 := by simp
        rw [z1]
        decide
      have e2 : scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) = 0 := by
        rw [hR0]
        unfold scaleDown
        simp
      omega
    · exact Nat.pos_of_ne_zero hR0
  have hAB : s.amount ≤ p.balance s.tokenOut := by
    rcases Nat.lt_or_ge (p.balance s.tokenOut) s.amount with hltB | hge
    · exfalso
      have h1 : (p.balance s.tokenOut + 1) * p.rate s.tokenOut ≤
          s.amount * p.rate s.tokenOut :=
        Nat.mul_le_mul_right _ hltB
      have h2 : (p.balance s.tokenOut + 1) * p.rate s.tokenOut =
          p.balance s.tokenOut * p.rate s.tokenOut + p.rate s.tokenOut := by
        rw [Nat.add_mul, Nat.one_mul]
      have g1 : s.amount * p.rate s.tokenOut ≤
          scaleUp s.amount (p.rate s.tokenOut) * ONE :=
        scaleUp_ge _ _
      have g2 : scaleUp s.amount (p.rate s.tokenOut) + 1 ≤
          scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) :=
        hscale
      have g3 : (scaleUp s.amount (p.rate s.tokenOut) + 1) * ONE ≤
          scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) * ONE :=
        Nat.mul_le_mul_right ONE g2
      have e3 : (scaleUp s.amount (p.rate s.tokenOut) + 1) * ONE =
          scaleUp s.amount (p.rate s.tokenOut) * ONE + ONE := by
        rw [Nat.add_mul, Nat.one_mul]
      have g4 : scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) * ONE ≤
          p.balance s.tokenOut * p.rate s.tokenOut := by
        unfold scaleDown
        exact Nat.div_mul_le_self _ _
      have hO := one_pos
      omega
    · exact hge
  obtain ⟨D, hD⟩ := divUp_some
    (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)))
    (p.rate s.tokenIn) hr
  have hD' : downscaleUp
      (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)))
      (p.rate s.tokenIn) = some D := hD
  have hE : complement p.fee = ONE - p.fee := compl_eq_of_lt _ hf
  have hEpos : 0 < ONE - p.fee := by omega
  obtain ⟨c, hc⟩ := divUp_some D (ONE - p.fee) hEpos
  have hc' : addSwapFeeAmount D p.fee = some c := by
    unfold addSwapFeeAmount
    rw [hE]
    exact hc
  have heq : swapGivenOut m p s = some c := by
    unfold swapGivenOut
    rw [ite_eq_left hlt, hD']
    exact hc'
  have hsB : amountOut s c ≤ p.balance s.tokenOut := by
    rw [amountOut_givenOut s c hk]
    exact hAB
  obtain ⟨p', hs⟩ := settle_some hsB
  have heq2 : onSwap m p s = some c := by
    rw [onSwap_givenOut m p s hk]
    exact heq
  have hstep : step onSwap m p s = some p' := by
    unfold step
    rw [ite_eq_left hv, heq2]
    exact hs
  rw [hstep]
  simp

theorem req_given_in_succeeds : GivenInSucceeds onSwap := by
  intro m p s hwb hk hv hr hf
  unfold Valid at hv
  obtain ⟨hne, hi, hj⟩ := hv
  have hsub := subFee_some s.amount p.fee hf
  obtain ⟨y, hy⟩ := divDown_some
    (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)))
    (p.rate s.tokenOut) hr
  have heq : onSwap m p s = some y := by
    rw [onSwap_givenIn m p s hk]
    unfold swapGivenIn
    rw [hsub]
    exact hy
  have hle : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) ≤
      scaledBalances p s.tokenOut := by
    have h := hwb.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) hne hi hj
    rw [balances_eq] at h
    exact h.1
  have h_yR : y * p.rate s.tokenOut ≤
      p.balance s.tokenOut * p.rate s.tokenOut := by
    have e1 : y * p.rate s.tokenOut ≤
        m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
          (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) * ONE :=
      divDown_bound hr hy
    have e2 : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
          (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) * ONE ≤
        scaledBalances p s.tokenOut * ONE :=
      Nat.mul_le_mul_right ONE hle
    have e3 : scaledBalances p s.tokenOut * ONE ≤
        p.balance s.tokenOut * p.rate s.tokenOut := by
      show (p.balance s.tokenOut * p.rate s.tokenOut / ONE) * ONE ≤ _
      exact Nat.div_mul_le_self _ _
    omega
  have hyB : y ≤ p.balance s.tokenOut := by
    rcases Nat.lt_or_ge (p.balance s.tokenOut) y with hlt | hge
    · exfalso
      have h1 : (p.balance s.tokenOut + 1) * p.rate s.tokenOut ≤
          y * p.rate s.tokenOut :=
        Nat.mul_le_mul_right _ hlt
      have h2 : (p.balance s.tokenOut + 1) * p.rate s.tokenOut =
          p.balance s.tokenOut * p.rate s.tokenOut + p.rate s.tokenOut := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · exact hge
  have hsB : amountOut s y ≤ p.balance s.tokenOut := by
    rw [amountOut_givenIn s y hk]
    exact hyB
  obtain ⟨p', hs⟩ := settle_some hsB
  have hstep : step onSwap m p s = some p' := by
    unfold step
    rw [ite_eq_left ⟨hne, hi, hj⟩, heq]
    exact hs
  rw [hstep]
  simp

theorem req_swap_keeps_value : SwapKeepsValue onSwap := by
  intro m p s p' hwb hstep
  obtain ⟨hv, c, him, hset⟩ := step_some_inv hstep
  unfold Valid at hv
  obtain ⟨hne, hi, hj⟩ := hv
  cases hkind : s.kind with
  | givenIn =>
    have heq : swapGivenIn m p s = some c := by
      rw [← onSwap_givenIn m p s hkind]
      exact him
    obtain ⟨A', XG, hsub, rfl, hy⟩ := swapGivenIn_some m p s c heq
    have hleA := (subFee_le hsub).1
    have hAeq := (subFee_le hsub).2
    have hA'le : A' ≤ s.amount := by
      rw [hAeq]
      exact Nat.sub_le _ _
    have hprice : m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale A' (p.rate s.tokenIn)) =
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
        (upscale A' (p.rate s.tokenIn)) := by
      rw [balances_eq]
    rw [hprice] at hy
    have hsound := hwb.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale A' (p.rate s.tokenIn)) hne hi hj
    rw [balances_eq] at hsound
    have hrOut : 0 < p.rate s.tokenOut := divDown_pos hy
    have hyR : c * p.rate s.tokenOut ≤
        m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
          (upscale A' (p.rate s.tokenIn)) * ONE :=
      divDown_bound hrOut hy
    have hAin : amountIn s c = s.amount := amountIn_givenIn s c hkind
    have hAout : amountOut s c = c := amountOut_givenIn s c hkind
    have hsB : amountOut s c ≤ p.balance s.tokenOut := by
      unfold settle at hset
      by_cases hc : amountOut s c ≤ p.balance s.tokenOut
      · exact hc
      · rw [ite_eq_right hc] at hset
        simp at hset
    have hcB : c ≤ p.balance s.tokenOut := by
      rw [← hAout]
      exact hsB
    unfold settle at hset
    rw [ite_eq_left hsB, hAin, hAout] at hset
    cases hset
    show m.invariant (scaledBalances p) ≤ m.invariant (fun k =>
      update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
        s.tokenOut (p.balance s.tokenOut - c) k * p.rate k / ONE)
    have hpoint : ∀ k, k < p.n →
        update2 (scaledBalances p) s.tokenIn
          (scaledBalances p s.tokenIn + upscale A' (p.rate s.tokenIn)) s.tokenOut
          (scaledBalances p s.tokenOut -
            m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut
              (upscale A' (p.rate s.tokenIn))) k ≤
        (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
          s.tokenOut (p.balance s.tokenOut - c) k * p.rate k / ONE) := by
      intro k hk
      by_cases hi : k = s.tokenIn
      · subst hi
        have eL : update2 (scaledBalances p) s.tokenIn
            (scaledBalances p s.tokenIn + upscale A' (p.rate s.tokenIn)) s.tokenOut
            (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn
              s.tokenOut (upscale A' (p.rate s.tokenIn))) s.tokenIn =
            scaledBalances p s.tokenIn + upscale A' (p.rate s.tokenIn) := by
          unfold update2
          rw [ite_eq_left rfl]
        rw [eL]
        have eR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
            s.tokenOut (p.balance s.tokenOut - c) s.tokenIn * p.rate s.tokenIn / ONE =
            (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE := by
          unfold update2
          rw [ite_eq_left rfl]
        rw [eR]
        have eSb : scaledBalances p s.tokenIn =
            p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
        have eX : upscale A' (p.rate s.tokenIn) =
            A' * p.rate s.tokenIn / ONE := rfl
        rw [eSb, eX, hAeq]
        exact givenIn_i_le _ _ _ _ hA'le
      · by_cases hj : k = s.tokenOut
        · subst hj
          have eL : update2 (scaledBalances p) s.tokenIn
              (scaledBalances p s.tokenIn + upscale A' (p.rate s.tokenIn)) s.tokenOut
              (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn
                s.tokenOut (upscale A' (p.rate s.tokenIn))) s.tokenOut =
              scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn
                s.tokenOut (upscale A' (p.rate s.tokenIn)) := by
            unfold update2
            rw [ite_eq_right hi, ite_eq_left rfl]
          rw [eL]
          have eR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
              s.tokenOut (p.balance s.tokenOut - c) s.tokenOut * p.rate s.tokenOut / ONE =
              (p.balance s.tokenOut - c) * p.rate s.tokenOut / ONE := by
            unfold update2
            rw [ite_eq_right hi, ite_eq_left rfl]
          rw [eR]
          have eSb : scaledBalances p s.tokenOut =
              p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
          rw [eSb]
          exact givenIn_j_le _ _ _ _ hyR hsound.1 hcB
        · have eL : update2 (scaledBalances p) s.tokenIn
            (scaledBalances p s.tokenIn + upscale A' (p.rate s.tokenIn)) s.tokenOut
            (scaledBalances p s.tokenOut - m.outGivenIn (scaledBalances p) s.tokenIn
              s.tokenOut (upscale A' (p.rate s.tokenIn))) k =
            scaledBalances p k := by
          simp only [update2, hi, hj]
        have eR : update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
            s.tokenOut (p.balance s.tokenOut - c) k = p.balance k := by
          simp only [update2, hi, hj]
        have eSb : scaledBalances p k = p.balance k * p.rate k / ONE := rfl
        rw [eL, eR, eSb]
        exact Nat.le_refl _
    exact Nat.le_trans hsound.2 (hwb.monotone _ _ hpoint)
  | givenOut =>
    have heq : swapGivenOut m p s = some c := by
      rw [← onSwap_givenOut m p s hkind]
      exact him
    obtain ⟨P, D, hlt, rfl, hD, hc⟩ := swapGivenOut_some m p s c heq
    have hrIn : 0 < p.rate s.tokenIn := divUp_pos hD
    have hcompl : 0 < complement p.fee := divUp_pos hc
    have hfee : p.fee < ONE := fee_lt_of_compl _ _ rfl hcompl
    have hcE : complement p.fee = ONE - p.fee := compl_eq_of_lt _ hfee
    have hc' : divUp D (ONE - p.fee) = some c := by
      rw [← hcE]
      exact hc
    have hEpos : 0 < ONE - p.fee := by omega
    have hprice : m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) =
        m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
        (scaleUp s.amount (p.rate s.tokenOut)) := by
      rw [balances_eq]
    rw [hprice] at hD
    obtain ⟨hDlo, hDhi, hDhi'⟩ := divUp_bounds hrIn hD
    obtain ⟨hclo, hchi, hchi'⟩ := divUp_bounds hEpos hc'
    have hsound := hwb.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) hne hi hj hlt
    rw [balances_eq] at hsound
    have hltSb : scaleUp s.amount (p.rate s.tokenOut) ≤
        scaledBalances p s.tokenOut :=
      Nat.le_of_lt (by rw [← balances_eq]; exact hlt)
    have hAin : amountIn s c = c := amountIn_givenOut s c hkind
    have hAout : amountOut s c = s.amount := amountOut_givenOut s c hkind
    have hsB : amountOut s c ≤ p.balance s.tokenOut := by
      unfold settle at hset
      by_cases hc : amountOut s c ≤ p.balance s.tokenOut
      · exact hc
      · rw [ite_eq_right hc] at hset
        simp at hset
    have hsAB : s.amount ≤ p.balance s.tokenOut := by
      rw [← hAout]
      exact hsB
    unfold settle at hset
    rw [ite_eq_left hsB, hAin, hAout] at hset
    cases hset
    show m.invariant (scaledBalances p) ≤ m.invariant (fun k =>
      update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
        s.tokenOut (p.balance s.tokenOut - s.amount) k * p.rate k / ONE)
    have hcore : ONE * ONE *
        m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
          (scaleUp s.amount (p.rate s.tokenOut)) ≤
        c * (ONE - p.fee) * p.rate s.tokenIn :=
      charge_core hDlo hclo
    have hE1 : ONE - p.fee ≤ ONE := by omega
    have hpoint : ∀ k, k < p.n →
        update2 (scaledBalances p) s.tokenIn
          (scaledBalances p s.tokenIn +
            m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
              (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
          (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k ≤
        (update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) k * p.rate k / ONE) := by
      intro k hk
      by_cases hi : k = s.tokenIn
      · subst hi
        have eL : update2 (scaledBalances p) s.tokenIn
            (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn
              s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
            (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenIn =
            scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn
              s.tokenOut (scaleUp s.amount (p.rate s.tokenOut)) := by
          unfold update2
          rw [ite_eq_left rfl]
        rw [eL]
        have eR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
            s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenIn * p.rate s.tokenIn / ONE =
            (p.balance s.tokenIn + c) * p.rate s.tokenIn / ONE := by
          unfold update2
          rw [ite_eq_left rfl]
        rw [eR]
        have eSb : scaledBalances p s.tokenIn =
            p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
        rw [eSb]
        exact givenOut_i_le _ _ _ _ _ hcore hE1
      · by_cases hj : k = s.tokenOut
        · subst hj
          have eL : update2 (scaledBalances p) s.tokenIn
              (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn
                s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
              (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) s.tokenOut =
              scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut) := by
            unfold update2
            rw [ite_eq_right hi, ite_eq_left rfl]
          rw [eL]
          have eR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
              s.tokenOut (p.balance s.tokenOut - s.amount) s.tokenOut * p.rate s.tokenOut / ONE =
              (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut / ONE := by
            unfold update2
            rw [ite_eq_right hi, ite_eq_left rfl]
          rw [eR]
          have eSb : scaledBalances p s.tokenOut =
              p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
          rw [eSb]
          exact givenIn_j_le _ _ _ _ (scaleUp_ge _ _) hltSb hsAB
        · have eL : update2 (scaledBalances p) s.tokenIn
            (scaledBalances p s.tokenIn + m.inGivenOut (scaledBalances p) s.tokenIn
              s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))) s.tokenOut
            (scaledBalances p s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k =
            scaledBalances p k := by
          simp only [update2, hi, hj]
        have eR : update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
            s.tokenOut (p.balance s.tokenOut - s.amount) k = p.balance k := by
          simp only [update2, hi, hj]
        have eSb : scaledBalances p k = p.balance k * p.rate k / ONE := rfl
        rw [eL, eR, eSb]
        exact Nat.le_refl _
    exact Nat.le_trans hsound (hwb.monotone _ _ hpoint)

theorem req_batch_keeps_value : BatchKeepsValue onSwap := by
  intro m p ss p' hwb hrun
  induction ss generalizing p p' with
  | nil =>
    have h2 : run onSwap m p [] = some p := rfl
    rw [h2] at hrun
    cases hrun
    exact Nat.le_refl _
  | cons s ss ih =>
    have hrunU : run onSwap m p (s :: ss) =
        match step onSwap m p s with
        | some q => run onSwap m q ss
        | none => none := rfl
    rw [hrunU] at hrun
    cases hst : step onSwap m p s with
    | none =>
      simp [hst] at hrun
    | some q =>
      simp only [hst] at hrun
      have h1 : value m p ≤ value m q := req_swap_keeps_value m p s q hwb hst
      have hqn : q.n = p.n := step_n _ _ _ _ _ hst
      have hwb' : WellBehaved m q.n := by
        rw [hqn]
        exact hwb
      have h2 : value m q ≤ value m p' := ih q p' hwb' hrun
      exact Nat.le_trans h1 h2

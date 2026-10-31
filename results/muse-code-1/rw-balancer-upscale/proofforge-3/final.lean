import BalancerSwap.Spec
import ProofForgeFin.FixedPoint
/-!
Port of the regular-swap path of Balancer V2's Composable Stable Pool, as deployed for the
osETH/WETH pool on Ethereum (0xDACf5Fa19b1f720111609043ac67A9818262850c, source verified on
Sourcify with an exact match, solc 0.7.1):

* `@balancer-labs/v2-pool-utils/contracts/BaseGeneralPool.sol`, `_swapGivenIn` (lines 49 to 66)
  and `_swapGivenOut` (lines 68 to 85);
* `@balancer-labs/v2-pool-utils/contracts/BasePool.sol`, `_addSwapFeeAmount` (618 to 621),
  `_subtractSwapFeeAmount` (626 to 630), `_upscale` (680 to 686), `_upscaleArray` (692 to 699),
  `_downscaleDown` (705 to 707), `_downscaleUp` (726 to 728);
* `@balancer-labs/v2-solidity-utils/contracts/math/FixedPoint.sol`, `mulDown`, `mulUp`,
  `divDown` and `divUp` (48 to 102) and `complement` (158 to 160).

The same logic is in balancer/balancer-v2-monorepo at commit
88842344fb5f44d8ef6f8f944acd3be80627df (`pkg/solidity-utils/contracts/helpers/ScalingHelpers.sol`
lines 35 to 56, `pkg/pool-utils/contracts/BaseGeneralPool.sol` lines 49 to 85).

`ComposableStablePool._swapGivenOut` forwards regular (non-BPT) swaps to
`BaseGeneralPool._swapGivenOut`, and `_onRegularSwap` calls the pool math with the balances
without the BPT. Here the math is the parameter `m`; `StableMath._calcInGivenOut` starts with
`balances[tokenIndexOut].sub(tokenAmountOut)`, which reverts when the amount out exceeds the
balance, and that check is kept. A revert is `none`. Arithmetic is unbounded, so the overflow
checks of `mulDown`, `mulUp`, `divDown` and `divUp` never fail.

Fix (rounding in the pool's favour on the given-out path): the amount out is converted to
18-decimal units rounded *up* (`upscaleUp`), and the swap reverts unless that rounded-up
amount is *strictly* below the pool's scaled balance. Previously the amount out was rounded
down, so a request just below a whole 18-decimal unit was priced at the unit below.
-/
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

/-- Rounding the amount out *up* to 18-decimal units: `(amount * r + (ONE - 1)) / ONE`. -/
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

/-! ## BaseGeneralPool -/

/-- `_swapGivenIn`. -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  match subtractSwapFeeAmount s.amount p.fee with
  | none => none
  | some amount =>
    downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
      (upscale amount (p.rate s.tokenIn))) (p.rate s.tokenOut)

/-- `_swapGivenOut`, with the amount out rounded up and a strict balance check. -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  if upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut then
    match downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
      (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none => none
    | some amountIn => addSwapFeeAmount amountIn p.fee
  else none

/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

/-! ## Rounding bridges -/

theorem hONE : 0 < ONE := by decide

theorem hONEne : ONE ≠ 0 := Nat.pos_iff_ne_zero.mp hONE

theorem upscaleArray_eq (p : Pool) : upscaleArray p = scaledBalances p := rfl

theorem upscaleUp_eq_scaleUp (a r : Nat) : upscaleUp a r = scaleUp a r := rfl

theorem mulUp_eq_ceil (a b : Nat) : mulUp a b = ProofForgeFin.ceilDiv (a * b) ONE := by
  unfold mulUp
  rw [ProofForgeFin.ceilDiv_eq_ite _ _ hONE]

theorem upscaleUp_eq_ceil (a r : Nat) :
    upscaleUp a r = ProofForgeFin.ceilDiv (a * r) ONE := by
  unfold upscaleUp ProofForgeFin.ceilDiv
  have h := hONE
  have he : a * r + (ONE - 1) = a * r + ONE - 1 := by omega
  rw [he]

theorem feeUp_le {amt fee : Nat} (h : fee < ONE) : mulUp amt fee ≤ amt := by
  rw [mulUp_eq_ceil, ProofForgeFin.ceilDiv_le_iff hONE]
  exact Nat.mul_le_mul (Nat.le_refl amt) (Nat.le_of_lt h)

theorem subFee_some {amt fee net : Nat} (h : subtractSwapFeeAmount amt fee = some net) :
    mulUp amt fee ≤ amt ∧ net = amt - mulUp amt fee := by
  unfold subtractSwapFeeAmount at h
  by_cases hc : mulUp amt fee ≤ amt
  · rw [if_pos hc] at h
    cases h
    exact ⟨hc, rfl⟩
  · rw [if_neg hc] at h
    cases h

theorem subFee_add {amt fee net : Nat} (h : subtractSwapFeeAmount amt fee = some net) :
    net + mulUp amt fee = amt := by
  obtain ⟨hle, rfl⟩ := subFee_some h
  exact Nat.sub_add_cancel hle

theorem divDown_some_eq {a b q : Nat} (hb : b ≠ 0) (h : divDown a b = some q) :
    a * ONE / b = q := by
  unfold divDown at h
  simp [hb] at h
  by_cases ha : a = 0
  · simp [ha] at h
    subst h
    simp [ha]
  · simp [ha] at h
    exact h

theorem divUp_some_eq {a b q : Nat} (hb : b ≠ 0) (h : divUp a b = some q) :
    ProofForgeFin.ceilDiv (a * ONE) b = q := by
  unfold divUp at h
  simp [hb] at h
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  by_cases ha : a = 0
  · simp [ha] at h
    subst h
    simp [ha]
  · have hne : a * ONE ≠ 0 := Nat.mul_ne_zero ha hONEne
    simp [ha] at h
    rw [ProofForgeFin.ceilDiv_eq_ite _ _ hbpos, if_neg hne]
    exact h

theorem complement_of_lt {fee : Nat} (h : fee < ONE) : complement fee = ONE - fee := by
  unfold complement
  simp [h]

theorem complement_of_ge {fee : Nat} (h : ¬ fee < ONE) : complement fee = 0 := by
  unfold complement
  simp [h]

theorem divDown_is_some {a b : Nat} (hb : b ≠ 0) :
    divDown a b = some (a * ONE / b) := by
  unfold divDown
  rw [if_neg hb]
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]

theorem divUp_is_some {a b : Nat} (hb : b ≠ 0) :
    divUp a b = some (ProofForgeFin.ceilDiv (a * ONE) b) := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  by_cases ha : a = 0
  · subst ha
    unfold divUp
    rw [if_neg hb]
    simp
  · have hne : a * ONE ≠ 0 := Nat.mul_ne_zero ha hONEne
    unfold divUp
    rw [if_neg hb, if_neg ha, ProofForgeFin.ceilDiv_eq_ite _ _ hbpos, if_neg hne]

theorem amountOut_givenIn (s : Swap) (h : s.kind = .givenIn) (q : Nat) :
    amountOut s q = q := by
  unfold amountOut
  rw [h]

theorem amountIn_givenIn (s : Swap) (h : s.kind = .givenIn) (q : Nat) :
    amountIn s q = s.amount := by
  unfold amountIn
  rw [h]

theorem amountOut_givenOut (s : Swap) (h : s.kind = .givenOut) (q : Nat) :
    amountOut s q = s.amount := by
  unfold amountOut
  rw [h]

theorem amountIn_givenOut (s : Swap) (h : s.kind = .givenOut) (q : Nat) :
    amountIn s q = q := by
  unfold amountIn
  rw [h]

theorem onSwap_givenIn (m : PoolMath) (p : Pool) (s : Swap) (h : s.kind = .givenIn) :
    onSwap m p s = swapGivenIn m p s := by
  unfold onSwap
  rw [h]

theorem onSwap_givenOut (m : PoolMath) (p : Pool) (s : Swap) (h : s.kind = .givenOut) :
    onSwap m p s = swapGivenOut m p s := by
  unfold onSwap
  rw [h]

theorem settle_pack {p : Pool} {s : Swap} {q : Nat} {p' : Pool}
    (h : settle p s q = some p') :
    amountOut s q ≤ p.balance s.tokenOut ∧
    p'.balance = update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s q)
      s.tokenOut (p.balance s.tokenOut - amountOut s q) ∧
    p'.n = p.n ∧ p'.rate = p.rate ∧ p'.fee = p.fee := by
  unfold settle at h
  by_cases hle : amountOut s q ≤ p.balance s.tokenOut
  · rw [if_pos hle] at h
    cases h
    exact ⟨hle, rfl, rfl, rfl, rfl⟩
  · rw [if_neg hle] at h
    cases h

theorem step_pack {impl : Impl} {m : PoolMath} {p : Pool} {s : Swap} {p' : Pool}
    (h : step impl m p s = some p') :
    Valid p s ∧ ∃ q, impl m p s = some q ∧ settle p s q = some p' := by
  unfold step at h
  by_cases hv : Valid p s
  · rw [if_pos hv] at h
    cases hq : impl m p s with
    | none =>
      rw [hq] at h
      simp at h
    | some q =>
      rw [hq] at h
      simp only at h
      exact ⟨hv, q, rfl, h⟩
  · rw [if_neg hv] at h
    cases h

theorem update2_self {b : Nat → Nat} {i x j y : Nat} :
    update2 b i x j y i = x := by
  unfold update2
  simp

theorem update2_other {b : Nat → Nat} {i x j y : Nat} (h : j ≠ i) :
    update2 b i x j y j = y := by
  unfold update2
  simp [h]

theorem update2_ne {b : Nat → Nat} {i x j y k : Nat} (hi : k ≠ i) (hj : k ≠ j) :
    update2 b i x j y k = b k := by
  unfold update2
  simp [hi, hj]

theorem add_floor_ge {U V W D : Nat} (h : W ≤ V) :
    U / D + W / D ≤ (U + V) / D := by
  have h1 : U / D + W / D ≤ (U + W) / D := ProofForgeFin.div_add_div_le _ _ _
  have h2 : (U + W) / D ≤ (U + V) / D :=
    ProofForgeFin.div_mono_left D (Nat.add_le_add (Nat.le_refl _) h)
  exact Nat.le_trans h1 h2

theorem sub_floor_ge {B y r P D : Nat} (h : y * r ≤ P * D) (hD : 0 < D) :
    B * r / D - P ≤ (B - y) * r / D := by
  have e1 : (B - y) * r = B * r - y * r := Nat.sub_mul _ _ _
  have e4 : (B * r / D - P) * D = B * r / D * D - P * D := Nat.sub_mul _ _ _
  have e5 : B * r / D * D ≤ B * r := Nat.div_mul_le_self _ _
  have e3 : (B * r / D - P) * D ≤ (B - y) * r := by omega
  exact (ProofForgeFin.le_div_iff hD).2 e3

theorem outIn_ge {B c rin P Q comp : Nat}
    (eA : P * ONE ≤ Q * rin) (eB : Q * ONE ≤ c * comp) (hcomp : comp ≤ ONE) :
    B * rin / ONE + P ≤ (B + c) * rin / ONE := by
  have eR : Q * rin * ONE = (Q * ONE) * rin := by
    rw [Nat.mul_assoc Q rin ONE, Nat.mul_comm rin ONE, ← Nat.mul_assoc Q ONE rin]
  have e1 : P * ONE * ONE ≤ Q * rin * ONE :=
    Nat.mul_le_mul eA (Nat.le_refl _)
  have e2 : (Q * ONE) * rin ≤ (c * comp) * rin :=
    Nat.mul_le_mul eB (Nat.le_refl _)
  have e3 : (c * comp) * rin ≤ (c * ONE) * rin :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) hcomp) (Nat.le_refl _)
  have e4 : (c * ONE) * rin = c * rin * ONE := by
    rw [Nat.mul_assoc c ONE rin, Nat.mul_comm ONE rin, ← Nat.mul_assoc c rin ONE]
  rw [eR] at e1
  have e5 : (P * ONE) * ONE ≤ (c * rin) * ONE :=
    Nat.le_trans (Nat.le_trans (Nat.le_trans e1 e2) e3) (Nat.le_of_eq e4)
  have eC : P * ONE ≤ c * rin := Nat.le_of_mul_le_mul_right e5 hONE
  have eD : P ≤ c * rin / ONE := (ProofForgeFin.le_div_iff hONE).2 eC
  have eUV : (B + c) * rin = B * rin + c * rin := Nat.add_mul _ _ _
  calc B * rin / ONE + P ≤ B * rin / ONE + c * rin / ONE :=
        Nat.add_le_add (Nat.le_refl _) eD
    _ ≤ (B * rin + c * rin) / ONE := ProofForgeFin.div_add_div_le _ _ _
    _ = (B + c) * rin / ONE := by rw [eUV]

theorem outOut_floor_ge {B a r : Nat} :
    B * r / ONE - ProofForgeFin.ceilDiv (a * r) ONE ≤ (B - a) * r / ONE := by
  have eC : a * r ≤ ProofForgeFin.ceilDiv (a * r) ONE * ONE :=
    ProofForgeFin.le_ceilDiv_mul _ _ hONE
  have e1 : (B - a) * r = B * r - a * r := Nat.sub_mul _ _ _
  have e4 : (B * r / ONE - ProofForgeFin.ceilDiv (a * r) ONE) * ONE
      = B * r / ONE * ONE - ProofForgeFin.ceilDiv (a * r) ONE * ONE := Nat.sub_mul _ _ _
  have e5 : B * r / ONE * ONE ≤ B * r := Nat.div_mul_le_self _ _
  have e3 : (B * r / ONE - ProofForgeFin.ceilDiv (a * r) ONE) * ONE ≤ (B - a) * r := by
    omega
  exact (ProofForgeFin.le_div_iff hONE).2 e3

theorem givenIn_pack {m : PoolMath} {p : Pool} {s : Swap} {y : Nat}
    (h : swapGivenIn m p s = some y) :
    ∃ net px, subtractSwapFeeAmount s.amount p.fee = some net ∧
      px = m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut
        (upscale net (p.rate s.tokenIn)) ∧
      downscaleDown px (p.rate s.tokenOut) = some y := by
  unfold swapGivenIn at h
  cases hsub : subtractSwapFeeAmount s.amount p.fee with
  | none =>
    rw [hsub] at h
    simp at h
  | some net =>
    rw [hsub] at h
    simp only at h
    exact ⟨net, _, rfl, rfl, h⟩

theorem givenOut_pack {m : PoolMath} {p : Pool} {s : Swap} {c : Nat}
    (h : swapGivenOut m p s = some c) :
    upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut ∧
    ∃ rawIn px, downscaleUp px (p.rate s.tokenIn) = some rawIn ∧
      px = m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut)) ∧
      addSwapFeeAmount rawIn p.fee = some c := by
  unfold swapGivenOut at h
  by_cases hlt : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut
  · rw [if_pos hlt] at h
    cases hraw : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut
        (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) with
    | none =>
      rw [hraw] at h
      simp at h
    | some rawIn =>
      rw [hraw] at h
      simp only at h
      exact ⟨hlt, rawIn, _, hraw, rfl, h⟩
  · rw [if_neg hlt] at h
    cases h

theorem netUp_le_netInDown {amt fee rate net : Nat}
    (hsub : subtractSwapFeeAmount amt fee = some net) :
    net * rate / ONE ≤ amt * (ONE - fee) * rate / (ONE * ONE) := by
  have hadd : net + mulUp amt fee = amt := subFee_add hsub
  have eMul : mulUp amt fee = ProofForgeFin.ceilDiv (amt * fee) ONE := mulUp_eq_ceil _ _
  have e1 : amt * fee ≤ mulUp amt fee * ONE := by
    rw [eMul]; exact ProofForgeFin.le_ceilDiv_mul _ _ hONE
  have eN : net * ONE + mulUp amt fee * ONE = amt * ONE := by
    rw [← Nat.add_mul, hadd]
  have eE : amt * (ONE - fee) = amt * ONE - amt * fee := Nat.mul_sub _ _ _
  have hnet : net * ONE ≤ amt * (ONE - fee) := by omega
  have step1 : (net * ONE) * (rate * ONE) ≤ (amt * (ONE - fee)) * (rate * ONE) :=
    Nat.mul_le_mul hnet (Nat.le_refl _)
  have eL : (net * ONE) * (rate * ONE) = net * rate * (ONE * ONE) := by
    rw [Nat.mul_assoc net ONE (rate * ONE), ← Nat.mul_assoc ONE rate ONE,
      Nat.mul_comm ONE rate, Nat.mul_assoc rate ONE ONE,
      ← Nat.mul_assoc net rate (ONE * ONE)]
  have eR : (amt * (ONE - fee)) * (rate * ONE) = amt * (ONE - fee) * rate * ONE := by
    rw [← Nat.mul_assoc]
  rw [eL, eR] at step1
  exact ProofForgeFin.div_le_div_of_mul_le hONE (Nat.mul_pos hONE hONE) step1

theorem strict_mul_right {a b k : Nat} (hk : 0 < k) (h : a < b) : a * k < b * k := by
  have h2 : a + 1 ≤ b := h
  have h3 : (a + 1) * k ≤ b * k := Nat.mul_le_mul h2 (Nat.le_refl k)
  have e : (a + 1) * k = a * k + k := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem charge_lower {price rin comp rawIn c : Nat}
    (eA : price * ONE ≤ rawIn * rin) (eB : rawIn * ONE ≤ c * comp) :
    ONE * ONE * price ≤ c * comp * rin := by
  have h1 : price * ONE * ONE ≤ rawIn * rin * ONE :=
    Nat.mul_le_mul eA (Nat.le_refl _)
  have h2 : (rawIn * ONE) * rin ≤ (c * comp) * rin :=
    Nat.mul_le_mul eB (Nat.le_refl _)
  have eR : rawIn * rin * ONE = (rawIn * ONE) * rin := by
    rw [Nat.mul_assoc rawIn rin ONE, Nat.mul_comm rin ONE,
      ← Nat.mul_assoc rawIn ONE rin]
  have eL1 : price * ONE * ONE = ONE * ONE * price := by
    rw [Nat.mul_assoc price ONE ONE, Nat.mul_comm price (ONE * ONE)]
  have h3 : rawIn * rin * ONE ≤ c * comp * rin := by rw [eR]; exact h2
  have h4 : ONE * ONE * price ≤ rawIn * rin * ONE := by rw [← eL1]; exact h1
  exact Nat.le_trans h4 h3

theorem charge_upper {price rin comp rawIn c : Nat} (hrin : 0 < rin)
    (hD : rawIn * rin < price * ONE + rin)
    (hC : c * comp < rawIn * ONE + comp) :
    (c - 1) * comp * rin < ONE * (ONE * price + rin) := by
  by_cases hc : c = 0
  · subst hc
    simp only [Nat.zero_sub, Nat.zero_mul]
    have hpos : 0 < ONE * price + rin := by
      have h := hrin
      omega
    exact Nat.mul_pos hONE hpos
  · have h1c : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc
    have hge : comp ≤ c * comp := by
      calc comp = comp * 1 := (Nat.mul_one comp).symm
        _ ≤ comp * c := Nat.mul_le_mul (Nat.le_refl comp) h1c
        _ = c * comp := Nat.mul_comm _ _
    have eSub : (c - 1) * comp = c * comp - comp := by
      rw [Nat.sub_mul, Nat.one_mul]
    have eS : (c - 1) * comp + comp = c * comp := by
      rw [eSub]; exact Nat.sub_add_cancel hge
    have hX : (c - 1) * comp < rawIn * ONE := by omega
    have hC3 : (c - 1) * comp * rin < (rawIn * ONE) * rin :=
      strict_mul_right hrin hX
    have hF1 : (rawIn * rin) * ONE < (price * ONE + rin) * ONE :=
      strict_mul_right hONE hD
    have eR1 : (rawIn * ONE) * rin = (rawIn * rin) * ONE := by
      rw [Nat.mul_assoc rawIn ONE rin, Nat.mul_comm ONE rin,
        ← Nat.mul_assoc rawIn rin ONE]
    have eFin : (price * ONE + rin) * ONE = ONE * (ONE * price + rin) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_assoc price ONE ONE,
        ← Nat.mul_assoc ONE ONE price, Nat.mul_comm (ONE * ONE) price,
        Nat.mul_comm rin ONE]
    rw [eR1] at hC3
    rw [eFin] at hF1
    exact Nat.lt_trans hC3 hF1

theorem netLess_le_netUp {amt fee rate net : Nat}
    (hsub : subtractSwapFeeAmount amt fee = some net) :
    (amt * (ONE - fee) - ONE) * rate / (ONE * ONE) ≤ net * rate / ONE := by
  have hadd : net + mulUp amt fee = amt := subFee_add hsub
  have eMul : mulUp amt fee = ProofForgeFin.ceilDiv (amt * fee) ONE := mulUp_eq_ceil _ _
  have e2 : mulUp amt fee * ONE < amt * fee + ONE := by
    rw [eMul]; exact ProofForgeFin.ceilDiv_mul_lt _ _ hONE
  have eN : net * ONE + mulUp amt fee * ONE = amt * ONE := by
    rw [← Nat.add_mul, hadd]
  have eE : amt * (ONE - fee) = amt * ONE - amt * fee := Nat.mul_sub _ _ _
  have hlow : amt * (ONE - fee) - ONE ≤ net * ONE := by omega
  have step1 : ((amt * (ONE - fee) - ONE)) * (rate * ONE) ≤ (net * ONE) * (rate * ONE) :=
    Nat.mul_le_mul hlow (Nat.le_refl _)
  have eL : ((amt * (ONE - fee) - ONE)) * (rate * ONE)
      = (amt * (ONE - fee) - ONE) * rate * ONE := by
    rw [← Nat.mul_assoc]
  have eR : (net * ONE) * (rate * ONE) = net * rate * (ONE * ONE) := by
    rw [Nat.mul_assoc net ONE (rate * ONE), ← Nat.mul_assoc ONE rate ONE,
      Nat.mul_comm ONE rate, Nat.mul_assoc rate ONE ONE,
      ← Nat.mul_assoc net rate (ONE * ONE)]
  rw [eL, eR] at step1
  exact ProofForgeFin.div_le_div_of_mul_le (Nat.mul_pos hONE hONE) hONE step1

theorem req_given_in_succeeds        : GivenInSucceeds onSwap := by
  intro m p s hw hkind hv hrate hfee
  have hvcopy := hv
  obtain ⟨hne, hin, hout⟩ := hv
  have hsub : subtractSwapFeeAmount s.amount p.fee = some (s.amount - mulUp s.amount p.fee) := by
    unfold subtractSwapFeeAmount
    rw [if_pos (feeUp_le hfee)]
  have hdown : downscaleDown (m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) (p.rate s.tokenOut) = some ((m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE / p.rate s.tokenOut) := by
    unfold downscaleDown
    exact divDown_is_some (Nat.pos_iff_ne_zero.mp hrate)
  have hgin : swapGivenIn m p s = some ((m.outGivenIn (upscaleArray p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE / p.rate s.tokenOut) := by
    unfold swapGivenIn
    rw [hsub]
    simp only
    exact hdown
  have hq : onSwap m p s = some ((m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE / p.rate s.tokenOut) := by
    rw [onSwap_givenIn _ _ _ hkind, hgin, upscaleArray_eq]
  have hpx_le := (hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn)) hne hin hout).1
  have hle : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE / p.rate s.tokenOut ≤ p.balance s.tokenOut := by
    have e1 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE / p.rate s.tokenOut * p.rate s.tokenOut ≤ (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE := Nat.div_mul_le_self _ _
    have e2 : scaledBalances p s.tokenOut * ONE ≤ p.balance s.tokenOut * p.rate s.tokenOut := by
      unfold scaledBalances scaleDown
      exact Nat.div_mul_le_self _ _
    have e3 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE ≤ scaledBalances p s.tokenOut * ONE := Nat.mul_le_mul hpx_le (Nat.le_refl _)
    have e4 : (m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale (s.amount - mulUp s.amount p.fee) (p.rate s.tokenIn))) * ONE / p.rate s.tokenOut * p.rate s.tokenOut ≤ p.balance s.tokenOut * p.rate s.tokenOut := Nat.le_trans (Nat.le_trans e1 e3) e2
    exact Nat.le_of_mul_le_mul_right e4 hrate
  unfold step
  rw [if_pos hvcopy, hq]
  simp only [settle, amountOut_givenIn _ hkind, amountIn_givenIn _ hkind]
  rw [if_pos hle]
  rfl
theorem req_given_out_succeeds       : GivenOutSucceeds onSwap := by
  intro m p s hw hkind hv hrin hfee hlt
  have hvcopy := hv
  obtain ⟨hne, hin, hout⟩ := hv
  have hcond : upscaleUp s.amount (p.rate s.tokenOut) < upscaleArray p s.tokenOut := hlt
  have hraw : downscaleUp (m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (upscaleUp s.amount (p.rate s.tokenOut))) (p.rate s.tokenIn) = some (ProofForgeFin.ceilDiv ((m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (upscaleUp s.amount (p.rate s.tokenOut))) * ONE) (p.rate s.tokenIn)) := by
    unfold downscaleUp
    exact divUp_is_some (Nat.pos_iff_ne_zero.mp hrin)
  have hcomp : complement p.fee = ONE - p.fee := complement_of_lt hfee
  have hcompne : ONE - p.fee ≠ 0 := by
    have h1 := hfee
    have h2 := hONE
    omega
  have hadd : addSwapFeeAmount (ProofForgeFin.ceilDiv ((m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (upscaleUp s.amount (p.rate s.tokenOut))) * ONE) (p.rate s.tokenIn)) p.fee = some (ProofForgeFin.ceilDiv ((ProofForgeFin.ceilDiv ((m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (upscaleUp s.amount (p.rate s.tokenOut))) * ONE) (p.rate s.tokenIn)) * ONE) (ONE - p.fee)) := by
    unfold addSwapFeeAmount
    rw [hcomp]
    exact divUp_is_some hcompne
  have hgout : swapGivenOut m p s = some (ProofForgeFin.ceilDiv ((ProofForgeFin.ceilDiv ((m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (upscaleUp s.amount (p.rate s.tokenOut))) * ONE) (p.rate s.tokenIn)) * ONE) (ONE - p.fee)) := by
    unfold swapGivenOut
    rw [if_pos hcond, hraw]
    simp only
    exact hadd
  have hq : onSwap m p s = some (ProofForgeFin.ceilDiv ((ProofForgeFin.ceilDiv ((m.inGivenOut (upscaleArray p) s.tokenIn s.tokenOut (upscaleUp s.amount (p.rate s.tokenOut))) * ONE) (p.rate s.tokenIn)) * ONE) (ONE - p.fee)) := by
    rw [onSwap_givenOut _ _ _ hkind]
    exact hgout
  have hrout : 0 < p.rate s.tokenOut := by
    by_cases hr : p.rate s.tokenOut = 0
    · rw [hr] at hlt
      have h1 : scaleUp s.amount 0 = 0 := by
        unfold scaleUp
        rw [Nat.mul_zero, Nat.zero_add]
        exact Nat.div_eq_of_lt (by have h := hONE; omega)
      have h2 : scaleDown (p.balance s.tokenOut) 0 = 0 := by
        unfold scaleDown
        rw [Nat.mul_zero]
        exact Nat.div_eq_of_lt hONE
      rw [h1, h2] at hlt
      omega
    · exact Nat.pos_of_ne_zero hr
  have hle_amt : s.amount ≤ p.balance s.tokenOut := by
    by_cases ha : s.amount ≤ p.balance s.tokenOut
    · exact ha
    · have hcon : p.balance s.tokenOut < s.amount := Nat.not_le.mp ha
      have hXY : p.balance s.tokenOut * p.rate s.tokenOut < s.amount * p.rate s.tokenOut :=
        strict_mul_right hrout hcon
      have hfloor_ceil : p.balance s.tokenOut * p.rate s.tokenOut / ONE < ProofForgeFin.ceilDiv (s.amount * p.rate s.tokenOut) ONE := by
        rw [ProofForgeFin.lt_ceilDiv_iff hONE]
        exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hXY
      have hlt2 : ProofForgeFin.ceilDiv (s.amount * p.rate s.tokenOut) ONE < p.balance s.tokenOut * p.rate s.tokenOut / ONE := by
        have e1 : scaleUp s.amount (p.rate s.tokenOut) = ProofForgeFin.ceilDiv (s.amount * p.rate s.tokenOut) ONE := by
          rw [← upscaleUp_eq_scaleUp]
          exact upscaleUp_eq_ceil _ _
        have e2 : scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
        rw [e1, e2] at hlt
        exact hlt
      omega
  unfold step
  rw [if_pos hvcopy, hq]
  simp only [settle, amountOut_givenOut _ hkind, amountIn_givenOut _ hkind]
  rw [if_pos hle_amt]
  rfl
theorem req_given_in_pays_at_most    : GivenInPaysAtMost onSwap := by
  intro m p s y hmono hkind hv hq
  rw [onSwap_givenIn _ _ _ hkind] at hq
  obtain ⟨net, px, hsub, hpx, hdown⟩ := givenIn_pack hq
  rw [upscaleArray_eq] at hpx
  unfold downscaleDown at hdown
  by_cases hrout : p.rate s.tokenOut = 0
  · rw [hrout] at hdown
    unfold divDown at hdown
    simp at hdown
  · have hroutpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrout
    have heq : px * ONE / p.rate s.tokenOut = y := divDown_some_eq hrout hdown
    have e1 : y * p.rate s.tokenOut ≤ px * ONE := by
      rw [← heq]
      exact Nat.div_mul_le_self _ _
    have hle : px ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) := by
      rw [hpx]
      exact hmono.1 _ _ _ _ _ (netUp_le_netInDown hsub)
    have e2 : px * ONE ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
      Nat.mul_le_mul hle (Nat.le_refl _)
    calc y * p.rate s.tokenOut ≤ m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) * ONE :=
          Nat.le_trans e1 e2
      _ = ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s) :=
          Nat.mul_comm _ _

theorem req_given_in_pays_at_least   : GivenInPaysAtLeast onSwap := by
  intro m p s y hmono hkind hv hq
  rw [onSwap_givenIn _ _ _ hkind] at hq
  obtain ⟨net, px, hsub, hpx, hdown⟩ := givenIn_pack hq
  rw [upscaleArray_eq] at hpx
  unfold downscaleDown at hdown
  by_cases hrout : p.rate s.tokenOut = 0
  · rw [hrout] at hdown
    unfold divDown at hdown
    simp at hdown
  · have hroutpos : 0 < p.rate s.tokenOut := Nat.pos_of_ne_zero hrout
    have heq : px * ONE / p.rate s.tokenOut = y := divDown_some_eq hrout hdown
    have hlow : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) ≤ px := by
      rw [hpx]
      exact hmono.1 _ _ _ _ _ (netLess_le_netUp hsub)
    have e1 : px * ONE < (y + 1) * p.rate s.tokenOut := by
      rw [← heq]
      exact ProofForgeFin.lt_div_add_one_mul _ _ hroutpos
    have e2 : m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) * ONE < (y + 1) * p.rate s.tokenOut :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul hlow (Nat.le_refl _)) e1
    calc ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s)
          = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) * ONE :=
          Nat.mul_comm _ _
      _ < (y + 1) * p.rate s.tokenOut := e2
theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := by
  intro m p s c hmono hkind hv hq
  rw [onSwap_givenOut _ _ _ hkind] at hq
  obtain ⟨hlt, rawIn, px, hraw, hpx, hadd⟩ := givenOut_pack hq
  rw [upscaleArray_eq, upscaleUp_eq_scaleUp] at hpx
  unfold downscaleUp at hraw
  unfold addSwapFeeAmount at hadd
  by_cases hrin : p.rate s.tokenIn = 0
  · rw [hrin] at hraw
    unfold divUp at hraw
    simp at hraw
  · have eA0 : ProofForgeFin.ceilDiv (px * ONE) (p.rate s.tokenIn) = rawIn :=
      divUp_some_eq hrin hraw
    have eA : px * ONE ≤ rawIn * p.rate s.tokenIn := by
      rw [← eA0]
      exact ProofForgeFin.le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hrin)
    by_cases hfee : p.fee < ONE
    · have hcomp : complement p.fee = ONE - p.fee := complement_of_lt hfee
      have hcompne : ONE - p.fee ≠ 0 := by
        have h1 := hfee
        have h2 := hONE
        omega
      rw [hcomp] at hadd
      have eB0 : ProofForgeFin.ceilDiv (rawIn * ONE) (ONE - p.fee) = c :=
        divUp_some_eq hcompne hadd
      have eB : rawIn * ONE ≤ c * (ONE - p.fee) := by
        rw [← eB0]
        exact ProofForgeFin.le_ceilDiv_mul _ _ (by have h1 := hfee; have h2 := hONE; omega)
      unfold outPrice
      rw [← hpx]
      exact charge_lower eA eB
    · rw [complement_of_ge hfee] at hadd
      unfold divUp at hadd
      simp at hadd

theorem req_given_out_charges_at_most  : GivenOutChargesAtMost onSwap := by
  intro m p s c hmono hkind hv hq
  rw [onSwap_givenOut _ _ _ hkind] at hq
  obtain ⟨hlt, rawIn, px, hraw, hpx, hadd⟩ := givenOut_pack hq
  rw [upscaleArray_eq, upscaleUp_eq_scaleUp] at hpx
  unfold downscaleUp at hraw
  unfold addSwapFeeAmount at hadd
  by_cases hrin : p.rate s.tokenIn = 0
  · rw [hrin] at hraw
    unfold divUp at hraw
    simp at hraw
  · have hrinpos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrin
    have eA0 : ProofForgeFin.ceilDiv (px * ONE) (p.rate s.tokenIn) = rawIn :=
      divUp_some_eq hrin hraw
    by_cases hfee : p.fee < ONE
    · have hcomp : complement p.fee = ONE - p.fee := complement_of_lt hfee
      have hcompne : ONE - p.fee ≠ 0 := by
        have h1 := hfee
        have h2 := hONE
        omega
      have hcomppos : 0 < ONE - p.fee := by
        have h1 := hfee
        have h2 := hONE
        omega
      rw [hcomp] at hadd
      have eB0 : ProofForgeFin.ceilDiv (rawIn * ONE) (ONE - p.fee) = c :=
        divUp_some_eq hcompne hadd
      have hD : rawIn * p.rate s.tokenIn < px * ONE + p.rate s.tokenIn := by
        have hceil := ProofForgeFin.ceilDiv_mul_lt (px * ONE) (p.rate s.tokenIn) hrinpos
        rw [eA0] at hceil
        exact hceil
      have hC : c * (ONE - p.fee) < rawIn * ONE + (ONE - p.fee) := by
        have hceil := ProofForgeFin.ceilDiv_mul_lt (rawIn * ONE) (ONE - p.fee) hcomppos
        rw [eB0] at hceil
        exact hceil
      unfold outPrice
      rw [← hpx]
      exact charge_upper hrinpos hD hC
    · rw [complement_of_ge hfee] at hadd
      unfold divUp at hadd
      simp at hadd
theorem req_swap_keeps_value         : SwapKeepsValue onSwap := by
  intro m p s p' hw hstep
  obtain ⟨hv, q, hq, hsettle⟩ := step_pack hstep
  obtain ⟨hne, hin, hout⟩ := hv
  obtain ⟨hle, hbal, hn, hrate_eq, hfee_eq⟩ := settle_pack hsettle
  cases hkind : s.kind with
  | givenIn =>
    rw [onSwap_givenIn _ _ _ hkind] at hq
    obtain ⟨net, px, hsub, hpx, hdown⟩ := givenIn_pack hq
    rw [upscaleArray_eq] at hpx
    rw [amountIn_givenIn _ hkind, amountOut_givenIn _ hkind] at hbal
    unfold downscaleDown at hdown
    by_cases hrout : p.rate s.tokenOut = 0
    · rw [hrout] at hdown
      unfold divDown at hdown
      simp at hdown
    · have heq : px * ONE / p.rate s.tokenOut = q := divDown_some_eq hrout hdown
      have hadd : net + mulUp s.amount p.fee = s.amount := subFee_add hsub
      have hnet_le : net ≤ s.amount := by omega
      have eyr : q * p.rate s.tokenOut ≤ px * ONE := by
        rw [← heq]
        exact Nat.div_mul_le_self _ _
      have hbi : scaledBalances p s.tokenIn + upscale net (p.rate s.tokenIn) ≤ scaledBalances p' s.tokenIn := by
        have e1 : scaledBalances p s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
        have e2 : scaledBalances p' s.tokenIn = (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn / ONE := by
          simp only [scaledBalances, scaleDown, hbal, hrate_eq, update2_self]
        have e3 : upscale net (p.rate s.tokenIn) = net * p.rate s.tokenIn / ONE := rfl
        rw [e1, e2, e3]
        have eUV : (p.balance s.tokenIn + s.amount) * p.rate s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn + s.amount * p.rate s.tokenIn := Nat.add_mul _ _ _
        rw [eUV]
        exact add_floor_ge (Nat.mul_le_mul hnet_le (Nat.le_refl _))
      have hbj : scaledBalances p s.tokenOut - px ≤ scaledBalances p' s.tokenOut := by
        have e1 : scaledBalances p s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
        have e2 : scaledBalances p' s.tokenOut = (p.balance s.tokenOut - q) * p.rate s.tokenOut / ONE := by
          simp only [scaledBalances, scaleDown, hbal, hrate_eq, update2_other (Ne.symm hne)]
        rw [e1, e2]
        exact sub_floor_ge eyr hONE
      have hsound := (hw.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (upscale net (p.rate s.tokenIn)) hne hin hout).2
      rw [← hpx] at hsound
      have hmid_le : ∀ k, k < p.n → update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + upscale net (p.rate s.tokenIn)) s.tokenOut (scaledBalances p s.tokenOut - px) k ≤ scaledBalances p' k := by
        intro k hk
        by_cases hi : k = s.tokenIn
        · subst hi
          rw [update2_self]
          exact hbi
        · by_cases hj : k = s.tokenOut
          · subst hj
            rw [update2_other (Ne.symm hne)]
            exact hbj
          · rw [update2_ne hi hj]
            have e : scaledBalances p' k = scaledBalances p k := by
              simp only [scaledBalances, scaleDown, hbal, hrate_eq, update2_ne hi hj]
            rw [e]
            exact Nat.le_refl _
      have hval : value m p ≤ value m p' := by
        unfold value
        exact Nat.le_trans hsound (hw.monotone _ _ hmid_le)
      exact hval
  | givenOut =>
    rw [onSwap_givenOut _ _ _ hkind] at hq
    obtain ⟨hlt, rawIn, px, hraw, hpx, hadd⟩ := givenOut_pack hq
    rw [upscaleArray_eq, upscaleUp_eq_ceil] at hpx hlt
    rw [amountIn_givenOut _ hkind, amountOut_givenOut _ hkind] at hbal
    unfold downscaleUp at hraw
    unfold addSwapFeeAmount at hadd
    by_cases hrin : p.rate s.tokenIn = 0
    · rw [hrin] at hraw
      unfold divUp at hraw
      simp at hraw
    · have hrinpos : 0 < p.rate s.tokenIn := Nat.pos_of_ne_zero hrin
      have eA0 : ProofForgeFin.ceilDiv (px * ONE) (p.rate s.tokenIn) = rawIn := divUp_some_eq hrin hraw
      have eA : px * ONE ≤ rawIn * p.rate s.tokenIn := by
        rw [← eA0]
        exact ProofForgeFin.le_ceilDiv_mul _ _ hrinpos
      by_cases hfee : p.fee < ONE
      · have hcomp : complement p.fee = ONE - p.fee := complement_of_lt hfee
        have hcompne : ONE - p.fee ≠ 0 := by have h1 := hfee; have h2 := hONE; omega
        have hcomppos : 0 < ONE - p.fee := by have h1 := hfee; have h2 := hONE; omega
        rw [hcomp] at hadd
        have eB0 : ProofForgeFin.ceilDiv (rawIn * ONE) (ONE - p.fee) = q := divUp_some_eq hcompne hadd
        have eB : rawIn * ONE ≤ q * (ONE - p.fee) := by
          rw [← eB0]
          exact ProofForgeFin.le_ceilDiv_mul _ _ hcomppos
        have hcomp_le : ONE - p.fee ≤ ONE := Nat.sub_le _ _
        have hbi : scaledBalances p s.tokenIn + px ≤ scaledBalances p' s.tokenIn := by
          have e1 : scaledBalances p s.tokenIn = p.balance s.tokenIn * p.rate s.tokenIn / ONE := rfl
          have e2 : scaledBalances p' s.tokenIn = (p.balance s.tokenIn + q) * p.rate s.tokenIn / ONE := by
            simp only [scaledBalances, scaleDown, hbal, hrate_eq, update2_self]
          rw [e1, e2]
          exact outIn_ge eA eB hcomp_le
        have hbj : scaledBalances p s.tokenOut - ProofForgeFin.ceilDiv (s.amount * p.rate s.tokenOut) ONE ≤ scaledBalances p' s.tokenOut := by
          have e1 : scaledBalances p s.tokenOut = p.balance s.tokenOut * p.rate s.tokenOut / ONE := rfl
          have e2 : scaledBalances p' s.tokenOut = (p.balance s.tokenOut - s.amount) * p.rate s.tokenOut / ONE := by
            simp only [scaledBalances, scaleDown, hbal, hrate_eq, update2_other (Ne.symm hne)]
          rw [e1, e2]
          exact outOut_floor_ge
        have hsound := hw.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (ProofForgeFin.ceilDiv (s.amount * p.rate s.tokenOut) ONE) hne hin hout hlt
        rw [← hpx] at hsound
        have hmid_le : ∀ k, k < p.n → update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + px) s.tokenOut (scaledBalances p s.tokenOut - ProofForgeFin.ceilDiv (s.amount * p.rate s.tokenOut) ONE) k ≤ scaledBalances p' k := by
          intro k hk
          by_cases hi : k = s.tokenIn
          · subst hi
            rw [update2_self]
            exact hbi
          · by_cases hj : k = s.tokenOut
            · subst hj
              rw [update2_other (Ne.symm hne)]
              exact hbj
            · rw [update2_ne hi hj]
              have e : scaledBalances p' k = scaledBalances p k := by
                simp only [scaledBalances, scaleDown, hbal, hrate_eq, update2_ne hi hj]
              rw [e]
              exact Nat.le_refl _
        have hval : value m p ≤ value m p' := by
          unfold value
          exact Nat.le_trans hsound (hw.monotone _ _ hmid_le)
        exact hval
      · rw [complement_of_ge hfee] at hadd
        unfold divUp at hadd
        simp at hadd

theorem req_batch_keeps_value        : BatchKeepsValue onSwap := by
  intro m p ss p' hw h
  induction ss generalizing p p' with
  | nil =>
    simp only [run] at h
    cases h
    exact Nat.le_refl _
  | cons s ss ih =>
    unfold run at h
    cases hstep : step onSwap m p s with
    | none =>
      rw [hstep] at h
      simp at h
    | some mid =>
      rw [hstep] at h
      simp only at h
      have h1 : value m p ≤ value m mid := req_swap_keeps_value m p s mid hw hstep
      obtain ⟨hv_mid, q_mid, hq_mid, hsettle_mid⟩ := step_pack hstep
      obtain ⟨hle_mid, hbal_mid, hn_mid, hrate_mid, hfee_mid⟩ := settle_pack hsettle_mid
      have hw' : WellBehaved m mid.n := by rw [hn_mid]; exact hw
      have h2 : value m mid ≤ value m p' := ih mid p' hw' h
      exact Nat.le_trans h1 h2

end BalancerSwap

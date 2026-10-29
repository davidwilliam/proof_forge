import BalancerSwap.Spec
/-!
# The requirements are not vacuous (protected, proved)

The value requirements assume the pool math is well behaved, and the price requirements assume
its prices are monotone. Both assumptions are met by a real pool formula:
`constantProduct_wellBehaved` and `constantProduct_priceMonotone` prove them for the
two-token constant-product pool `constantProduct`.

The requirements also fix what an implementation must do. `exploit_swap_charge` takes the
state of the Balancer osETH/WETH pool before each exploit swap of the November 2025 attack:
374,353 wei of WETH (token 0, scaling factor 1e18) and 18 wei of osETH (token 1, scaling
factor 1058132408689971699, its rate), with the pool's 0.01% fee. The attacker asks for 17 wei
of osETH out. With the constant-product math, every implementation that meets
REQ-GIVEN-OUT-SUCCEEDS, REQ-GIVEN-OUT-CHARGES-AT-LEAST and REQ-GIVEN-OUT-CHARGES-AT-MOST
accepts the swap and charges 6,739,028 or 6,739,029 wei of WETH. The exact amount out is
17.988 osETH units of 1e-18; rounded up to 18 of the pool's 19 units, the math prices it at
6,738,354 before the fee. (The port of Balancer's code rounds the amount out down to 17 and
charges 3,182,320; see `witnesses/attack_batch.lean`.)
-/

namespace BalancerSwap

/-! ## The constant-product pool is well behaved -/

theorem cp_out_le (bi bj x : Nat) : bj * x / (bi + x) ≤ bj := by
  apply Nat.div_le_of_le_mul
  rw [Nat.add_mul, Nat.mul_comm bj x]
  exact Nat.le_add_left _ _

theorem cp_out_sound (bi bj x : Nat) : bi * bj ≤ (bi + x) * (bj - bj * x / (bi + x)) := by
  have h1 : bj * x / (bi + x) * (bi + x) ≤ bj * x := Nat.div_mul_le_self _ _
  have h2 : (bi + x) * (bj * x / (bi + x)) ≤ x * bj := by
    rw [Nat.mul_comm, Nat.mul_comm x]; exact h1
  rw [Nat.mul_sub, Nat.add_mul]
  omega

theorem ceil_ge (a d : Nat) (hd : 0 < d) : a ≤ (a + (d - 1)) / d * d := by
  have h1 := Nat.div_add_mod (a + (d - 1)) d
  have h2 := Nat.mod_lt (a + (d - 1)) hd
  rw [Nat.mul_comm]
  omega

theorem ceil_le {a d q : Nat} (hd : 0 < d) (h : a ≤ q * d) : (a + (d - 1)) / d ≤ q := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hd).2
  rw [Nat.succ_mul]
  omega

theorem cp_in_sound (bi bj x : Nat) (hx : x < bj) :
    bi * bj ≤ (bi + (bi * x + (bj - x - 1)) / (bj - x)) * (bj - x) := by
  have hd : 0 < bj - x := by omega
  have h1 := ceil_ge (bi * x) (bj - x) hd
  have h2 : bi * x ≤ bi * bj := Nat.mul_le_mul_left bi (Nat.le_of_lt hx)
  have h3 : bj - x - 1 = bj - x - 1 := rfl
  rw [Nat.add_mul, Nat.mul_sub]
  omega

theorem constantProduct_wellBehaved : WellBehaved constantProduct 2 where
  monotone := by
    intro b b' h
    exact Nat.mul_le_mul (h 0 (by decide)) (h 1 (by decide))
  outGivenIn := by
    intro b i j x hij hi hj
    show b j * x / (b i + x) ≤ b j ∧ b 0 * b 1 ≤ _
    refine ⟨cp_out_le _ _ _, ?_⟩
    have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show b 0 * b 1 ≤ (b 0 + x) * (b 1 - b 1 * x / (b 0 + x))
      exact cp_out_sound _ _ _
    · show b 0 * b 1 ≤ (b 0 - b 0 * x / (b 1 + x)) * (b 1 + x)
      rw [Nat.mul_comm (b 0), Nat.mul_comm (b 0 - _)]
      exact cp_out_sound _ _ _
  inGivenOut := by
    intro b i j x hij hi hj hx
    show b 0 * b 1 ≤ _
    have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show b 0 * b 1 ≤ (b 0 + (if x < b 1 then (b 0 * x + (b 1 - x - 1)) / (b 1 - x) else b 0 * x)) *
        (b 1 - x)
      rw [ite_eq_left hx]
      exact cp_in_sound _ _ _ hx
    · show b 0 * b 1 ≤ (b 0 - x) *
        (b 1 + (if x < b 0 then (b 1 * x + (b 0 - x - 1)) / (b 0 - x) else b 1 * x))
      rw [ite_eq_left hx, Nat.mul_comm (b 0), Nat.mul_comm (b 0 - x)]
      exact cp_in_sound _ _ _ hx

/-! ## Its prices are monotone -/

theorem cp_out_mono (bi bj x y : Nat) (hxy : x ≤ y) : bj * x / (bi + x) ≤ bj * y / (bi + y) := by
  rcases Nat.eq_zero_or_pos (bi + y) with h0 | hpos
  · have : x = 0 := by omega
    subst this
    simp
  · apply (Nat.le_div_iff_mul_le hpos).2
    have h1 : bj * x / (bi + x) * (bi + x) ≤ bj * x := Nat.div_mul_le_self _ _
    have h2 : bj * x / (bi + x) * (y - x) ≤ bj * (y - x) := Nat.mul_le_mul_right _ (cp_out_le bi bj x)
    have e : bi + y = (bi + x) + (y - x) := by omega
    rw [e, Nat.mul_add]
    have e2 : bj * y = bj * x + bj * (y - x) := by rw [← Nat.mul_add]; congr 1; omega
    rw [e2]
    exact Nat.add_le_add h1 h2

theorem cp_in_mono (bi bj x y : Nat) (hxy : x ≤ y) :
    (if x < bj then (bi * x + (bj - x - 1)) / (bj - x) else bi * x) ≤
      (if y < bj then (bi * y + (bj - y - 1)) / (bj - y) else bi * y) := by
  by_cases hy : y < bj
  · have hx : x < bj := by omega
    rw [ite_eq_left hx, ite_eq_left hy]
    apply ceil_le (by omega)
    have h1 := ceil_ge (bi * y) (bj - y) (by omega)
    have h2 : bi * x ≤ bi * y := Nat.mul_le_mul_left bi hxy
    have h3 : (bi * y + (bj - y - 1)) / (bj - y) * (bj - y) ≤
        (bi * y + (bj - y - 1)) / (bj - y) * (bj - x) := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [ite_eq_right hy]
    have h2 : bi * x ≤ bi * y := Nat.mul_le_mul_left bi hxy
    by_cases hx : x < bj
    · rw [ite_eq_left hx]
      have : (bi * x + (bj - x - 1)) / (bj - x) ≤ bi * x := by
        apply ceil_le (by omega)
        exact Nat.le_mul_of_pos_right _ (by omega)
      omega
    · rw [ite_eq_right hx]; exact h2

theorem constantProduct_priceMonotone : PriceMonotone constantProduct := by
  refine ⟨?_, ?_⟩
  · intro b i j x y hxy
    exact cp_out_mono (b i) (b j) x y hxy
  · intro b i j x y hxy
    exact cp_in_mono (b i) (b j) x y hxy

/-! ## The requirements pin the charge of the exploit swap -/

/-- The osETH/WETH pool before each exploit swap of the attack: 374,353 wei of WETH and 18 wei
of osETH (the balances before the second swap of the first round). -/
def attackPool : Pool where
  n := 2
  balance k := if k = 0 then 374353 else if k = 1 then 18 else 0
  rate k := if k = 1 then 1058132408689971699 else ONE
  fee := 100000000000000

/-- 17 wei of osETH out, paid in WETH. -/
def exploitSwap : Swap := { kind := .givenOut, tokenIn := 0, tokenOut := 1, amount := 17 }

theorem exploit_outPrice : outPrice constantProduct attackPool exploitSwap = 6738354 := by decide

theorem exploit_swap_charge (impl : Impl) (h1 : GivenOutSucceeds impl)
    (h2 : GivenOutChargesAtLeast impl) (h3 : GivenOutChargesAtMost impl) :
    ∃ c, impl constantProduct attackPool exploitSwap = some c ∧ (c = 6739028 ∨ c = 6739029) := by
  have hv : Valid attackPool exploitSwap := by decide
  have hs := h1 constantProduct attackPool exploitSwap constantProduct_wellBehaved rfl hv
    (by decide) (by decide) (by decide)
  unfold step at hs
  rw [ite_eq_left hv] at hs
  split at hs
  · rename_i c hc
    refine ⟨c, hc, ?_⟩
    have a := h2 _ _ _ c constantProduct_priceMonotone rfl hv hc
    have b := h3 _ _ _ c constantProduct_priceMonotone rfl hv hc
    rw [exploit_outPrice] at a b
    have e1 : attackPool.fee = 100000000000000 := rfl
    have e2 : attackPool.rate exploitSwap.tokenIn = ONE := rfl
    rw [e1, e2] at a b
    unfold ONE at a b
    omega
  · simp at hs

end BalancerSwap

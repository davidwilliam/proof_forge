import OzSqrt.Spec
import OzSqrt.Lemmas
/-!
The square-root routine under repair, `Math.sqrt(uint256 a)` in the style of OpenZeppelin
Contracts `Math.sol`, as this pool's first deposit calls it:

```
function sqrt(uint256 a) internal pure returns (uint256) {
    if (a == 0) {
        return 0;
    }
    uint256 result = 1 << (log2(a) >> 1);
    unchecked {
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        return min(result, a / result);
    }
}
```
-/
namespace OzSqrt

def sqrt : SqrtFn := fun a =>
  if a = 0 then 0
  else
    let result : U256 := (1 : U256) <<< (log2 a >>> 1)
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    min result (a / result)

/-- The final `min` of the routine never exceeds the floor root: pure Nat fact. -/
theorem min_sq_le (a r : U256) :
    (min r (a / r)).toNat * (min r (a / r)).toNat ≤ a.toNat := by
  rw [toNat_min, BitVec.toNat_udiv]
  by_cases hr : r.toNat = 0
  · have hm : Nat.min r.toNat (a.toNat / r.toNat) = 0 := by simp [hr]
    rw [hm]; simp
  · have h1 : Nat.min r.toNat (a.toNat / r.toNat) ≤ r.toNat := Nat.min_le_left _ _
    have h2 : Nat.min r.toNat (a.toNat / r.toNat) ≤ a.toNat / r.toNat := Nat.min_le_right _ _
    have h3 : Nat.min r.toNat (a.toNat / r.toNat) * Nat.min r.toNat (a.toNat / r.toNat)
        ≤ r.toNat * (a.toNat / r.toNat) := Nat.mul_le_mul h1 h2
    have h4 : r.toNat * (a.toNat / r.toNat) ≤ a.toNat := by
      have hdm := Nat.div_add_mod a.toNat r.toNat
      omega
    omega

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  by_cases ha : a = 0
  · subst ha; unfold sqrt; simp
  · unfold sqrt; simp only [ha, ↓reduceIte]
    exact min_sq_le a _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry

/-- Value of the round-up wrapper on naturals. -/
theorem sqrtUp_tonat (a : U256)
    (hss : ((sqrt a) * (sqrt a)).toNat = (sqrt a).toNat * (sqrt a).toNat)
    (hS128 : (sqrt a).toNat < 2 ^ 128) :
    (sqrtUp sqrt a).toNat =
      (sqrt a).toNat + (if (sqrt a).toNat * (sqrt a).toNat < a.toNat then 1 else 0) := by
  unfold sqrtUp
  show ((sqrt a) + (if (sqrt a) * (sqrt a) < a then 1 else 0)).toNat = _
  by_cases h : (sqrt a) * (sqrt a) < a
  · rw [if_pos h]
    have hb : (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
      have hlt := BitVec.lt_def.mp h; rw [hss] at hlt; exact hlt
    rw [if_pos hb]
    have h1 : (1 : U256).toNat = 1 := by decide
    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h]
    have hb : ¬ (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
      intro hc
      apply h
      rw [BitVec.lt_def, hss]; exact hc
    rw [if_neg hb]
    have h0 : (0 : U256).toNat = 0 := by decide
    rw [BitVec.toNat_add, h0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

/-- The root fits below `2 ^ 128`: its square is below `2 ^ 256`. -/
theorem sqrt_lt_pow (a : U256) (habove : (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat) :
    (sqrt a).toNat < 2 ^ 128 := by
  by_cases h : (sqrt a).toNat < 2 ^ 128
  · exact h
  · have hc' : 2 ^ 128 ≤ (sqrt a).toNat := by omega
    have hge := Nat.pow_le_pow_left hc' 2
    have e : (2 ^ 128) ^ 2 = 2 ^ 256 := by rw [Nat.pow_two, ← Nat.pow_add]
    rw [e] at hge
    have habove2 : (sqrt a).toNat ^ 2 ≤ a.toNat := by
      rw [Nat.pow_two]; exact habove
    have hle := Nat.le_trans hge habove2
    have hAlt : a.toNat < 2 ^ 256 := a.isLt
    omega

/-- The square of the root, as a `U256` product, matches the Nat product. -/
theorem sqrt_sq_tonat (a : U256) (habove : (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat) :
    ((sqrt a) * (sqrt a)).toNat = (sqrt a).toNat * (sqrt a).toNat := by
  have hAlt : a.toNat < 2 ^ 256 := a.isLt
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]

theorem req_sqrt_up_tight  : SqrtUpTight sqrt := by
  intro a ha
  have habove := req_sqrt_not_above a
  have hS128 := sqrt_lt_pow a habove
  have hss := sqrt_sq_tonat a habove
  rw [sqrtUp_tonat a hss hS128] at ha ⊢
  by_cases hb : (sqrt a).toNat * (sqrt a).toNat < a.toNat
  · rw [if_pos hb] at ⊢
    have e0 : (sqrt a).toNat + 1 - 1 = (sqrt a).toNat := Nat.add_sub_cancel _ _
    rw [e0]; exact hb
  · rw [if_neg hb] at ha ⊢
    rw [Nat.add_zero] at ha ⊢
    have hge : a.toNat ≤ (sqrt a).toNat * (sqrt a).toNat := by omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (show (sqrt a).toNat ≠ 0 by omega)
    rw [ht] at habove hge ⊢
    have e1 : t.succ - 1 = t := by omega
    rw [e1]
    have hlt : t * t < t.succ * t.succ := by
      rw [Nat.succ_eq_add_one]
      have e : (t + 1) * (t + 1) = t * t + (t + t + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
    omega

theorem req_mint_backed    : MintBacked sqrt := by
  intro a0 a1 l hl
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some hl
  have habove := req_sqrt_not_above (a0 * a1)
  rw [toNat_mul_of_lt hprod] at habove
  rw [hliq]
  exact habove

theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := by
  refine ⟨7, by decide, fun a => ?_⟩
  unfold sqrt newtonSqrt
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ha]
  · rw [if_neg ha, if_neg ha]; simp only [iterate, newtonStep]

end OzSqrt

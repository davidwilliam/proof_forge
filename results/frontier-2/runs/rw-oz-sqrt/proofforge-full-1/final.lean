import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.SqrtIter
import ProofForgeFin.WordBridge
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

open ProofForgeFin.Sqrt ProofForgeFin.WordBridge

/-- The fixed routine is the deployed algorithm with seven Newton steps. -/
theorem sqrt_eq_newton7 (a : U256) : sqrt a = newtonSqrt 7 a := by
  unfold sqrt newtonSqrt
  rfl

/-- Seven Newton steps from the power-of-two estimate reach the root or the root plus one. -/
theorem newton7_mem {A : Nat} (hA : 0 < A) (hs128 : Nat.sqrt A < 2 ^ 128) :
    newtonIter A 7 (2 ^ (Nat.log2 A / 2)) = Nat.sqrt A ∨
      (newtonIter A 7 (2 ^ (Nat.log2 A / 2)) = Nat.sqrt A + 1 ∧
        Nat.sqrt A * (Nat.sqrt A + 1) ≤ A) :=
  newtonIter_eq_or_succ_of_lt_two_mul (a := A) (x := 2 ^ (Nat.log2 A / 2)) (b := 128) (k := 5)
    (Nat.two_pow_pos _) (two_pow_half_log2_le_sqrt hA) (sqrt_lt_two_mul_two_pow_half_log2 _)
    hs128 (by decide) (by decide)

/-- The fixed routine returns the floor of the square root on every input. -/
theorem sqrt_toNat (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases h0 : a = 0
  · subst h0
    have e1 : sqrt (0 : U256) = 0 := by unfold sqrt; rw [if_pos rfl]
    rw [e1]; decide
  · have hApos : 0 < a.toNat := by
      by_cases hc : a.toNat = 0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using hc)) h0
      · omega
    have hAlt : a.toNat < 2 ^ 256 := a.isLt
    have hw256 : (0 : Nat) < 256 := by decide
    have h256 : (256 : Nat) ≤ 2 * 128 := by decide
    have hspos : 0 < Nat.sqrt a.toNat := sqrt_pos hApos
    have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
      sqrt_lt_two_pow_of_lt (w := 256) (k := 128) hAlt h256
    have hL : Nat.log2 a.toNat < 256 := log2_toNat_lt (w := 256) hw256 a
    have hshift : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
      rw [toNat_shiftRight, toNat_log2]
    have hx0 : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
      rw [shiftLeft_bv_eq, hshift]
      exact toNat_one_shiftLeft' (by omega)
    have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
    have h2x0 : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
      sqrt_lt_two_mul_two_pow_half_log2 _
    have hx0127 : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 127 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hdiv0 : a.toNat / 2 ^ (Nat.log2 a.toNat / 2)
        < 2 * 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
      div_lt_of_sqrt_lt_mul hx0pos h2x0
    have hsum0 : 2 ^ (Nat.log2 a.toNat / 2)
        + a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 := by omega
    have hN1lt : newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 := by
      have h2 : 2 ^ (Nat.log2 a.toNat / 2)
          + a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 130 := by omega
      have e : newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))
          = (2 ^ (Nat.log2 a.toNat / 2) + a.toNat / 2 ^ (Nat.log2 a.toNat / 2)) / 2 := rfl
      omega
    have hN1ge : Nat.sqrt a.toNat ≤ newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) :=
      sqrt_le_newton hx0pos
    have hsim : ∀ y : U256, Nat.sqrt a.toNat ≤ y.toNat → y.toNat < 2 ^ 129 →
        ((y + a / y) >>> 1).toNat = newton a.toNat y.toNat := by
      intro y h1 h2
      exact toNat_newton_word_of_sqrt_le hspos h1 (by omega)
    have hpres : ∀ n : Nat, Nat.sqrt a.toNat ≤ n → n < 2 ^ 129 →
        Nat.sqrt a.toNat ≤ newton a.toNat n ∧ newton a.toNat n < 2 ^ 129 := by
      intro n h1 h2
      refine ⟨sqrt_le_newton_of_le h1, ?_⟩
      have h3 := newton_le_max h1
      omega
    have hr1 : (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hw : ((1 : U256) <<< (log2 a >>> 1)).toNat
          + a.toNat / ((1 : U256) <<< (log2 a >>> 1)).toNat < 2 ^ 256 := by
        rw [hx0]; exact hsum0
      simp only [newtonStep]
      rw [toNat_newton_word _ _ hw, hx0]
    have hP1 : Nat.sqrt a.toNat
          ≤ (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat
        ∧ (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat < 2 ^ 129 := by
      rw [hr1]; exact ⟨hN1ge, hN1lt⟩
    have htail : (iterate (newtonStep a) 6
          (newtonStep a ((1 : U256) <<< (log2 a >>> 1)))).toNat
        = Nat.repeat (newton a.toNat) 6
          (newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) := by
      have h := iter_map_of_sim (iterate (newtonStep a)) (newtonStep a)
        (fun _ => rfl) (fun _ _ => rfl) BitVec.toNat (newton a.toNat)
        (fun n => Nat.sqrt a.toNat ≤ n ∧ n < 2 ^ 129)
        (fun y hy => hsim y hy.1 hy.2)
        (fun b hb => hpres b hb.1 hb.2)
        6 (newtonStep a ((1 : U256) <<< (log2 a >>> 1))) hP1
      rwa [hr1] at h
    have hrep : Nat.repeat (newton a.toNat) 6
          (newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
        = newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have e1 : Nat.repeat (newton a.toNat) 6
            (newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
          = newtonIter a.toNat 6
            (newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) := by
        rw [newtonIter_eq_repeat]
      rw [e1]; exact (newtonIter_succ a.toNat 6 _).symm
    have hmem := newton7_mem hApos hs128
    have hN7pos : 0 < newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) :=
      newtonIter_pos 7 hspos hx0pos
    have hmin : Nat.min (newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
        (a.toNat / newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
        = Nat.sqrt a.toNat :=
      min_div_eq_sqrt hN7pos hmem
    rw [sqrt_eq_newton7]
    unfold newtonSqrt
    rw [if_neg h0]
    show (OzSqrt.min (OzSqrt.iterate (OzSqrt.newtonStep a) 7
        ((1 : U256) <<< (log2 a >>> 1)))
      (a / OzSqrt.iterate (OzSqrt.newtonStep a) 7
        ((1 : U256) <<< (log2 a >>> 1)))).toNat
      = Nat.sqrt a.toNat
    have e76 : OzSqrt.iterate (OzSqrt.newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))
        = OzSqrt.iterate (OzSqrt.newtonStep a) 6
          (OzSqrt.newtonStep a ((1 : U256) <<< (log2 a >>> 1))) := rfl
    rw [e76, toNat_min, toNat_div, htail, hrep]
    exact hmin

/-- The rounded-up root on values. -/
theorem sqrtUp_toNat (a : U256) : (sqrtUp sqrt a).toNat
    = Nat.sqrt a.toNat
      + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  unfold sqrtUp
  have hr : (sqrt a).toNat = Nat.sqrt a.toNat := sqrt_toNat a
  have h256 : (256 : Nat) ≤ 2 * 128 := by decide
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    sqrt_lt_two_pow_of_lt (w := 256) (k := 128) a.isLt h256
  have hsq : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    have hbound : (sqrt a).toNat < 2 ^ 128 := by omega
    have h := toNat_mul_of_lt_two_pow (x := sqrt a) (y := sqrt a)
      (m := 128) (n := 128) hbound hbound (by decide)
    rw [h, hr]
  have hlt : (sqrt a * sqrt a < a) ↔ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
    rw [BitVec.lt_def, hsq]
  have h1 : (1 : U256).toNat = 1 := by decide
  have h0' : (0 : U256).toNat = 0 := by decide
  have hif : (if sqrt a * sqrt a < a then (1 : U256) else 0).toNat
      = (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
    rw [toNat_ite]
    by_cases h : sqrt a * sqrt a < a
    · rw [if_pos h, if_pos (hlt.mp h), h1]
    · rw [if_neg h, if_neg (fun c => h (hlt.mpr c)), h0']
  have hadd : (sqrt a + (if sqrt a * sqrt a < a then (1 : U256) else 0)).toNat
      = Nat.sqrt a.toNat
        + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
    have hb1 : (sqrt a).toNat < 2 ^ 128 := by omega
    have hb2 : (if sqrt a * sqrt a < a then (1 : U256) else 0).toNat < 2 ^ 128 := by
      by_cases h : sqrt a * sqrt a < a
      · rw [if_pos h]; decide
      · rw [if_neg h]; decide
    rw [toNat_add_of_lt_two_pow (x := sqrt a) (k := 128) hb1 hb2 (by decide), hr, hif]
  show (sqrt a + (if sqrt a * sqrt a < a then (1 : U256) else 0)).toNat = _
  rw [hadd]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  rw [sqrt_toNat]
  exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  rw [sqrt_toNat]
  exact Nat.lt_succ_sqrt _

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  rw [sqrtUp_toNat]
  exact le_mul_self_sqrt_add_ite _

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a h
  have hu := sqrtUp_toNat a
  rw [hu] at h ⊢
  exact sqrt_add_ite_sub_one_mul_self_lt h

theorem req_mint_backed : MintBacked sqrt := by
  intro amount0 amount1 liquidity h
  obtain ⟨hprod, _, hliq⟩ := firstMint_eq_some h
  have hmul := toNat_mul_of_lt hprod
  have hsqrt := sqrt_toNat (amount0 * amount1)
  have hle : Nat.sqrt (amount0.toNat * amount1.toNat)
        * Nat.sqrt (amount0.toNat * amount1.toNat)
      ≤ amount0.toNat * amount1.toNat := Nat.sqrt_le _
  have e : (liquidity.toNat + 1000) * (liquidity.toNat + 1000)
      = Nat.sqrt (amount0.toNat * amount1.toNat)
        * Nat.sqrt (amount0.toNat * amount1.toNat) := by
    have hll : liquidity.toNat + 1000 = Nat.sqrt (amount0 * amount1).toNat := by omega
    rw [hll, hmul]
  rw [e] at ⊢
  exact hle

theorem req_mint_full : MintFull sqrt := by
  intro amount0 amount1 liquidity h
  obtain ⟨hprod, _, hliq⟩ := firstMint_eq_some h
  have hmul := toNat_mul_of_lt hprod
  have hsqrt := sqrt_toNat (amount0 * amount1)
  have hlt : amount0.toNat * amount1.toNat
      < (Nat.sqrt (amount0.toNat * amount1.toNat) + 1)
        * (Nat.sqrt (amount0.toNat * amount1.toNat) + 1) :=
    Nat.lt_succ_sqrt _
  have e : (liquidity.toNat + 1001) * (liquidity.toNat + 1001)
      = (Nat.sqrt (amount0.toNat * amount1.toNat) + 1)
        * (Nat.sqrt (amount0.toNat * amount1.toNat) + 1) := by
    have hll : liquidity.toNat + 1001 = Nat.sqrt (amount0 * amount1).toNat + 1 := by omega
    rw [hll, hmul]
  rw [e] at ⊢
  exact hlt

theorem req_mint_live : MintLive sqrt := by
  intro amount0 amount1 hprod hbig
  apply firstMint_isSome hprod
  have hmul := toNat_mul_of_lt hprod
  have hsqrt := sqrt_toNat (amount0 * amount1)
  have hbig' : 1001 * 1001 ≤ (amount0 * amount1).toNat := by
    rw [hmul]; exact hbig
  have hle : 1001 ≤ Nat.sqrt (amount0 * amount1).toNat :=
    le_sqrt_of_mul_self_le hbig'
  omega

theorem req_newton_budget : NewtonBudget sqrt :=
  ⟨7, by decide, fun a => sqrt_eq_newton7 a⟩

end OzSqrt

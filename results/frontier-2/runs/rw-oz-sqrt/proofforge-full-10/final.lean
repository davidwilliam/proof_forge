import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.SqrtIter
import ProofForgeFin.WordBridge
import ProofForgeFin.NatSqrt
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

theorem sqrt_eq_newtonSqrt7 : sqrt = newtonSqrt 7 := by
  unfold sqrt newtonSqrt
  rfl

theorem toNat_sqrt (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases ha0 : a = 0
  · subst ha0
    have e0 : (0 : U256).toNat = 0 := by decide
    unfold sqrt
    rw [ite_eq_left rfl, e0, Nat.sqrt_zero]
  · have hapos : 0 < a.toNat := by
      cases Nat.eq_zero_or_pos a.toNat with
      | inl h => exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) ha0
      | inr h => exact h
    have hspos : 0 < Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.sqrt_pos hapos
    have hL : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
    have hlog : Nat.log2 a.toNat < 256 :=
      ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
    have hhalf : ((log2 a) >>> 1).toNat = Nat.log2 a.toNat / 2 := by
      rw [ProofForgeFin.WordBridge.toNat_shiftRight, hL, Nat.pow_one]
    have hlt256 : ((log2 a) >>> 1).toNat < 256 := by omega
    have hx0 : ((1 : U256) <<< (log2 a >>> 1)).toNat
        = 2 ^ (Nat.log2 a.toNat / 2) := by
      rw [ProofForgeFin.WordBridge.toNat_one_shiftLeft_bv (w := 256) hlt256, hhalf]
    have hx0le : 2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hapos
    have hsl2 : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
      ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 a.toNat
    have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
      ProofForgeFin.Sqrt.sqrt_toNat_lt_two_pow a (by decide)
    have hx0127 : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 127 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hdiv4 : a.toNat / 2 ^ (Nat.log2 a.toNat / 2)
        < 4 * 2 ^ (Nat.log2 a.toNat / 2) :=
      ProofForgeFin.Sqrt.div_lt_of_sqrt_lt_mul (a := a.toNat)
        (x := 2 ^ (Nat.log2 a.toNat / 2)) (c := 2) (Nat.two_pow_pos _) hsl2
    have hsum0 : ((1 : U256) <<< (log2 a >>> 1)).toNat
        + a.toNat / ((1 : U256) <<< (log2 a >>> 1)).toNat < 2 ^ 256 := by
      rw [hx0]
      have hbig : 5 * 2 ^ 127 < 2 ^ 256 := by decide
      omega
    have e1b : (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat
        = ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) := by
      have h := ProofForgeFin.Sqrt.toNat_newton_word (a := a)
        (x := ((1 : U256) <<< (log2 a >>> 1))) hsum0
      rw [hx0] at h
      exact h
    have hy1ge : Nat.sqrt a.toNat
        ≤ ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) :=
      ProofForgeFin.Sqrt.sqrt_le_newton (Nat.two_pow_pos _)
    have hy1lt : ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))
        < 2 ^ 129 := by
      have hN : ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))
          = (2 ^ (Nat.log2 a.toNat / 2) + a.toNat / 2 ^ (Nat.log2 a.toNat / 2)) / 2 := rfl
      have hbig2 : 3 * 2 ^ 127 < 2 ^ 129 := by decide
      omega
    have hPres : ∀ b : Nat, Nat.sqrt a.toNat ≤ b → b < 2 ^ 129 →
        Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat b ∧
          ProofForgeFin.Sqrt.newton a.toNat b < 2 ^ 129 := by
      intro b hle hblt
      have hle1 := ProofForgeFin.Sqrt.sqrt_le_newton_of_le (a := a.toNat) hle
      have hadd := ProofForgeFin.Sqrt.add_div_le_of_sqrt_le (a := a.toNat) hspos hle
      have hN : ProofForgeFin.Sqrt.newton a.toNat b = (b + a.toNat / b) / 2 := rfl
      refine ⟨hle1, by omega⟩
    have hsim : ∀ y : U256, (Nat.sqrt a.toNat ≤ y.toNat ∧ y.toNat < 2 ^ 129) →
        (newtonStep a y).toNat = ProofForgeFin.Sqrt.newton a.toNat y.toNat := by
      intro y hy
      obtain ⟨hle, hlt⟩ := hy
      show ((y + a / y) >>> 1).toNat = ProofForgeFin.Sqrt.newton a.toNat y.toNat
      exact ProofForgeFin.Sqrt.toNat_newton_word_of_sqrt_le hspos hle (by
        have hbig : 2 ^ 129 + 2 ^ 128 + 2 < 2 ^ 256 := by decide
        omega)
    have hw1P : (Nat.sqrt a.toNat
          ≤ (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat ∧
          (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat < 2 ^ 129) := by
      rw [e1b]
      exact ⟨hy1ge, hy1lt⟩
    have hmap := ProofForgeFin.WordBridge.iter_map_of_sim
      (iterate (newtonStep a)) (newtonStep a)
      (fun x => rfl) (fun k x => rfl) BitVec.toNat
      (ProofForgeFin.Sqrt.newton a.toNat)
      (fun b => Nat.sqrt a.toNat ≤ b ∧ b < 2 ^ 129) hsim
      (fun b h => hPres b h.1 h.2) 6
      (newtonStep a ((1 : U256) <<< (log2 a >>> 1))) hw1P
    rw [e1b] at hmap
    have h7 : ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))
        = ProofForgeFin.Sqrt.newtonIter a.toNat 6
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) := by
      rw [show (7 : Nat) = 1 + 6 from rfl, ProofForgeFin.Sqrt.newtonIter_add,
        ProofForgeFin.Sqrt.newtonIter_one]
    have hword7 : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hbridge : iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))
          = iterate (newtonStep a) 6
            (newtonStep a ((1 : U256) <<< (log2 a >>> 1))) := rfl
      rw [hbridge, hmap, ← ProofForgeFin.Sqrt.newtonIter_eq_repeat, h7]
    have hmem7 : ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))
        = Nat.sqrt a.toNat ∨
        (ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))
          = Nat.sqrt a.toNat + 1 ∧
          Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 1) ≤ a.toNat) :=
      ProofForgeFin.Sqrt.newtonIter_eq_or_succ_of_lt_two_mul
        (a := a.toNat) (x := 2 ^ (Nat.log2 a.toNat / 2)) (b := 128) (k := 5)
        (Nat.two_pow_pos _) hx0le hsl2 hs128 (by decide) (by decide)
    have hy7pos : 0 < ProofForgeFin.Sqrt.newtonIter a.toNat 7
        (2 ^ (Nat.log2 a.toNat / 2)) := by
      cases hmem7 with
      | inl h => omega
      | inr h =>
        obtain ⟨h1, h2⟩ := h
        omega
    have hminNat : Nat.min
        (ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
        (a.toNat / ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
        = Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.min_div_eq_sqrt hy7pos hmem7
    have hns : (newtonSqrt 7 a).toNat = Nat.sqrt a.toNat := by
      unfold newtonSqrt
      rw [ite_eq_right ha0]
      show (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat
        = Nat.sqrt a.toNat
      have hmin_rw : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
          (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat
          = Nat.min
            (ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
            (a.toNat / ProofForgeFin.Sqrt.newtonIter a.toNat 7
              (2 ^ (Nat.log2 a.toNat / 2))) := by
        show (if iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))
            < a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))
          then iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))
          else a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
          = _
        rw [ProofForgeFin.WordBridge.toNat_ite_lt, hword7, BitVec.toNat_udiv, hword7]
      rw [hmin_rw]
      exact hminNat
    have hsqrt7 : sqrt a = newtonSqrt 7 a := congrFun sqrt_eq_newtonSqrt7 a
    rw [hsqrt7]
    exact hns

theorem toNat_sqrtUp (a : U256) : (sqrtUp sqrt a).toNat
    = Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_toNat_lt_two_pow a (by decide)
  have hss : Nat.sqrt a.toNat * Nat.sqrt a.toNat < 2 ^ 256 :=
    ProofForgeFin.WordBridge.mul_self_lt_two_pow hs128 (by decide)
  have hmul : ((sqrt a) * (sqrt a)).toNat
      = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    have h := ProofForgeFin.WordBridge.toNat_mul_of_lt' (x := sqrt a) (y := sqrt a)
      (by rw [toNat_sqrt]; exact hss)
    rwa [toNat_sqrt] at h
  have hle : (2 : Nat) ^ 128 ≤ 2 ^ 256 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  unfold sqrtUp
  show ((sqrt a) + (if (sqrt a) * (sqrt a) < a then 1 else 0)).toNat = _
  by_cases hcN : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · have hc : (sqrt a) * (sqrt a) < a :=
      BitVec.lt_def.mpr (by rw [hmul]; exact hcN)
    rw [if_pos hc, if_pos hcN]
    have e1 : (1 : U256).toNat = 1 := by decide
    have hlt : (sqrt a).toNat + (1 : U256).toNat < 2 ^ 256 := by
      rw [toNat_sqrt, e1]
      omega
    have hadd := ProofForgeFin.WordBridge.toNat_add_of_lt' (x := sqrt a) (y := 1) hlt
    rw [toNat_sqrt, e1] at hadd
    exact hadd
  · have hc : ¬ (sqrt a) * (sqrt a) < a :=
      fun h => hcN (by have h2 := BitVec.lt_def.mp h; rwa [hmul] at h2)
    rw [if_neg hc, if_neg hcN]
    have e0 : (0 : U256).toNat = 0 := by decide
    have hlt : (sqrt a).toNat + (0 : U256).toNat < 2 ^ 256 := by
      rw [toNat_sqrt, e0]
      omega
    have hadd := ProofForgeFin.WordBridge.toNat_add_of_lt' (x := sqrt a) (y := 0) hlt
    rw [toNat_sqrt, e0] at hadd
    exact hadd

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  show ∀ a : U256, (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat
  intro a
  rw [toNat_sqrt]
  exact Nat.sqrt_le a.toNat

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  show ∀ a : U256, a.toNat < ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1)
  intro a
  rw [toNat_sqrt]
  exact Nat.lt_succ_sqrt a.toNat

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  show ∀ a : U256, a.toNat ≤ (sqrtUp sqrt a).toNat * (sqrtUp sqrt a).toNat
  intro a
  rw [toNat_sqrtUp]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite a.toNat

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  show ∀ a : U256, 0 < (sqrtUp sqrt a).toNat →
    (((sqrtUp sqrt a).toNat - 1) * ((sqrtUp sqrt a).toNat - 1) < a.toNat)
  intro a ha
  rw [toNat_sqrtUp] at ha ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt ha

theorem req_mint_backed : MintBacked sqrt := by
  show ∀ amount0 amount1 liquidity : U256,
    firstMint sqrt amount0 amount1 = some liquidity →
      (liquidity.toNat + 1000) * (liquidity.toNat + 1000)
        ≤ amount0.toNat * amount1.toNat
  intro a0 a1 l hl
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some hl
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hsqrt : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [toNat_sqrt, hmul]
  rw [hliq, hsqrt]
  exact Nat.sqrt_le _

theorem req_mint_full : MintFull sqrt := by
  show ∀ amount0 amount1 liquidity : U256,
    firstMint sqrt amount0 amount1 = some liquidity →
      amount0.toNat * amount1.toNat
        < (liquidity.toNat + 1001) * (liquidity.toNat + 1001)
  intro a0 a1 l hl
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some hl
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hsqrt : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [toNat_sqrt, hmul]
  have hlt := Nat.lt_succ_sqrt (a0.toNat * a1.toNat)
  have e : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by omega
  rw [e]
  exact hlt

theorem req_mint_live : MintLive sqrt := by
  show ∀ amount0 amount1 : U256, amount0.toNat * amount1.toNat < 2 ^ 256 →
    1001 * 1001 ≤ amount0.toNat * amount1.toNat →
      (firstMint sqrt amount0 amount1).isSome
  intro a0 a1 hprod hbig
  apply firstMint_isSome hprod
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  rw [toNat_sqrt, hmul]
  have hle : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) :=
    ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le hbig
  omega

theorem req_newton_budget : NewtonBudget sqrt :=
  ⟨7, by decide, fun a => congrFun sqrt_eq_newtonSqrt7 a⟩

end OzSqrt

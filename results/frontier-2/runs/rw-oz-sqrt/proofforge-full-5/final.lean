import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
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

theorem sqrt_init_toNat (a : U256) :
    ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
  have hshift : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
    rw [ProofForgeFin.WordBridge.toNat_shiftRight _ 1, hlog, Nat.pow_one]
  have hlt : (log2 a >>> 1).toNat < 256 := by
    rw [hshift]
    have h2 := ProofForgeFin.WordBridge.log2_toNat_lt (w := 256) (by decide) a
    omega
  rw [ProofForgeFin.WordBridge.toNat_one_shiftLeft_bv hlt, hshift]

theorem sqrt_nat_iter_le (A k : Nat) (hA : A < 2 ^ 256) (hApos : 0 < A) :
    ProofForgeFin.Sqrt.newtonIter A k (2 ^ (Nat.log2 A / 2)) ≤ 2 ^ 129 := by
  have hL : Nat.log2 A < 256 := (Nat.log2_lt (by omega)).mpr hA
  have hx0le : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A :=
    ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hApos
  have hs128 : Nat.sqrt A < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt hA (by decide)
  rcases k with _ | j
  · rw [ProofForgeFin.Sqrt.newtonIter_zero]
    have h127 : 2 ^ (Nat.log2 A / 2) ≤ 2 ^ 127 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rw [ProofForgeFin.Sqrt.newtonIter_succ]
    have hx0pos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.two_pow_pos _
    have hs1 : Nat.sqrt A ≤ ProofForgeFin.Sqrt.newton A (2 ^ (Nat.log2 A / 2)) :=
      ProofForgeFin.Sqrt.sqrt_le_newton hx0pos
    have hd1 : ProofForgeFin.Sqrt.newton A (2 ^ (Nat.log2 A / 2)) - Nat.sqrt A ≤
        Nat.sqrt A / 4 + 2 :=
      ProofForgeFin.Sqrt.newton_sub_sqrt_le_of_lt_two_mul hx0pos hx0le
        (ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 A)
    have hle := ProofForgeFin.Sqrt.newtonIter_le_max (a := A)
      (x := ProofForgeFin.Sqrt.newton A (2 ^ (Nat.log2 A / 2))) j hs1
    omega

theorem sqrt_nat_sum_bound (A x : Nat) (hA : A < 2 ^ 256) (hApos : 0 < A)
    (hxpos : 0 < x) (hxB : x ≤ 2 ^ 129)
    (h : x = 2 ^ (Nat.log2 A / 2) ∨ Nat.sqrt A ≤ x) :
    x + A / x < 2 ^ 256 := by
  have hL : Nat.log2 A < 256 := (Nat.log2_lt (by omega)).mpr hA
  have hspos : 0 < Nat.sqrt A := ProofForgeFin.Sqrt.sqrt_pos hApos
  have hx0le : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A :=
    ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hApos
  have hs128 : Nat.sqrt A < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt hA (by decide)
  have hx0127 : 2 ^ (Nat.log2 A / 2) ≤ 2 ^ 127 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rcases h with rfl | hle
  · have hx0pos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.two_pow_pos _
    have hdiv := ProofForgeFin.Sqrt.div_lt_of_sqrt_lt_mul (a := A)
      (x := 2 ^ (Nat.log2 A / 2)) (c := 2) hx0pos
      (ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 A)
    omega
  · have hle2 := ProofForgeFin.Sqrt.add_div_le_of_sqrt_le (a := A) (x := x) hspos hle
    omega

theorem sqrt_step_toNat (a : U256) (y : U256) (hApos : 0 < a.toNat)
    (hP : y.toNat = 2 ^ (Nat.log2 a.toNat / 2) ∨ Nat.sqrt a.toNat ≤ y.toNat)
    (hxB : y.toNat ≤ 2 ^ 129) :
    (newtonStep a y).toNat = ProofForgeFin.Sqrt.newton a.toNat y.toNat := by
  have hxpos : 0 < y.toNat := by
    rcases hP with hEq | hle
    · rw [hEq]; exact Nat.two_pow_pos _
    · exact Nat.lt_of_lt_of_le (ProofForgeFin.Sqrt.sqrt_pos hApos) hle
  have hsum := sqrt_nat_sum_bound a.toNat y.toNat a.isLt hApos hxpos hxB hP
  exact ProofForgeFin.Sqrt.toNat_newton_word a y hsum

theorem sqrt_iter_toNat (a : U256) (hApos : 0 < a.toNat) (k : Nat) :
    (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> 1))).toNat =
    ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)) := by
  induction k with
  | zero =>
    rw [ProofForgeFin.Sqrt.newtonIter_zero]
    exact sqrt_init_toNat a
  | succ k ih =>
    rw [ProofForgeFin.WordBridge.iter_succ_of_eqns (iterate (newtonStep a)) (newtonStep a)
      (fun x => rfl) (fun k x => rfl) k _,
      ProofForgeFin.Sqrt.newtonIter_succ']
    have hBk : (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> 1))).toNat ≤ 2 ^ 129 := by
      rw [ih]
      exact sqrt_nat_iter_le a.toNat k a.isLt hApos
    have hPk : (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> 1))).toNat =
        2 ^ (Nat.log2 a.toNat / 2) ∨
        Nat.sqrt a.toNat ≤ (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> 1))).toNat := by
      rw [ih]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · left
        exact ProofForgeFin.Sqrt.newtonIter_zero _ _
      · right
        exact ProofForgeFin.Sqrt.sqrt_le_newtonIter (Nat.two_pow_pos _) hk
    have hstep := sqrt_step_toNat a _ hApos hPk hBk
    rw [hstep, ih]

theorem sqrt_toNat (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases h : a = 0
  · subst h
    have hsqrt : sqrt (0 : U256) = 0 := by simp [sqrt]
    rw [hsqrt]
    decide
  · have hApos : 0 < a.toNat := ProofForgeFin.WordBridge.ne_zero_iff_toNat_pos.mp h
    have heq : sqrt a = newtonSqrt 7 a := by
      simp only [sqrt, newtonSqrt, iterate, newtonStep]
    rw [heq]
    have hns : newtonSqrt 7 a = min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) := by
      unfold newtonSqrt
      rw [if_neg h]
    rw [hns, toNat_min, BitVec.toNat_udiv, sqrt_iter_toNat a hApos 7]
    have hspos : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hApos
    have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
    have hpos : 0 < ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) :=
      ProofForgeFin.Sqrt.newtonIter_pos 7 hspos hx0pos
    have hmem : ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) =
        Nat.sqrt a.toNat ∨
        (ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) =
          Nat.sqrt a.toNat + 1 ∧
          Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 1) ≤ a.toNat) :=
      ProofForgeFin.Sqrt.newtonIter_eq_or_succ_of_lt_two_mul (a := a.toNat)
        (x := 2 ^ (Nat.log2 a.toNat / 2)) (b := 128) (k := 5) hx0pos
        (ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hApos)
        (ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 a.toNat)
        (ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt a.isLt (by decide))
        (by decide) (by decide)
    exact ProofForgeFin.Sqrt.min_div_eq_sqrt hpos hmem

theorem sqrtUp_toNat (a : U256) : (sqrtUp sqrt a).toNat =
    Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt a.isLt (by decide)
  have hss : Nat.sqrt a.toNat * Nat.sqrt a.toNat < 2 ^ 256 :=
    ProofForgeFin.WordBridge.mul_self_lt_two_pow hs128 (by decide)
  have hprod : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    rw [BitVec.toNat_mul, sqrt_toNat a, Nat.mod_eq_of_lt hss]
  show ((sqrt a + (if sqrt a * sqrt a < a then (1 : U256) else 0))).toNat = _
  by_cases hc : sqrt a * sqrt a < a
  · rw [if_pos hc]
    have hcN : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      have hlt := BitVec.lt_def.mp hc
      rwa [hprod] at hlt
    rw [if_pos hcN, BitVec.toNat_add, sqrt_toNat a]
    have h1 : (1 : U256).toNat = 1 := by decide
    rw [h1, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hc]
    have hcN : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      intro hlt
      apply hc
      rw [BitVec.lt_def, hprod]
      exact hlt
    rw [if_neg hcN, BitVec.toNat_add, sqrt_toNat a]
    have h0 : (0 : U256).toNat = 0 := by decide
    rw [h0, Nat.mod_eq_of_lt (by omega)]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  unfold SqrtNotAbove
  intro a
  rw [sqrt_toNat]
  exact Nat.sqrt_le a.toNat

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  unfold SqrtNotBelow
  intro a
  rw [sqrt_toNat]
  exact Nat.lt_succ_sqrt a.toNat

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  unfold SqrtUpCovers
  intro a
  rw [sqrtUp_toNat]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite a.toNat

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  unfold SqrtUpTight
  intro a h
  rw [sqrtUp_toNat] at h ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt h

theorem req_mint_backed : MintBacked sqrt := by
  unfold MintBacked
  intro a0 a1 l h
  obtain ⟨hprod, hmin, hliq⟩ := firstMint_eq_some h
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hle : (sqrt (a0 * a1)).toNat * (sqrt (a0 * a1)).toNat ≤ (a0 * a1).toNat := by
    rw [sqrt_toNat]
    exact Nat.sqrt_le _
  rw [hliq, ← hmul]
  exact hle

theorem req_mint_full : MintFull sqrt := by
  unfold MintFull
  intro a0 a1 l h
  obtain ⟨hprod, hmin, hliq⟩ := firstMint_eq_some h
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hlt : (a0 * a1).toNat <
      ((sqrt (a0 * a1)).toNat + 1) * ((sqrt (a0 * a1)).toNat + 1) := by
    rw [sqrt_toNat]
    exact Nat.lt_succ_sqrt _
  have e : l.toNat + 1001 = (sqrt (a0 * a1)).toNat + 1 := by omega
  rw [← hmul, e]
  exact hlt

theorem req_mint_live : MintLive sqrt := by
  unfold MintLive
  intro a0 a1 h1 h2
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt h1
  have h1001 : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [ProofForgeFin.Sqrt.le_sqrt_iff]
    omega
  have hgt : 1000 < (sqrt (a0 * a1)).toNat := by
    rw [sqrt_toNat, hmul]
    omega
  exact firstMint_isSome h1 hgt
theorem req_newton_budget : NewtonBudget sqrt := by
  refine ⟨7, by decide, fun a => ?_⟩
  simp only [sqrt, newtonSqrt, iterate, newtonStep]

end OzSqrt

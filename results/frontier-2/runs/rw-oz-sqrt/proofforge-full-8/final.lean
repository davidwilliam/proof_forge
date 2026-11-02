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

/-- `(log2 a >>> 1)` has value `Nat.log2 a / 2`. -/
theorem log2_half_val (a : U256) : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
  rw [ProofForgeFin.WordBridge.toNat_shiftRight, toNat_log2, Nat.pow_one]

/-- The power-of-two estimate has value `2 ^ (Nat.log2 a / 2)`. -/
theorem init_val (a : U256) : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have h1 : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := log2_half_val a
  have hlog : Nat.log2 a.toNat < 256 :=
    ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
  have hlt : (log2 a >>> 1).toNat < 256 := by omega
  rw [ProofForgeFin.WordBridge.shiftLeft_bv_eq]
  rw [ProofForgeFin.WordBridge.toNat_one_shiftLeft' (w := 256) hlt, h1]

/-- `sqrt` unfolds to the same seven explicit Newton steps. -/
theorem sqrt_unfold (a : U256) (h : a ≠ 0) :
    sqrt a =
      (let r0 : U256 := (1 : U256) <<< (log2 a >>> 1)
       let r1 := (r0 + a / r0) >>> 1
       let r2 := (r1 + a / r1) >>> 1
       let r3 := (r2 + a / r2) >>> 1
       let r4 := (r3 + a / r3) >>> 1
       let r5 := (r4 + a / r4) >>> 1
       let r6 := (r5 + a / r5) >>> 1
       let r7 := (r6 + a / r6) >>> 1
       min r7 (a / r7)) := by
  unfold sqrt
  rw [if_neg h]

/-- `sqrt` is the deployed seven-step routine. -/
theorem sqrt_eq_ns7 (a : U256) : sqrt a = newtonSqrt 7 a := by
  unfold sqrt newtonSqrt
  by_cases h : a = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    simp only [iterate, newtonStep]

/-- Seven Nat Newton steps from the power-of-two estimate reach the root or the root plus one. -/
theorem nat_newton7_mem (n : Nat) (h256 : n < 2 ^ 256) (hpos : 0 < n) :
    ProofForgeFin.Sqrt.newtonIter n 7 (2 ^ (Nat.log2 n / 2)) = Nat.sqrt n ∨
      (ProofForgeFin.Sqrt.newtonIter n 7 (2 ^ (Nat.log2 n / 2)) = Nat.sqrt n + 1 ∧
        Nat.sqrt n * (Nat.sqrt n + 1) ≤ n) := by
  open ProofForgeFin.Sqrt in
  have hx0 : 0 < 2 ^ (Nat.log2 n / 2) := Nat.two_pow_pos _
  have h1 := two_pow_half_log2_le_sqrt (a := n) hpos
  have h2 := sqrt_lt_two_mul_two_pow_half_log2 (a := n)
  have hs := sqrt_lt_two_pow_of_lt (a := n) (w := 256) (k := 128) h256 (by decide)
  have hmem := newtonIter_eq_or_succ_of_lt_two_mul (a := n) (x := 2 ^ (Nat.log2 n / 2))
    (b := 128) (k := 5) hx0 h1 h2 hs (by decide) (by decide)
  have h52 : (5 : Nat) + 2 = 7 := rfl
  rw [h52] at hmem
  exact hmem

/-- Six word steps after the first one act as six Nat steps. -/
theorem iter6_toNat (a : U256) (hpos : 0 < a.toNat) :
    (iterate (newtonStep a) 6
      (newtonStep a ((1 : U256) <<< (log2 a >>> 1)))).toNat =
      ProofForgeFin.Sqrt.newtonIter a.toNat 6
        (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) := by
  open ProofForgeFin.Sqrt in
  have hL : Nat.log2 a.toNat < 256 :=
    ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
  have h1 : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) :=
    init_val a
  have hs : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hpos
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    sqrt_lt_two_pow_of_lt a.isLt (by decide)
  have h127 : (2 : Nat) ^ 127 ≤ 2 ^ 129 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have hbig : (2 : Nat) ^ 129 + 2 ^ 128 + 2 ≤ 2 ^ 256 := by
    have l1 : (2 : Nat) ^ 129 ≤ 2 ^ 255 := Nat.pow_le_pow_right (by decide) (by decide)
    have l2 : (2 : Nat) ^ 128 ≤ 2 ^ 255 := Nat.pow_le_pow_right (by decide) (by decide)
    have e : (2 : Nat) ^ 255 + 2 ^ 255 = 2 ^ 256 := by grind
    omega
  have hx0le : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 127 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hdiv : a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 * 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
    div_lt_of_sqrt_lt_mul (Nat.two_pow_pos _)
      (sqrt_lt_two_mul_two_pow_half_log2 a.toNat)
  have h4 : 2 * 2 * 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 129 := by
    have e : (2 : Nat) * 2 * 2 ^ (Nat.log2 a.toNat / 2) =
        2 ^ 2 * 2 ^ (Nat.log2 a.toNat / 2) := by grind
    rw [e, ← Nat.pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hP_first : 0 < newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) ∧
      newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) ≤ 2 ^ 129 ∧
      Nat.sqrt a.toNat ≤ newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) := by
    refine ⟨?_, ?_, sqrt_le_newton (Nat.two_pow_pos _)⟩
    · have hle : Nat.sqrt a.toNat ≤ newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) :=
        sqrt_le_newton (Nat.two_pow_pos _)
      omega
    · unfold newton
      omega
  have hf : ∀ y : U256,
      (0 < y.toNat ∧ y.toNat ≤ 2 ^ 129 ∧ Nat.sqrt a.toNat ≤ y.toNat) →
      (newtonStep a y).toNat = newton a.toNat y.toNat := by
    intro y hy
    unfold newtonStep
    exact toNat_newton_word_of_sqrt_le hs hy.2.2 (by omega)
  have hP : ∀ b : Nat,
      (0 < b ∧ b ≤ 2 ^ 129 ∧ Nat.sqrt a.toNat ≤ b) →
      (0 < newton a.toNat b ∧ newton a.toNat b ≤ 2 ^ 129 ∧
        Nat.sqrt a.toNat ≤ newton a.toNat b) := by
    intro b hb
    refine ⟨?_, ?_, sqrt_le_newton_of_le hb.2.2⟩
    · have := sqrt_le_newton_of_le (a := a.toNat) hb.2.2
      omega
    · have hle := newton_le_max (a := a.toNat) hb.2.2
      have hs1 : Nat.sqrt a.toNat + 1 ≤ 2 ^ 129 := by omega
      omega
  have hsim := ProofForgeFin.WordBridge.iter_map_of_sim
    (iterate (newtonStep a)) (newtonStep a)
    (fun x => rfl) (fun k x => by simp only [iterate]) BitVec.toNat (newton a.toNat)
    (fun b => 0 < b ∧ b ≤ 2 ^ 129 ∧ Nat.sqrt a.toNat ≤ b) hf hP 6
    (newtonStep a ((1 : U256) <<< (log2 a >>> 1)))
  have hr1 : (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat =
      newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) := by
    have h0 : (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat =
        newton a.toNat (((1 : U256) <<< (log2 a >>> 1))).toNat := by
      unfold newtonStep
      apply toNat_newton_word
      rw [h1]
      omega
    rw [h0, h1]
  have hmem := hsim (by rw [hr1]; exact hP_first)
  rw [hr1] at hmem
  rw [← newtonIter_eq_repeat] at hmem
  exact hmem

/-- The word routine returns the floor root of the value. -/
theorem sqrt_toNat (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  open ProofForgeFin.Sqrt in
  by_cases h : a = 0
  · subst h
    unfold sqrt
    rw [if_pos rfl]
    have hz : Nat.sqrt 0 = 0 :=
      ProofForgeFin.Sqrt.sqrt_eq_of_bounds (by decide) (by decide)
    simp only [ProofForgeFin.WordBridge.toNat_zero', hz]
  · have hpos : 0 < a.toNat :=
      ProofForgeFin.WordBridge.ne_zero_iff_toNat_pos.mp h
    have hmem7 := nat_newton7_mem a.toNat a.isLt hpos
    have e7 : iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)) =
        iterate (newtonStep a) 6
          (newtonStep a ((1 : U256) <<< (log2 a >>> 1))) := rfl
    have h7 : newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) =
        newtonIter a.toNat 6 (newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) :=
      newtonIter_succ a.toNat 6 (2 ^ (Nat.log2 a.toNat / 2))
    have hspos : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hpos
    have hy : 0 < newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) := by
      rcases hmem7 with hh | ⟨hh, _⟩ <;> omega
    have hmin : Nat.min (newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
        (a.toNat / newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))) = Nat.sqrt a.toNat :=
      min_div_eq_sqrt hy hmem7
    have hbridge := iter6_toNat a hpos
    rw [sqrt_eq_ns7]
    unfold newtonSqrt
    rw [if_neg h, e7]
    have hword : (min (iterate (newtonStep a) 6
        (newtonStep a ((1 : U256) <<< (log2 a >>> 1))))
        (a / iterate (newtonStep a) 6
          (newtonStep a ((1 : U256) <<< (log2 a >>> 1))))).toNat =
        Nat.min (newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
          (a.toNat / newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))) := by
      rw [toNat_min, BitVec.toNat_udiv, hbridge, h7]
    rw [hword, hmin]

/-- The rounded-up root on words is the rounded-up root on values. -/
theorem sqrtUp_toNat (a : U256) :
    (sqrtUp sqrt a).toNat =
      Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hroot := sqrt_toNat a
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt a.isLt (by decide)
  have hsq : (sqrt a * sqrt a).toNat =
      Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    have hlt : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
      rw [hroot]
      exact ProofForgeFin.WordBridge.mul_self_lt_two_pow hs128 (by decide)
    rw [ProofForgeFin.WordBridge.toNat_mul_of_lt' hlt, hroot]
  have hite : ((if sqrt a * sqrt a < a then (1 : U256) else 0)).toNat =
      (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
    by_cases h : sqrt a * sqrt a < a
    · have hp : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
        have := BitVec.lt_def.mp h
        omega
      rw [if_pos h, if_pos hp]
      exact BitVec.toNat_one (by decide)
    · have hn : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
        intro hc
        apply h
        exact BitVec.lt_def.mpr (by omega)
      rw [if_neg h, if_neg hn]
      rfl
  have hsum : (sqrt a).toNat +
      (if sqrt a * sqrt a < a then (1 : U256) else 0).toNat < 2 ^ 256 := by
    rw [hroot, hite]
    by_cases hc : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  unfold sqrtUp
  rw [ProofForgeFin.WordBridge.toNat_add_of_lt' hsum, hroot, hite]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  show (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat
  rw [sqrt_toNat]
  exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  show a.toNat < ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1)
  rw [sqrt_toNat]
  exact Nat.lt_succ_sqrt a.toNat

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  show a.toNat ≤ (sqrtUp sqrt a).toNat * (sqrtUp sqrt a).toNat
  rw [sqrtUp_toNat]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite a.toNat

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a ha
  show ((sqrtUp sqrt a).toNat - 1) * ((sqrtUp sqrt a).toNat - 1) < a.toNat
  rw [sqrtUp_toNat] at ha ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt ha

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l h
  show (l.toNat + 1000) * (l.toNat + 1000) ≤ a0.toNat * a1.toNat
  obtain ⟨hlt, _, heq⟩ := firstMint_eq_some h
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hlt
  have hs : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, hmul]
  have e : l.toNat + 1000 = Nat.sqrt (a0.toNat * a1.toNat) := by omega
  rw [e]
  exact Nat.sqrt_le (a0.toNat * a1.toNat)

theorem req_mint_full : MintFull sqrt := by
  intro a0 a1 l h
  show a0.toNat * a1.toNat < (l.toNat + 1001) * (l.toNat + 1001)
  obtain ⟨hlt, _, heq⟩ := firstMint_eq_some h
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hlt
  have hs : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, hmul]
  have e : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by omega
  rw [e]
  exact Nat.lt_succ_sqrt (a0.toNat * a1.toNat)

theorem req_mint_live : MintLive sqrt := by
  intro a0 a1 hlt hbig
  show (firstMint sqrt a0 a1).isSome
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hlt
  have hs : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, hmul]
  have hle : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) :=
    ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le hbig
  have h1000 : 1000 < (sqrt (a0 * a1)).toNat := by omega
  exact firstMint_isSome hlt h1000

theorem req_newton_budget : NewtonBudget sqrt :=
  ⟨7, by decide, fun a => sqrt_eq_ns7 a⟩

end OzSqrt

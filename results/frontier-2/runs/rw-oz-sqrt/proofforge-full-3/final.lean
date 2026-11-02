import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.SqrtIter
import ProofForgeFin.NatSqrt
import ProofForgeFin.WordBridge
/-!
The square-root routine under repair, `Math.sqrt(uint256 a)` in the style of OpenZeppelin
Contracts `Math.sol`, as this pool's first deposit calls it (seven Newton steps).
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

theorem newtonIter7_min_eq (A : Nat) (hA : 0 < A) (hA256 : A < 2 ^ 256) :
    Nat.min (ProofForgeFin.Sqrt.newtonIter A 7 (2 ^ (Nat.log2 A / 2)))
        (A / ProofForgeFin.Sqrt.newtonIter A 7 (2 ^ (Nat.log2 A / 2))) = Nat.sqrt A := by
  have hsPos : 0 < Nat.sqrt A := ProofForgeFin.Sqrt.sqrt_pos hA
  have hx0pos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.pow_pos (by decide)
  have hx0le : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A :=
    ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hA
  have h2x0 : Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) :=
    ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 A
  have hof : (BitVec.ofNat 256 A).toNat = A :=
    ProofForgeFin.WordBridge.toNat_ofNat_of_lt' hA256
  have hs128 : Nat.sqrt A < 2 ^ 128 := by
    have h := ProofForgeFin.Sqrt.sqrt_toNat_lt_two_pow
      (BitVec.ofNat 256 A) (show 256 ≤ 2 * 128 from by decide)
    rw [hof] at h
    exact h
  have hmem : ProofForgeFin.Sqrt.newtonIter A 7 (2 ^ (Nat.log2 A / 2)) = Nat.sqrt A ∨
      (ProofForgeFin.Sqrt.newtonIter A 7 (2 ^ (Nat.log2 A / 2)) = Nat.sqrt A + 1 ∧
        Nat.sqrt A * (Nat.sqrt A + 1) ≤ A) := by
    have h := ProofForgeFin.Sqrt.newtonIter_eq_or_succ_of_lt_two_mul
      (a := A) (x := 2 ^ (Nat.log2 A / 2)) (b := 128) (k := 5)
      hx0pos hx0le h2x0 hs128 (by decide) (by decide)
    simpa using h
  have hy7pos : 0 < ProofForgeFin.Sqrt.newtonIter A 7 (2 ^ (Nat.log2 A / 2)) := by
    have hle := ProofForgeFin.Sqrt.sqrt_le_newtonIter (a := A) hx0pos (show 0 < 7 from by decide)
    omega
  exact ProofForgeFin.Sqrt.min_div_eq_sqrt hy7pos hmem

theorem sqrt_toNat (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases ha : a = 0
  · subst ha
    unfold sqrt
    rw [if_pos rfl]
    have h0 : (0 : U256).toNat = 0 := ProofForgeFin.WordBridge.toNat_zero'
    rw [h0]
    exact Nat.sqrt_zero
  · have hApos : 0 < a.toNat :=
      ProofForgeFin.WordBridge.ne_zero_iff_toNat_pos.mp ha
    have hA256 : a.toNat < 2 ^ 256 := a.isLt
    have hL : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
    have hL256 : Nat.log2 a.toNat < 256 :=
      ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
    have hshift : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
      rw [ProofForgeFin.WordBridge.toNat_shiftRight, hL, Nat.pow_one]
    have hinit : ((1 : U256) <<< (log2 a >>> 1)).toNat
        = 2 ^ (Nat.log2 a.toNat / 2) := by
      have hlt : (log2 a >>> 1).toNat < 256 := by omega
      rw [ProofForgeFin.WordBridge.toNat_one_shiftLeft_bv hlt, hshift]
    have hsPos : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hApos
    have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.pow_pos (by decide)
    have hx0le : 2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hApos
    have hx0le127 : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 127 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hx0255 : 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 255 :=
      Nat.lt_of_le_of_lt hx0le127 (Nat.pow_lt_pow_right (by decide) (by decide))
    have hs254 : Nat.sqrt a.toNat < 2 ^ 254 :=
      Nat.lt_of_lt_of_le
        (ProofForgeFin.Sqrt.sqrt_toNat_lt_two_pow a (show 256 ≤ 2 * 128 from by decide))
        (Nat.pow_le_pow_right (by decide) (by decide))
    have h2_254 : (2 : Nat) < 2 ^ 254 := by
      have hle : (2 : Nat) ^ 2 ≤ 2 ^ 254 :=
        Nat.pow_le_pow_right (by decide) (by decide)
      have e2 : (2 : Nat) ^ 2 = 4 := by decide
      omega
    have hs2_255 : Nat.sqrt a.toNat + 2 < 2 ^ 255 :=
      ProofForgeFin.WordBridge.add_lt_two_pow hs254 h2_254 (by decide)
    have hA4 : a.toNat < 4 * 2 ^ (Nat.log2 a.toNat / 2) * 2 ^ (Nat.log2 a.toNat / 2) := by
      have hup : a.toNat < (Nat.sqrt a.toNat + 1) * (Nat.sqrt a.toNat + 1) :=
        Nat.lt_succ_sqrt a.toNat
      have hs1le : Nat.sqrt a.toNat + 1 ≤ 2 * 2 ^ (Nat.log2 a.toNat / 2) := by
        have h2 := ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 a.toNat
        omega
      have hle : (Nat.sqrt a.toNat + 1) * (Nat.sqrt a.toNat + 1) ≤
          (2 * 2 ^ (Nat.log2 a.toNat / 2)) * (2 * 2 ^ (Nat.log2 a.toNat / 2)) :=
        Nat.mul_le_mul hs1le hs1le
      have e : (2 * 2 ^ (Nat.log2 a.toNat / 2)) * (2 * 2 ^ (Nat.log2 a.toNat / 2)) =
          4 * 2 ^ (Nat.log2 a.toNat / 2) * 2 ^ (Nat.log2 a.toNat / 2) := by grind
      have hle2 : (Nat.sqrt a.toNat + 1) * (Nat.sqrt a.toNat + 1) ≤
          4 * 2 ^ (Nat.log2 a.toNat / 2) * 2 ^ (Nat.log2 a.toNat / 2) := by
        rw [← e]
        exact hle
      exact Nat.lt_of_lt_of_le hup hle2
    have hdiv4 : a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 4 * 2 ^ (Nat.log2 a.toNat / 2) :=
      (Nat.div_lt_iff_lt_mul hx0pos).mpr hA4
    have h4x0_255 : 4 * 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 255 := by
      have h4le : 4 * 2 ^ (Nat.log2 a.toNat / 2) ≤ 4 * 2 ^ 127 :=
        Nat.mul_le_mul (Nat.le_refl _) hx0le127
      have e : (4 : Nat) * 2 ^ 127 = 2 ^ 129 := by
        rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
      have h129 : (2 : Nat) ^ 129 ≤ 2 ^ 255 :=
        Nat.pow_le_pow_right (by decide) (by decide)
      omega
    have hAdiv255 : a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 255 :=
      Nat.lt_of_lt_of_le hdiv4 (Nat.le_of_lt h4x0_255)
    have hsum0 : 2 ^ (Nat.log2 a.toNat / 2)
        + a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 :=
      ProofForgeFin.WordBridge.add_lt_two_pow hx0255 hAdiv255 (by decide)
    have h7 : sqrt a = newtonSqrt 7 a := by
      unfold sqrt newtonSqrt
      rw [ite_eq_right ha, ite_eq_right ha]
      rfl
    have hns : newtonSqrt 7 a =
        min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
          (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) := by
      unfold newtonSqrt
      rw [ite_eq_right ha]
    have hr1 : (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat =
        ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hsum : ((1 : U256) <<< (log2 a >>> 1)).toNat +
          a.toNat / ((1 : U256) <<< (log2 a >>> 1)).toNat < 2 ^ 256 := by
        rw [hinit]
        exact hsum0
      unfold newtonStep
      have e := ProofForgeFin.Sqrt.toNat_newton_word
        (a := a) (x := ((1 : U256) <<< (log2 a >>> 1))) hsum
      rw [hinit] at e
      exact e
    have hf : ∀ y : U256,
        (Nat.sqrt a.toNat ≤ y.toNat ∧ y.toNat < 2 ^ 255) →
        (newtonStep a y).toNat = ProofForgeFin.Sqrt.newton a.toNat y.toNat := by
      intro y hy
      obtain ⟨hle, hlt⟩ := hy
      have hsum : y.toNat + a.toNat / y.toNat < 2 ^ 256 := by
        have hadd : y.toNat + a.toNat / y.toNat ≤ y.toNat + Nat.sqrt a.toNat + 2 :=
          ProofForgeFin.Sqrt.add_div_le_of_sqrt_le hsPos hle
        have hbound : y.toNat + Nat.sqrt a.toNat + 2 < 2 ^ 256 := by
          have h3 := ProofForgeFin.WordBridge.add_lt_two_pow hlt hs2_255
            (show 255 < 256 from by decide)
          rw [Nat.add_assoc]
          exact h3
        omega
      unfold newtonStep
      exact ProofForgeFin.Sqrt.toNat_newton_word _ _ hsum
    have hP : ∀ b : Nat,
        (Nat.sqrt a.toNat ≤ b ∧ b < 2 ^ 255) →
        (Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat b ∧
          ProofForgeFin.Sqrt.newton a.toNat b < 2 ^ 255) := by
      intro b hb
      obtain ⟨hle, hlt⟩ := hb
      have hle' : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat b :=
        ProofForgeFin.Sqrt.sqrt_le_newton_of_le hle
      have hsum : b + a.toNat / b < 2 ^ 256 := by
        have hadd : b + a.toNat / b ≤ b + Nat.sqrt a.toNat + 2 :=
          ProofForgeFin.Sqrt.add_div_le_of_sqrt_le hsPos hle
        have hbound : b + Nat.sqrt a.toNat + 2 < 2 ^ 256 := by
          have h3 := ProofForgeFin.WordBridge.add_lt_two_pow hlt hs2_255
            (show 255 < 256 from by decide)
          rw [Nat.add_assoc]
          exact h3
        omega
      have hlt' : ProofForgeFin.Sqrt.newton a.toNat b < 2 ^ 255 := by
        have e256 : (2 : Nat) ^ 256 = 2 ^ 255 * 2 := by
          rw [show (256 : Nat) = 255 + 1 from rfl, Nat.pow_succ]
        unfold ProofForgeFin.Sqrt.newton
        have h' : b + a.toNat / b < 2 ^ 255 * 2 := by
          rw [← e256]
          exact hsum
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h'
      exact ⟨hle', hlt'⟩
    have hx : Nat.sqrt a.toNat ≤
          (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat ∧
        (newtonStep a ((1 : U256) <<< (log2 a >>> 1))).toNat < 2 ^ 255 := by
      rw [hr1]
      have hle : Nat.sqrt a.toNat ≤
          ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) :=
        ProofForgeFin.Sqrt.sqrt_le_newton (a := a.toNat) hx0pos
      have hlt : ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))
          < 2 ^ 255 := by
        have e256 : (2 : Nat) ^ 256 = 2 ^ 255 * 2 := by
          rw [show (256 : Nat) = 255 + 1 from rfl, Nat.pow_succ]
        unfold ProofForgeFin.Sqrt.newton
        have h' : 2 ^ (Nat.log2 a.toNat / 2)
            + a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 255 * 2 := by
          rw [← e256]
          exact hsum0
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h'
      exact ⟨hle, hlt⟩
    have hsim6 := ProofForgeFin.WordBridge.iter_map_of_sim
      (iterate (newtonStep a)) (newtonStep a)
      (fun _ => rfl) (fun _ _ => rfl)
      BitVec.toNat (ProofForgeFin.Sqrt.newton a.toNat)
      (fun b => Nat.sqrt a.toNat ≤ b ∧ b < 2 ^ 255)
      hf hP 6 _ hx
    have eIt : iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)) =
        iterate (newtonStep a) 6 (newtonStep a ((1 : U256) <<< (log2 a >>> 1))) := rfl
    have eRep : Nat.repeat (ProofForgeFin.Sqrt.newton a.toNat) 7
          (2 ^ (Nat.log2 a.toNat / 2)) =
        Nat.repeat (ProofForgeFin.Sqrt.newton a.toNat) 6
          (ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) :=
      (ProofForgeFin.WordBridge.repeat_succ' _ 6 _).symm
    have eNR : ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) =
        Nat.repeat (ProofForgeFin.Sqrt.newton a.toNat) 7
          (2 ^ (Nat.log2 a.toNat / 2)) :=
      ProofForgeFin.Sqrt.newtonIter_eq_repeat _ _ _
    have hIterToNat : (iterate (newtonStep a) 7
        ((1 : U256) <<< (log2 a >>> 1))).toNat =
        ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) := by
      rw [eIt, hsim6, hr1, ← eRep, ← eNR]
    rw [h7, hns, toNat_min, ProofForgeFin.WordBridge.toNat_div, hIterToNat]
    exact newtonIter7_min_eq a.toNat hApos hA256

theorem sqrtUp_toNat (a : U256) :
    (sqrtUp sqrt a).toNat =
      Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hsqrt := sqrt_toNat a
  have hss256 : Nat.sqrt a.toNat * Nat.sqrt a.toNat < 2 ^ 256 :=
    ProofForgeFin.Sqrt.mul_self_sqrt_lt_two_pow a.isLt
  have hprod_eq : (sqrt a * sqrt a).toNat
      = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    have h : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
      rw [hsqrt]
      exact hss256
    have e := ProofForgeFin.WordBridge.toNat_mul_of_lt' h
    rw [hsqrt] at e
    exact e
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_toNat_lt_two_pow a (show 256 ≤ 2 * 128 from by decide)
  have hone : (1 : U256).toNat = 1 :=
    ProofForgeFin.WordBridge.toNat_one' (by decide)
  have hzero : (0 : U256).toNat = 0 := ProofForgeFin.WordBridge.toNat_zero'
  unfold sqrtUp
  show ((sqrt a + (if sqrt a * sqrt a < a then (1 : U256) else 0)).toNat = _)
  by_cases hc : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · have hcB : sqrt a * sqrt a < a := by
      have hiff := ProofForgeFin.WordBridge.lt_iff_toNat_lt
        (x := sqrt a * sqrt a) (y := a)
      rw [hprod_eq] at hiff
      exact hiff.mpr hc
    rw [if_pos hcB, if_pos hc]
    have hsadd : Nat.sqrt a.toNat + 1 < 2 ^ 256 := by
      have h128 : (2 : Nat) ^ 128 < 2 ^ 256 :=
        Nat.pow_lt_pow_right (by decide) (by decide)
      omega
    have hsum : (sqrt a).toNat + (1 : U256).toNat < 2 ^ 256 := by
      rw [hone, hsqrt]
      exact hsadd
    have heq := ProofForgeFin.WordBridge.toNat_add_of_lt'
      (x := sqrt a) (y := 1) hsum
    rw [heq, hsqrt, hone]
  · have hcB : ¬ sqrt a * sqrt a < a := by
      have hiff := ProofForgeFin.WordBridge.lt_iff_toNat_lt
        (x := sqrt a * sqrt a) (y := a)
      rw [hprod_eq] at hiff
      exact fun h => hc (hiff.mp h)
    rw [if_neg hcB, if_neg hc]
    have hsum : (sqrt a).toNat + (0 : U256).toNat < 2 ^ 256 := by
      rw [hzero, hsqrt]
      have hs256 : Nat.sqrt a.toNat < 2 ^ 256 :=
        Nat.lt_of_lt_of_le hs128
          (Nat.pow_le_pow_right (by decide) (by decide : 128 ≤ 256))
      omega
    have heq := ProofForgeFin.WordBridge.toNat_add_of_lt'
      (x := sqrt a) (y := 0) hsum
    rw [heq, hsqrt, hzero]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  have h := sqrt_toNat a
  rw [h]
  exact Nat.sqrt_le a.toNat

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  have h := sqrt_toNat a
  rw [h]
  exact Nat.lt_succ_sqrt a.toNat

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  rw [sqrtUp_toNat a]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite a.toNat

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a hpos
  rw [sqrtUp_toNat a] at hpos ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt hpos

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l h
  have hmem := firstMint_eq_some h
  obtain ⟨hprod, hroot, hliq⟩ := hmem
  have h1 : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, toNat_mul_of_lt hprod]
  have heq : l.toNat + 1000 = Nat.sqrt (a0.toNat * a1.toNat) := by omega
  rw [heq]
  exact Nat.sqrt_le _

theorem req_mint_full : MintFull sqrt := by
  intro a0 a1 l h
  have hmem := firstMint_eq_some h
  obtain ⟨hprod, hroot, hliq⟩ := hmem
  have h1 : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, toNat_mul_of_lt hprod]
  have heq : l.toNat + 1000 = Nat.sqrt (a0.toNat * a1.toNat) := by omega
  have e2 : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by omega
  rw [e2]
  exact Nat.lt_succ_sqrt _

theorem req_mint_live : MintLive sqrt := by
  intro a0 a1 hprod hbig
  have h1 : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, toNat_mul_of_lt hprod]
  apply firstMint_isSome hprod
  rw [h1]
  have h1001 : Nat.sqrt (1001 * 1001) = 1001 :=
    ProofForgeFin.Sqrt.sqrt_mul_self 1001
  have hmono : Nat.sqrt (1001 * 1001) ≤ Nat.sqrt (a0.toNat * a1.toNat) :=
    ProofForgeFin.Sqrt.sqrt_le_sqrt hbig
  omega

theorem req_newton_budget : NewtonBudget sqrt := by
  refine ⟨7, by decide, fun a => ?_⟩
  unfold sqrt newtonSqrt
  by_cases h : a = 0
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

end OzSqrt

import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.SqrtIter
import ProofForgeFin.WordBridge
import ProofForgeFin.NatSqrt
namespace OzSqrt
open ProofForgeFin.Sqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem sqrt_toNat (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  unfold sqrt newtonSqrt
  by_cases h0 : a = 0
  · subst h0
    simp only
    show (0 : U256).toNat = Nat.sqrt (0 : U256).toNat
    rw [show (0 : U256).toNat = 0 from rfl, Nat.sqrt_zero]
  · rw [ite_eq_right h0]
    have hA : 0 < a.toNat :=
      (ProofForgeFin.WordBridge.ne_zero_iff_toNat_pos (x := a)).mp h0
    have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
    have hLlt : Nat.log2 a.toNat < 256 :=
      ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
    have hshift1 : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
      rw [ProofForgeFin.WordBridge.toNat_shiftRight_one, hlog]
    have hshlt : (log2 a >>> 1).toNat < 256 := by omega
    have hinit : ((1 : U256) <<< (log2 a >>> 1)).toNat
        = 2 ^ (Nat.log2 a.toNat / 2) := by
      rw [ProofForgeFin.WordBridge.toNat_one_shiftLeft_bv (w := 256) (v := 256) hshlt, hshift1]
    have hn0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.pow_pos (by decide)
    have hn0le : 2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat :=
      two_pow_half_log2_le_sqrt hA
    have hlt2 : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
      sqrt_lt_two_mul_two_pow_half_log2 a.toNat
    have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
      sqrt_toNat_lt_two_pow (w := 256) (k := 128) a (by decide)
    have hn0le127 : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 127 := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    have hdiv4 : a.toNat / 2 ^ (Nat.log2 a.toNat / 2)
        < 4 * 2 ^ (Nat.log2 a.toNat / 2) :=
      div_lt_of_sqrt_lt_mul hn0pos hlt2
    have hn1ge : Nat.sqrt a.toNat ≤ newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) :=
      sqrt_le_newton hn0pos
    have hn1lt : newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 := by
      unfold newton
      omega
    have hmem : newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))
        = Nat.sqrt a.toNat ∨
        (newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))
          = Nat.sqrt a.toNat + 1 ∧
          Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 1) ≤ a.toNat) := by
      have h := newtonIter_eq_or_succ_of_lt_two_mul
        (a := a.toNat) (x := 2 ^ (Nat.log2 a.toNat / 2)) (b := 128) (k := 5)
        hn0pos hn0le hlt2 hs128 (by decide) (by decide)
      simpa using h
    have hle_max : ∀ k, newtonIter a.toNat (k + 1) (2 ^ (Nat.log2 a.toNat / 2))
        ≤ max (newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)))
          (Nat.sqrt a.toNat + 1) := by
      intro k
      have e : newtonIter a.toNat (k + 1) (2 ^ (Nat.log2 a.toNat / 2))
          = newtonIter a.toNat k
            (newton a.toNat (2 ^ (Nat.log2 a.toNat / 2))) := by
        rw [newtonIter_succ]
      rw [e]
      exact newtonIter_le_max k hn1ge
    have hiter_lt : ∀ k, newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2))
        < 2 ^ 129 := by
      intro k
      rcases k with _ | m
      · rw [newtonIter_zero]; omega
      · have h := hle_max m
        omega
    have hiter_ge : ∀ k, 0 < k →
        Nat.sqrt a.toNat ≤ newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)) :=
      fun k hk => sqrt_le_newtonIter hn0pos hk
    have hstep : ∀ (w : U256) (x : Nat),
        w.toNat = x → x < 2 ^ 129 →
        x + a.toNat / x < 2 ^ 256 →
        (newtonStep a w).toNat = newton a.toNat x := by
      intro w x hx hxlt hsum
      unfold newtonStep
      have hwd : (a / w).toNat = a.toNat / x := by
        rw [ProofForgeFin.WordBridge.toNat_div, hx]
      have hadd : (w + a / w).toNat = x + a.toNat / x := by
        have h2 := ProofForgeFin.WordBridge.toNat_add_of_lt' (x := w) (y := a / w)
        rw [hx, hwd] at h2
        exact h2 hsum
      rw [ProofForgeFin.WordBridge.toNat_shiftRight_one, hadd]
      rfl
    have hsum0 : 2 ^ (Nat.log2 a.toNat / 2)
        + a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 := by
      omega
    have hsumS : ∀ x, Nat.sqrt a.toNat ≤ x → x < 2 ^ 129 →
        x + a.toNat / x < 2 ^ 256 := by
      intro x hsx hxlt
      have hspos : 0 < Nat.sqrt a.toNat :=
        Nat.lt_of_lt_of_le hn0pos hn0le
      have hle : x + a.toNat / x ≤ x + Nat.sqrt a.toNat + 2 :=
        add_div_le_of_sqrt_le hspos hsx
      omega
    have w0eq : ((1 : U256) <<< (log2 a >>> 1)).toNat
        = 2 ^ (Nat.log2 a.toNat / 2) := hinit
    have hw_succ : ∀ (k : Nat) (w : U256),
        iterate (newtonStep a) (k + 1) w
          = newtonStep a (iterate (newtonStep a) k w) :=
      fun k w => ProofForgeFin.WordBridge.iter_succ_of_eqns
        (fun k x => iterate (newtonStep a) k x) (newtonStep a)
        (fun x => rfl) (fun k x => rfl) k w
    have e1 : (iterate (newtonStep a) 1 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newtonIter a.toNat 1 (2 ^ (Nat.log2 a.toNat / 2)) := by
      rw [hw_succ, newtonIter_succ']
      show (newtonStep a (iterate (newtonStep a) 0 ((1 : U256) <<< (log2 a >>> 1)))).toNat
        = newton a.toNat (newtonIter a.toNat 0 (2 ^ (Nat.log2 a.toNat / 2)))
      rw [show iterate (newtonStep a) 0 ((1 : U256) <<< (log2 a >>> 1))
        = ((1 : U256) <<< (log2 a >>> 1)) from rfl,
        show newtonIter a.toNat 0 (2 ^ (Nat.log2 a.toNat / 2))
          = 2 ^ (Nat.log2 a.toNat / 2) from rfl]
      exact hstep _ _ w0eq (by omega) hsum0
    have e2 : (iterate (newtonStep a) 2 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newtonIter a.toNat 2 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hge : Nat.sqrt a.toNat ≤ newtonIter a.toNat 1 (2 ^ (Nat.log2 a.toNat / 2)) :=
        hiter_ge 1 (by decide)
      have hlt : newtonIter a.toNat 1 (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 :=
        hiter_lt 1
      have hs := hsumS _ hge hlt
      rw [hw_succ 1 _, newtonIter_succ' a.toNat 1 _]
      exact hstep _ _ e1 hlt hs
    have e3 : (iterate (newtonStep a) 3 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newtonIter a.toNat 3 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hge : Nat.sqrt a.toNat ≤ newtonIter a.toNat 2 (2 ^ (Nat.log2 a.toNat / 2)) :=
        hiter_ge 2 (by decide)
      have hlt : newtonIter a.toNat 2 (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 :=
        hiter_lt 2
      have hs := hsumS _ hge hlt
      rw [hw_succ 2 _, newtonIter_succ' a.toNat 2 _]
      exact hstep _ _ e2 hlt hs
    have e4 : (iterate (newtonStep a) 4 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newtonIter a.toNat 4 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hge : Nat.sqrt a.toNat ≤ newtonIter a.toNat 3 (2 ^ (Nat.log2 a.toNat / 2)) :=
        hiter_ge 3 (by decide)
      have hlt : newtonIter a.toNat 3 (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 :=
        hiter_lt 3
      have hs := hsumS _ hge hlt
      rw [hw_succ 3 _, newtonIter_succ' a.toNat 3 _]
      exact hstep _ _ e3 hlt hs
    have e5 : (iterate (newtonStep a) 5 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newtonIter a.toNat 5 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hge : Nat.sqrt a.toNat ≤ newtonIter a.toNat 4 (2 ^ (Nat.log2 a.toNat / 2)) :=
        hiter_ge 4 (by decide)
      have hlt : newtonIter a.toNat 4 (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 :=
        hiter_lt 4
      have hs := hsumS _ hge hlt
      rw [hw_succ 4 _, newtonIter_succ' a.toNat 4 _]
      exact hstep _ _ e4 hlt hs
    have e6 : (iterate (newtonStep a) 6 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newtonIter a.toNat 6 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hge : Nat.sqrt a.toNat ≤ newtonIter a.toNat 5 (2 ^ (Nat.log2 a.toNat / 2)) :=
        hiter_ge 5 (by decide)
      have hlt : newtonIter a.toNat 5 (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 :=
        hiter_lt 5
      have hs := hsumS _ hge hlt
      rw [hw_succ 5 _, newtonIter_succ' a.toNat 5 _]
      exact hstep _ _ e5 hlt hs
    have e7 : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
        = newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) := by
      have hge : Nat.sqrt a.toNat ≤ newtonIter a.toNat 6 (2 ^ (Nat.log2 a.toNat / 2)) :=
        hiter_ge 6 (by decide)
      have hlt : newtonIter a.toNat 6 (2 ^ (Nat.log2 a.toNat / 2)) < 2 ^ 129 :=
        hiter_lt 6
      have hs := hsumS _ hge hlt
      rw [hw_succ 6 _, newtonIter_succ' a.toNat 6 _]
      exact hstep _ _ e6 hlt hs
    have hmin : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat
        = Nat.sqrt a.toNat := by
      rw [toNat_min]
      have hdiv : (a / iterate (newtonStep a) 7
          ((1 : U256) <<< (log2 a >>> 1))).toNat
          = a.toNat / newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) := by
        rw [ProofForgeFin.WordBridge.toNat_div, e7]
      rw [hdiv, e7]
      have hspos : 0 < Nat.sqrt a.toNat :=
        Nat.lt_of_lt_of_le hn0pos hn0le
      have hge7 : Nat.sqrt a.toNat
          ≤ newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) :=
        hiter_ge 7 (by decide)
      have hx0 : 0 < newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) := by
        omega
      have hfin : Nat.min (newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
          (a.toNat / newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
          = Nat.sqrt a.toNat :=
        min_div_eq_sqrt hx0 hmem
      exact hfin
    rw [hmin]

theorem sqrtUp_toNat (a : U256) : (sqrtUp sqrt a).toNat
    = Nat.sqrt a.toNat
      + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  unfold sqrtUp
  have hsq : (sqrt a).toNat = Nat.sqrt a.toNat := sqrt_toNat a
  have hprod_lt : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
    rw [hsq]
    exact Nat.lt_of_le_of_lt (Nat.sqrt_le a.toNat) a.isLt
  have hmul : (sqrt a * sqrt a).toNat
      = (sqrt a).toNat * (sqrt a).toNat := by
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt hprod_lt
  have hone : (1 : U256).toNat = 1 :=
    ProofForgeFin.WordBridge.toNat_one' (by decide)
  by_cases hcB : sqrt a * sqrt a < a
  · have hcN : (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
      have := BitVec.lt_def.mp hcB
      rwa [hmul] at this
    rw [hsq] at hcN
    have heq : (if sqrt a * sqrt a < a then (1 : U256) else 0) = 1 :=
      if_pos hcB
    have hsqrt_lt : (sqrt a).toNat < 2 ^ 128 := by
      rw [hsq]; exact sqrt_toNat_lt_two_pow (w := 256) (k := 128) a (by decide)
    have hadd : (sqrt a + (if sqrt a * sqrt a < a then 1 else 0)).toNat
        = (sqrt a).toNat + 1 := by
      rw [heq]
      have h2 := ProofForgeFin.WordBridge.toNat_add_of_lt'
        (x := sqrt a) (y := (1 : U256)) (by omega)
      rwa [hone] at h2
    rw [hadd, hsq]
    simp [hcN]
  · have hcN : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      intro hlt
      apply hcB
      apply BitVec.lt_def.mpr
      rw [hmul, hsq]
      exact hlt
    have heq : (if sqrt a * sqrt a < a then (1 : U256) else 0) = 0 :=
      if_neg hcB
    have hadd : (sqrt a + (if sqrt a * sqrt a < a then 1 else 0)).toNat
        = (sqrt a).toNat := by
      rw [heq]
      simp
    rw [hadd, hsq]
    simp [hcN]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  rw [sqrt_toNat]
  exact Nat.sqrt_le a.toNat

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  rw [sqrt_toNat]
  exact Nat.lt_succ_sqrt a.toNat

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  rw [sqrtUp_toNat]
  exact le_mul_self_sqrt_add_ite a.toNat

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a hpos
  rw [sqrtUp_toNat] at hpos ⊢
  exact sqrt_add_ite_sub_one_mul_self_lt hpos

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l h
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some h
  have hsqrt : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, toNat_mul_of_lt hprod]
  have hle : (l.toNat + 1000) * (l.toNat + 1000)
      ≤ (sqrt (a0 * a1)).toNat * (sqrt (a0 * a1)).toNat :=
    Nat.le_of_eq (by rw [hliq])
  rw [hsqrt] at hle
  exact Nat.le_trans hle (Nat.sqrt_le _)

theorem req_mint_full : MintFull sqrt := by
  intro a0 a1 l h
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some h
  have hsqrt : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, toNat_mul_of_lt hprod]
  have heqBase : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by
    omega
  rw [heqBase]
  exact Nat.lt_succ_sqrt _

theorem req_mint_live : MintLive sqrt := by
  intro a0 a1 hprod hbig
  apply firstMint_isSome hprod
  have hsqrt : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_toNat, toNat_mul_of_lt hprod]
  rw [hsqrt]
  have hle : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) := by
    apply le_sqrt_of_mul_self_le
    omega
  omega

theorem req_newton_budget : NewtonBudget sqrt := by
  exact ⟨7, by decide, fun a => rfl⟩

end OzSqrt

import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin
/-!
Fixed square-root routine: OpenZeppelin `Math.sqrt` with all seven Newton steps,
followed by the final `min`:

```
if (a == 0) { return 0; }
result = 1 << (log2(a) >> 1);
result = (result + a / result) >> 1;   // seven times
return min(result, a / result);
```
-/
namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

/-- The word routine returns the floor of the square root on every input. -/
theorem sqrt_val (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases h0 : a = 0
  · subst h0
    have hif : sqrt (0 : U256) = 0 := by unfold sqrt newtonSqrt; rw [if_pos rfl]
    have hz0 : (0 : U256).toNat = 0 := by decide
    rw [hif, hz0]
    exact Nat.sqrt_zero.symm
  · have hz0 : (0 : U256).toNat = 0 := by decide
    have hApos : 0 < a.toNat := Nat.pos_of_ne_zero (fun hz =>
      h0 (BitVec.toNat_eq.mpr (by rw [hz, hz0])))
    have hA : a.toNat < 2 ^ 256 := a.isLt
    have hL256 : Nat.log2 a.toNat < 256 := Nat.log2_lt_of_lt_pow (Nat.ne_of_gt hApos) hA
    have h2pos : (0 : Nat) < 2 := by decide
    generalize hx0def : 2 ^ (Nat.log2 a.toNat / 2) = x0
    generalize hw0def : ((1 : U256) <<< (log2 a >>> 1)) = w0
    have hL2 : Nat.log2 a.toNat / 2 ≤ 127 := by omega
    have hshr : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
      rw [BitVec.toNat_ushiftRight, toNat_log2, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have hw0 : w0.toNat = x0 := by
      rw [← hw0def, BitVec.shiftLeft_eq', hshr]
      have h1 : (1 : U256).toNat = 1 := ProofForgeFin.WordBridge.toNat_one' (by decide)
      have hfit : (1 : U256).toNat * 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 := by
        rw [h1, Nat.one_mul]
        exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hL2)
          (Nat.pow_lt_pow_right (by decide) (by decide))
      rw [ProofForgeFin.toNat_shiftLeft_of_lt _ _ hfit, h1, Nat.one_mul, hx0def]
    have hx0pos : 0 < x0 := by rw [← hx0def]; exact Nat.two_pow_pos _
    have hx0127 : x0 ≤ 2 ^ 127 := by
      rw [← hx0def]; exact Nat.pow_le_pow_right (by decide) hL2
    have hx0lt : x0 < 2 ^ 129 := Nat.lt_of_le_of_lt hx0127
      (Nat.pow_lt_pow_right (by decide) (by decide))
    have hspos : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hApos
    have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
      ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt hA (by decide)
    have hx0le : x0 ≤ Nat.sqrt a.toNat := by
      rw [← hx0def]; exact ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hApos
    have hs2 : Nat.sqrt a.toNat < 2 * x0 := by
      rw [← hx0def]; exact ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 a.toNat
    have hA1 : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) := Nat.lt_log2_self
    have hLe : Nat.log2 a.toNat + 1 ≤ 129 + Nat.log2 a.toNat / 2 := by omega
    have hPow : 2 ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ 129 * x0 := by
      rw [← hx0def, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) hLe
    have hAdiv : a.toNat / x0 < 2 ^ 129 :=
      (Nat.div_lt_iff_lt_mul hx0pos).mpr (Nat.lt_of_lt_of_le hA1 hPow)
    have hy1 : ProofForgeFin.Sqrt.newton a.toNat x0 < 2 ^ 129 := by
      have hsum0 : x0 + a.toNat / x0 < 2 ^ 129 * 2 := by omega
      unfold ProofForgeFin.Sqrt.newton
      exact (Nat.div_lt_iff_lt_mul h2pos).mpr hsum0
    have p128 : (2 : Nat) ^ 128 ≤ 2 ^ 129 := Nat.pow_le_pow_right (by decide) (by decide)
    have p129 : (2 : Nat) ^ 129 + 2 ^ 129 = 2 ^ 130 := by
      rw [show (130 : Nat) = 129 + 1 from rfl, Nat.pow_succ]
    have p130 : (2 : Nat) ^ 130 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by decide)
    have hsim : ∀ j : Nat, (iterate (newtonStep a) j w0).toNat
        = ProofForgeFin.Sqrt.newtonIter a.toNat j x0
        ∧ ProofForgeFin.Sqrt.newtonIter a.toNat j x0 < 2 ^ 129
        ∧ (0 < j → Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newtonIter a.toNat j x0) := by
      intro j
      induction j with
      | zero =>
        refine ⟨?_, ?_, ?_⟩
        · exact hw0
        · exact hx0lt
        · intro h; omega
      | succ j ih =>
        obtain ⟨ih1, ih2, ih3⟩ := ih
        have hsum : ProofForgeFin.Sqrt.newtonIter a.toNat j x0
            + a.toNat / ProofForgeFin.Sqrt.newtonIter a.toNat j x0 < 2 ^ 256 := by
          by_cases hj : j = 0
          · subst hj
            rw [ProofForgeFin.Sqrt.newtonIter_zero]
            omega
          · have hge : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newtonIter a.toNat j x0 :=
              ih3 (Nat.pos_of_ne_zero hj)
            have hadd := ProofForgeFin.Sqrt.add_div_le_of_sqrt_le hspos hge
            omega
        have hstep : (newtonStep a (iterate (newtonStep a) j w0)).toNat
            = ProofForgeFin.Sqrt.newton a.toNat (iterate (newtonStep a) j w0).toNat := by
          unfold newtonStep
          exact ProofForgeFin.Sqrt.toNat_newton_word a (iterate (newtonStep a) j w0)
            (by rw [ih1]; exact hsum)
        have hword : (iterate (newtonStep a) (j + 1) w0).toNat
            = ProofForgeFin.Sqrt.newton a.toNat (iterate (newtonStep a) j w0).toNat := by
          have e := ProofForgeFin.WordBridge.iter_succ_of_eqns (iterate (newtonStep a))
            (newtonStep a) (fun x => rfl) (fun k x => rfl) j w0
          rw [e]
          exact hstep
        have hnat : ProofForgeFin.Sqrt.newtonIter a.toNat (j + 1) x0
            = ProofForgeFin.Sqrt.newton a.toNat (ProofForgeFin.Sqrt.newtonIter a.toNat j x0) :=
          ProofForgeFin.Sqrt.newtonIter_succ' a.toNat j x0
        refine ⟨?_, ?_, ?_⟩
        · rw [hword, ih1, hnat]
        · rw [hnat]
          by_cases hj : j = 0
          · subst hj
            rw [ProofForgeFin.Sqrt.newtonIter_zero]
            exact hy1
          · have hge : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newtonIter a.toNat j x0 :=
              ih3 (Nat.pos_of_ne_zero hj)
            have hadd := ProofForgeFin.Sqrt.add_div_le_of_sqrt_le hspos hge
            unfold ProofForgeFin.Sqrt.newton
            exact (Nat.div_lt_iff_lt_mul h2pos).mpr (by omega)
        · intro _
          exact ProofForgeFin.Sqrt.sqrt_le_newtonIter hx0pos (by omega)
    have h7 := (hsim 7).1
    have hNat7 : ProofForgeFin.Sqrt.newtonIter a.toNat 7 x0 = Nat.sqrt a.toNat
        ∨ (ProofForgeFin.Sqrt.newtonIter a.toNat 7 x0 = Nat.sqrt a.toNat + 1
          ∧ Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 1) ≤ a.toNat) :=
      ProofForgeFin.Sqrt.newtonIter_eq_or_succ_of_lt_two_mul (k := 5)
        hx0pos hx0le hs2 hs128 (by decide) (by decide)
    have hpos7 : 0 < ProofForgeFin.Sqrt.newtonIter a.toNat 7 x0 :=
      ProofForgeFin.Sqrt.newtonIter_pos 7 hspos hx0pos
    have hmin : Nat.min (ProofForgeFin.Sqrt.newtonIter a.toNat 7 x0)
        (a.toNat / ProofForgeFin.Sqrt.newtonIter a.toNat 7 x0) = Nat.sqrt a.toNat :=
      ProofForgeFin.Sqrt.min_div_eq_sqrt hpos7 hNat7
    have hsqrt_eq : sqrt a
        = min (iterate (newtonStep a) 7 w0) (a / iterate (newtonStep a) 7 w0) := by
      rw [← hw0def]
      unfold sqrt newtonSqrt
      rw [if_neg h0]
    calc (sqrt a).toNat
        = (min (iterate (newtonStep a) 7 w0) (a / iterate (newtonStep a) 7 w0)).toNat := by
          rw [hsqrt_eq]
      _ = Nat.sqrt a.toNat := by
          rw [toNat_min, BitVec.toNat_udiv, h7]
          exact hmin

/-- The rounded-up root on values. -/
theorem sqrtUp_val (a : U256) : (sqrtUp sqrt a).toNat
    = Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hsqrt : (sqrt a).toNat = Nat.sqrt a.toNat := sqrt_val a
  have hmul : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    have hlt : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
      rw [hsqrt]
      exact Nat.lt_of_le_of_lt (Nat.sqrt_le _) a.isLt
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hlt, hsqrt]
  have h1 : (1 : U256).toNat = 1 := ProofForgeFin.WordBridge.toNat_one' (by decide)
  have hz0 : (0 : U256).toNat = 0 := by decide
  have hs128 : Nat.sqrt a.toNat < 2 ^ 128 :=
    ProofForgeFin.Sqrt.sqrt_toNat_lt_two_pow a (by decide)
  have h128 : (2 : Nat) ^ 128 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by decide)
  simp only [sqrtUp]
  by_cases hc : sqrt a * sqrt a < a
  · rw [if_pos hc]
    have hc'' := BitVec.lt_def.mp hc
    rw [hmul] at hc''
    rw [if_pos hc'']
    have hadd : (sqrt a + 1).toNat = (sqrt a).toNat + 1 := by
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by rw [hsqrt]; omega)]
    rw [hadd, hsqrt]
  · rw [if_neg hc]
    have hc'' : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      intro hlt
      apply hc
      rw [BitVec.lt_def, hmul]
      exact hlt
    rw [if_neg hc'']
    have hadd : (sqrt a + 0).toNat = (sqrt a).toNat + 0 := by
      rw [BitVec.toNat_add, hz0, Nat.mod_eq_of_lt (by rw [hsqrt]; omega)]
    rw [hadd, hsqrt]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  have h := sqrt_val a
  rw [h]
  exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  have h := sqrt_val a
  rw [h]
  exact Nat.lt_succ_sqrt _

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  have h := sqrtUp_val a
  rw [h]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite a.toNat

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a ha
  have h := sqrtUp_val a
  rw [h] at ha ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt ha

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l hl
  have h := firstMint_eq_some hl
  obtain ⟨hprod, hroot, hliq⟩ := h
  have hs := req_sqrt_not_above (a0 * a1)
  have hmul := toNat_mul_of_lt hprod
  rw [← hliq, hmul] at hs
  exact hs

theorem req_mint_full : MintFull sqrt := by
  intro a0 a1 l hl
  have h := firstMint_eq_some hl
  obtain ⟨hprod, hroot, hliq⟩ := h
  have hs := req_sqrt_not_below (a0 * a1)
  have hmul := toNat_mul_of_lt hprod
  rw [hmul, ← hliq] at hs
  have heq : l.toNat + 1000 + 1 = l.toNat + 1001 := by omega
  rw [heq] at hs
  exact hs

theorem req_mint_live : MintLive sqrt := by
  intro a0 a1 hprod hbig
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hsqrt : (sqrt (a0 * a1)).toNat = Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [sqrt_val, hmul]
  exact firstMint_isSome hprod (by
    rw [hsqrt]
    have hle : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) :=
      ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le hbig
    omega)

theorem req_newton_budget : NewtonBudget sqrt := ⟨7, Nat.le_refl 7, fun _ => rfl⟩

end OzSqrt

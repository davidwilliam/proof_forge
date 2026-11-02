import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.SqrtIter
import ProofForgeFin.NatSqrt
import ProofForgeFin.WordBridge
import ProofForgeFin.Evm.Bits

namespace OzSqrt

open ProofForgeFin.Sqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem log2_lt256 (a : U256) : Nat.log2 a.toNat < 256 := by
  by_cases h0 : a.toNat = 0
  · rw [h0]; decide
  · exact Nat.log2_lt_of_lt_pow h0 a.isLt

theorem init_toNat (a : U256) :
    (((1 : U256) <<< (log2 a >>> (1 : Nat))).toNat) = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hinner : ((log2 a >>> (1 : Nat)).toNat) = Nat.log2 a.toNat / 2 := by
    rw [ProofForgeFin.WordBridge.toNat_shiftRight, toNat_log2]
  have hL2 : Nat.log2 a.toNat / 2 < 256 := by
    have hL := log2_lt256 a
    omega
  rw [ProofForgeFin.WordBridge.shiftLeft_bv_eq]
  rw [hinner]
  exact ProofForgeFin.Evm.toNat_one_shiftLeft hL2

theorem x0_le127 (a : U256) : 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 127 := by
  apply Nat.pow_le_pow_right (by decide)
  have hL := log2_lt256 a
  omega

theorem s_lt128 (a : U256) : Nat.sqrt a.toNat < 2 ^ 128 :=
  ProofForgeFin.Sqrt.sqrt_lt_two_pow_of_lt a.isLt (by decide)

theorem nat_N1_le (a : U256) (_hpos : 0 < a.toNat) :
    ProofForgeFin.Sqrt.newton a.toNat (2 ^ (Nat.log2 a.toNat / 2)) ≤ 2 ^ 129 := by
  have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
  have hs_lt : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
    ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 _
  have hdiv : a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 4 * 2 ^ (Nat.log2 a.toNat / 2) := by
    have h := ProofForgeFin.Sqrt.div_lt_of_sqrt_lt_mul (a := a.toNat)
      (x := 2 ^ (Nat.log2 a.toNat / 2)) (c := 2) hx0pos hs_lt
    have e : 2 * 2 * 2 ^ (Nat.log2 a.toNat / 2) = 4 * 2 ^ (Nat.log2 a.toNat / 2) := by grind
    omega
  have hx0 := x0_le127 a
  have h4le : 4 * 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 129 := by
    have h2 : (2 : Nat) ^ 2 = 4 := by decide
    have h129 : (129 : Nat) = 127 + 2 := by omega
    have hmon : 4 * 2 ^ (Nat.log2 a.toNat / 2) ≤ 4 * 2 ^ 127 :=
      Nat.mul_le_mul_left 4 hx0
    have heq : 4 * 2 ^ (127 : Nat) = 2 ^ 129 := by
      rw [h129, Nat.pow_add, h2, Nat.mul_comm]
    omega
  unfold ProofForgeFin.Sqrt.newton
  have h129s : (2 : Nat) ^ 129 * 2 = 2 ^ 130 := by
    have h130 : (130 : Nat) = 129 + 1 := by omega
    rw [h130, Nat.pow_succ]
  omega

theorem nat_props (a : U256) (hpos : 0 < a.toNat) (k : Nat) :
    ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)) ≤ 2 ^ 129 ∧
    (1 ≤ k → Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2))) := by
  have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
  have hN1_le := nat_N1_le a hpos
  induction k with
  | zero =>
    refine ⟨Nat.le_trans (x0_le127 a) (Nat.pow_le_pow_right (by decide) (by omega)), by omega⟩
  | succ k ih =>
    obtain ⟨ih_le, ih_ge⟩ := ih
    constructor
    · by_cases hk0 : k = 0
      · subst hk0
        rw [ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_zero]
        exact hN1_le
      · have h1k : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hs_le := ih_ge h1k
        have hstep : ProofForgeFin.Sqrt.newtonIter a.toNat (k + 1) (2 ^ (Nat.log2 a.toNat / 2)) =
            ProofForgeFin.Sqrt.newton a.toNat
              (ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2))) := by
          rw [ProofForgeFin.Sqrt.newtonIter_succ']
        rw [hstep]
        have hle := ProofForgeFin.Sqrt.newton_le_max hs_le
        have hs128 := s_lt128 a
        have h128_129 : (2 : Nat) ^ 128 ≤ 2 ^ 129 :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hs129 : Nat.sqrt a.toNat + 1 ≤ 2 ^ 129 := by omega
        have hmax : max (ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)))
            (Nat.sqrt a.toNat + 1) ≤ 2 ^ 129 := Nat.max_le.mpr ⟨ih_le, hs129⟩
        exact Nat.le_trans hle hmax
    · intro _
      by_cases hk0 : k = 0
      · subst hk0
        rw [ProofForgeFin.Sqrt.newtonIter_succ', ProofForgeFin.Sqrt.newtonIter_zero]
        exact ProofForgeFin.Sqrt.sqrt_le_newton hx0pos
      · have h1k : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hs_le := ih_ge h1k
        have hstep : ProofForgeFin.Sqrt.newtonIter a.toNat (k + 1) (2 ^ (Nat.log2 a.toNat / 2)) =
            ProofForgeFin.Sqrt.newton a.toNat
              (ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2))) := by
          rw [ProofForgeFin.Sqrt.newtonIter_succ']
        rw [hstep]
        exact ProofForgeFin.Sqrt.sqrt_le_newton_of_le hs_le

theorem nat_all_le (a : U256) (hpos : 0 < a.toNat) (k : Nat) :
    ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)) ≤ 2 ^ 129 :=
  (nat_props a hpos k).1

theorem nat_ge (a : U256) (hpos : 0 < a.toNat) (k : Nat) (hk : 1 ≤ k) :
    Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)) :=
  (nat_props a hpos k).2 hk

theorem sum_bound0 (a : U256) (_hpos : 0 < a.toNat) :
    2 ^ (Nat.log2 a.toNat / 2) + a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 := by
  have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
  have hs_lt : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
    ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 _
  have hdiv : a.toNat / 2 ^ (Nat.log2 a.toNat / 2) < 4 * 2 ^ (Nat.log2 a.toNat / 2) := by
    have h := ProofForgeFin.Sqrt.div_lt_of_sqrt_lt_mul (a := a.toNat)
      (x := 2 ^ (Nat.log2 a.toNat / 2)) (c := 2) hx0pos hs_lt
    have e : 2 * 2 * 2 ^ (Nat.log2 a.toNat / 2) = 4 * 2 ^ (Nat.log2 a.toNat / 2) := by grind
    omega
  have hx0 := x0_le127 a
  have h130_256 : (2 : Nat) ^ 130 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
  have h4le : 4 * 2 ^ (Nat.log2 a.toNat / 2) ≤ 2 ^ 129 := by
    have h2 : (2 : Nat) ^ 2 = 4 := by decide
    have h129 : (129 : Nat) = 127 + 2 := by omega
    have hmon : 4 * 2 ^ (Nat.log2 a.toNat / 2) ≤ 4 * 2 ^ 127 :=
      Nat.mul_le_mul_left 4 hx0
    have heq : 4 * 2 ^ (127 : Nat) = 2 ^ 129 := by
      rw [h129, Nat.pow_add, h2, Nat.mul_comm]
    omega
  have e130 : (2 : Nat) ^ 130 = 2 ^ 129 + 2 ^ 129 := by
    have h130 : (130 : Nat) = 129 + 1 := by omega
    rw [h130, Nat.pow_succ]
  omega

theorem sum_boundS (a : U256) (hpos : 0 < a.toNat) (N : Nat)
    (hNle : N ≤ 2 ^ 129) (hs_le : Nat.sqrt a.toNat ≤ N) :
    N + a.toNat / N < 2 ^ 256 := by
  have hs_pos : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hpos
  have hs128 := s_lt128 a
  have hle := ProofForgeFin.Sqrt.add_div_le_of_sqrt_le (a := a.toNat) (x := N) hs_pos hs_le
  have h130_256 : (2 : Nat) ^ 130 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
  have e130 : (2 : Nat) ^ 130 = 2 ^ 129 + 2 ^ 129 := by
    have h130 : (130 : Nat) = 129 + 1 := by omega
    rw [h130, Nat.pow_succ]
  have h128_129 : (2 : Nat) ^ 128 ≤ 2 ^ 129 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem iterate_succ' (f : U256 → U256) (k : Nat) (x : U256) :
    iterate f (k + 1) x = f (iterate f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    show iterate f (k + 1) (f x) = f (iterate f (k + 1) x)
    rw [ih]
    rfl

theorem word_eq (a : U256) (hpos : 0 < a.toNat) (k : Nat) :
    ((iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat)))).toNat) =
    ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)) := by
  induction k with
  | zero =>
    rw [OzSqrt.iterate, ProofForgeFin.Sqrt.newtonIter_zero]
    exact init_toNat a
  | succ k ih =>
    have hNle : ProofForgeFin.Sqrt.newtonIter a.toNat k (2 ^ (Nat.log2 a.toNat / 2)) ≤ 2 ^ 129 :=
      nat_all_le a hpos k
    have hsum : (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat)))).toNat +
        a.toNat / (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat)))).toNat < 2 ^ 256 := by
      rw [ih]
      by_cases hk0 : k = 0
      · subst hk0
        rw [ProofForgeFin.Sqrt.newtonIter_zero]
        exact sum_bound0 a hpos
      · have h1k : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hs_le := nat_ge a hpos k h1k
        exact sum_boundS a hpos _ hNle hs_le
    have hstep : iterate (newtonStep a) (k + 1) ((1 : U256) <<< (log2 a >>> (1 : Nat))) =
        newtonStep a (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat)))) :=
      iterate_succ' _ _ _
    rw [hstep]
    have hEq : newtonStep a (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat)))) =
        ((iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat))) +
          a / iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat)))) >>> (1 : Nat)) := rfl
    have hword : ((newtonStep a (iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat))))).toNat) =
        ProofForgeFin.Sqrt.newton a.toNat
          ((iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> (1 : Nat)))).toNat) := by
      rw [hEq, ProofForgeFin.Sqrt.toNat_newton_word _ _ hsum]
    rw [hword, ih]
    rw [ProofForgeFin.Sqrt.newtonIter_succ']

theorem seven_mem (a : U256) (hpos : 0 < a.toNat) :
    ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) = Nat.sqrt a.toNat ∨
    (ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) = Nat.sqrt a.toNat + 1 ∧
      Nat.sqrt a.toNat * (Nat.sqrt a.toNat + 1) ≤ a.toNat) := by
  have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.two_pow_pos _
  have hx0_le_s : 2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat :=
    ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hpos
  have hs_lt : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
    ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 _
  have hs128 := s_lt128 a
  have h := ProofForgeFin.Sqrt.newtonIter_eq_or_succ_of_lt_two_mul (a := a.toNat)
    (x := 2 ^ (Nat.log2 a.toNat / 2)) (b := 128) (k := 5)
    hx0pos hx0_le_s hs_lt hs128 (by decide) (by decide)
  simpa [show (5 : Nat) + 2 = 7 by decide] using h

theorem toNat_sqrt (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  unfold sqrt newtonSqrt
  by_cases ha0 : a = 0
  · subst ha0
    simp [Nat.sqrt_zero]
  · have hpos : 0 < a.toNat := by
      by_cases h : a.toNat = 0
      · exact absurd (BitVec.eq_of_toNat_eq h) ha0
      · omega
    rw [ite_eq_right ha0]
    have hs_pos : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hpos
    have hW7 := word_eq a hpos 7
    have hmem := seven_mem a hpos
    have hmin_nat := ProofForgeFin.Sqrt.min_div_eq_sqrt (a := a.toNat)
      (x := ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
      (by
        have hNpos : 0 < ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)) :=
          Nat.lt_of_lt_of_le hs_pos (nat_ge a hpos 7 (by omega))
        exact hNpos) hmem
    have hU2 : (let result := iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat)));
        min result (a / result)) =
        min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat))))
          (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat)))) := rfl
    rw [hU2]
    have hmin_word : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat))))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat))))).toNat =
        Nat.min ((iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat)))).toNat)
          (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat)))).toNat) := by
      rw [toNat_min, BitVec.toNat_udiv]
    have hmin_word2 : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat))))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> (1 : Nat))))).toNat =
        Nat.min (ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
          (a.toNat / ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))) := by
      rw [hmin_word, hW7]
    rw [hmin_word2]
    exact hmin_nat

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  have h := toNat_sqrt a
  rw [h]
  exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  have h := toNat_sqrt a
  rw [h]
  exact Nat.lt_succ_sqrt _

theorem sqrtUp_toNat (a : U256) :
    ((sqrtUp sqrt a).toNat) = Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hU : sqrtUp sqrt a = sqrt a + (if sqrt a * sqrt a < a then 1 else 0) := rfl
  rw [hU]
  have hs := toNat_sqrt a
  have hrr : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    have hle : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
      rw [hs]
      exact Nat.lt_of_le_of_lt (Nat.sqrt_le _) a.isLt
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hle, hs]
  by_cases hc : sqrt a * sqrt a < a
  · have hcn : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      have := BitVec.lt_def.mp hc
      rw [hrr] at this
      exact this
    rw [ite_eq_left hc, ite_eq_left hcn]
    have hone : ((1 : U256)).toNat = 1 := rfl
    have hsmall : (sqrt a).toNat + (1 : U256).toNat < 2 ^ 256 := by
      rw [hone]
      rw [hs]
      have hs128 := s_lt128 a
      have h128_256 : (2 : Nat) ^ 128 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsmall, hs]
    rfl
  · have hcn : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      intro hlt
      exact hc (BitVec.lt_def.mpr (by rw [hrr]; exact hlt))
    rw [ite_eq_right hc, ite_eq_right hcn]
    have hz : ((0 : U256)).toNat = 0 := rfl
    have hsmall : (sqrt a).toNat + ((0 : U256)).toNat < 2 ^ 256 := by
      rw [hz]
      have := a.isLt
      omega
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsmall, hs, hz, Nat.add_zero]

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  have h := sqrtUp_toNat a
  rw [h]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite _

theorem req_sqrt_up_tight  : SqrtUpTight sqrt := by
  intro a hpos
  have h := sqrtUp_toNat a
  rw [h] at hpos ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt hpos

theorem req_mint_backed    : MintBacked sqrt := by
  intro a0 a1 l hl
  have ⟨hprod, hroot, hliq⟩ := firstMint_eq_some hl
  have hs := toNat_sqrt (a0 * a1)
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  rw [hmul] at hs
  have hle : Nat.sqrt (a0.toNat * a1.toNat) * Nat.sqrt (a0.toNat * a1.toNat) ≤ a0.toNat * a1.toNat :=
    Nat.sqrt_le _
  have heq : l.toNat + 1000 = Nat.sqrt (a0.toNat * a1.toNat) := by omega
  rw [heq]
  exact hle

theorem req_mint_full      : MintFull sqrt := by
  intro a0 a1 l hl
  have ⟨hprod, hroot, hliq⟩ := firstMint_eq_some hl
  have hs := toNat_sqrt (a0 * a1)
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  rw [hmul] at hs
  have hlt : a0.toNat * a1.toNat <
      (Nat.sqrt (a0.toNat * a1.toNat) + 1) * (Nat.sqrt (a0.toNat * a1.toNat) + 1) :=
    Nat.lt_succ_sqrt _
  have heq : l.toNat + 1000 = Nat.sqrt (a0.toNat * a1.toNat) := by omega
  have heq2 : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by omega
  rw [heq2]
  exact hlt

theorem req_mint_live      : MintLive sqrt := by
  intro a0 a1 hprod hbig
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat := toNat_mul_of_lt hprod
  have hs := toNat_sqrt (a0 * a1)
  rw [hmul] at hs
  apply firstMint_isSome hprod
  have h1001 : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) := by
    rw [Nat.le_sqrt]
    omega
  omega

theorem req_newton_budget  : NewtonBudget sqrt := by
  exact ⟨7, Nat.le_refl 7, fun a => rfl⟩

end OzSqrt

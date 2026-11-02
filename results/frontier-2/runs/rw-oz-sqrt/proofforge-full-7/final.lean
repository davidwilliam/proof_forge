import OzSqrt.Spec
import OzSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.SqrtIter
import ProofForgeFin.WordBridge
import ProofForgeFin.NatSqrt
namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem iterate_add (f : U256 → U256) (j k : Nat) (x : U256) :
    iterate f (j + k) x = iterate f k (iterate f j x) := by
  induction j generalizing x with
  | zero => simp [iterate]
  | succ j ih =>
    rw [Nat.add_right_comm, iterate, iterate, ih]

theorem iterate_succ_last (f : U256 → U256) (k : Nat) (x : U256) :
    iterate f (k + 1) x = f (iterate f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iterate, ih, iterate]

theorem x0_toNat (a : U256) :
    ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (Nat.log2 a.toNat / 2) := by
  have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
  have hshr : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
    rw [ProofForgeFin.WordBridge.toNat_shiftRight, hlog]
  have hlt : (log2 a >>> 1).toNat < 256 := by
    rw [hshr]
    have h1 : Nat.log2 a.toNat < 256 :=
      ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
    omega
  have h1 : ((1 : U256) <<< (log2 a >>> 1)).toNat = 2 ^ (log2 a >>> 1).toNat :=
    ProofForgeFin.WordBridge.toNat_one_shiftLeft_bv hlt
  rw [h1, hshr]

theorem x0_le_sqrt (a : U256) (hpos : 0 < a.toNat) :
    2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat :=
  ProofForgeFin.Sqrt.two_pow_half_log2_le_sqrt hpos

theorem sqrt_lt_two_mul_x0 (a : U256) :
    Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
  ProofForgeFin.Sqrt.sqrt_lt_two_mul_two_pow_half_log2 a.toNat

theorem x0_lt_pow (a : U256) : 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 128 := by
  apply Nat.pow_lt_pow_right (by decide)
  have h1 : Nat.log2 a.toNat < 256 :=
    ProofForgeFin.WordBridge.log2_toNat_lt (by decide) a
  omega

theorem sqrt_lt_pow (a : U256) : Nat.sqrt a.toNat < 2 ^ 128 :=
  ProofForgeFin.Sqrt.sqrt_toNat_lt_two_pow a (by decide)

theorem word_first_bound (a : U256) (x0 : Nat)
    (hx0pos : 0 < x0) (hlt2 : Nat.sqrt a.toNat < 2 * x0)
    (hx0b : x0 < 2 ^ 128) :
    x0 + a.toNat / x0 < 2 ^ 256 := by
  have hdiv : a.toNat / x0 < 4 * x0 := by
    have h := ProofForgeFin.Sqrt.div_lt_of_sqrt_lt_mul (a := a.toNat) (x := x0) (c := 2) hx0pos hlt2
    simpa [show (2 : Nat) * 2 * x0 = 4 * x0 by omega] using h
  have h1 : (5 : Nat) * x0 < 5 * 2 ^ 128 := Nat.mul_lt_mul_of_pos_left hx0b (by decide)
  have h2 : (5 : Nat) * 2 ^ 128 < 2 ^ 256 := by decide
  omega

theorem word_first_eq (a : U256) (x0w : U256) (x0 : Nat)
    (hx0 : x0w.toNat = x0)
    (hx0pos : 0 < x0) (hlt2 : Nat.sqrt a.toNat < 2 * x0)
    (hx0b : x0 < 2 ^ 128) :
    (newtonStep a x0w).toNat = ProofForgeFin.Sqrt.newton a.toNat x0 := by
  have hb : x0 + a.toNat / x0 < 2 ^ 256 :=
    word_first_bound a x0 hx0pos hlt2 hx0b
  have hbw : x0w.toNat + a.toNat / x0w.toNat < 2 ^ 256 := by
    rw [hx0]; exact hb
  have h := ProofForgeFin.Sqrt.toNat_newton_word a x0w hbw
  rw [hx0] at h
  exact h

theorem nat_reaches (A x0 : Nat) (hx0pos : 0 < x0)
    (hle : x0 ≤ Nat.sqrt A) (hlt2 : Nat.sqrt A < 2 * x0)
    (hsb : Nat.sqrt A < 2 ^ 128) :
    (ProofForgeFin.Sqrt.newtonIter A 7 x0 = Nat.sqrt A ∨
      (ProofForgeFin.Sqrt.newtonIter A 7 x0 = Nat.sqrt A + 1 ∧
        Nat.sqrt A * (Nat.sqrt A + 1) ≤ A)) := by
  have h7 : (7 : Nat) = 5 + 2 := by decide
  rw [h7]
  exact ProofForgeFin.Sqrt.newtonIter_eq_or_succ_of_lt_two_mul (a := A) (x := x0) (b := 128) (k := 5)
    hx0pos hle hlt2 hsb (by decide) (by decide)

theorem x1_lt (a : U256) (x0 : Nat)
    (hx0pos : 0 < x0) (hle : x0 ≤ Nat.sqrt a.toNat)
    (hlt2 : Nat.sqrt a.toNat < 2 * x0)
    (hsb : Nat.sqrt a.toNat < 2 ^ 128) :
    ProofForgeFin.Sqrt.newton a.toNat x0 < 2 ^ 129 := by
  have herr : ProofForgeFin.Sqrt.newton a.toNat x0 - Nat.sqrt a.toNat ≤
      Nat.sqrt a.toNat / 4 + 2 :=
    ProofForgeFin.Sqrt.newton_sub_sqrt_le_of_lt_two_mul hx0pos hle hlt2
  have hle2 : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat x0 :=
    ProofForgeFin.Sqrt.sqrt_le_newton hx0pos
  omega

theorem word_rest6 (a : U256) (x1w : U256) (x1 : Nat)
    (hx1 : x1w.toNat = x1)
    (hs_le : Nat.sqrt a.toNat ≤ x1)
    (hx1b : x1 < 2 ^ 129)
    (hsb : Nat.sqrt a.toNat < 2 ^ 128)
    (hspos : 0 < Nat.sqrt a.toNat) :
    ∀ k, k ≤ 6 →
      (iterate (newtonStep a) k x1w).toNat =
        ProofForgeFin.Sqrt.newtonIter a.toNat k x1 := by
  have hsim : ∀ (y : U256),
      (Nat.sqrt a.toNat ≤ y.toNat ∧
        y.toNat ≤ max x1 (Nat.sqrt a.toNat + 1)) →
      (newtonStep a y).toNat = ProofForgeFin.Sqrt.newton a.toNat y.toNat := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    have hmaxb : max x1 (Nat.sqrt a.toNat + 1) < 2 ^ 129 :=
      Nat.max_lt.mpr ⟨hx1b, by omega⟩
    have hy129 : y.toNat < 2 ^ 129 := Nat.lt_of_le_of_lt h2 hmaxb
    have hs2129 : Nat.sqrt a.toNat + 2 < 2 ^ 129 := by
      have h128 : (2 : Nat) ^ 128 < 2 ^ 129 :=
        Nat.pow_lt_pow_right (by decide) (by decide)
      omega
    have hbound : y.toNat + Nat.sqrt a.toNat + 2 < 2 ^ 256 := by
      have h := ProofForgeFin.WordBridge.add_lt_two_pow (w := 256) (k := 129)
        hy129 hs2129 (by decide)
      omega
    exact ProofForgeFin.Sqrt.toNat_newton_word_of_sqrt_le (w := 256)
      hspos h1 hbound
  have hpres : ∀ (b : Nat),
      (Nat.sqrt a.toNat ≤ b ∧ b ≤ max x1 (Nat.sqrt a.toNat + 1)) →
      (Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat b ∧
        ProofForgeFin.Sqrt.newton a.toNat b ≤ max x1 (Nat.sqrt a.toNat + 1)) := by
    intro b hb
    obtain ⟨h1, h2⟩ := hb
    constructor
    · exact ProofForgeFin.Sqrt.sqrt_le_newton_of_le h1
    · have h3 := ProofForgeFin.Sqrt.newton_le_max (a := a.toNat) (x := b) h1
      omega
  intro k _
  have hP0 : (Nat.sqrt a.toNat ≤ x1w.toNat ∧
      x1w.toNat ≤ max x1 (Nat.sqrt a.toNat + 1)) := by
    rw [hx1]
    constructor
    · exact hs_le
    · exact Nat.le_max_left _ _
  have hmap := ProofForgeFin.WordBridge.iter_map_of_sim
    (iterate (newtonStep a)) (newtonStep a)
    (fun x => rfl) (fun k x => rfl)
    BitVec.toNat (ProofForgeFin.Sqrt.newton a.toNat)
    (fun b => Nat.sqrt a.toNat ≤ b ∧ b ≤ max x1 (Nat.sqrt a.toNat + 1))
    hsim hpres k x1w hP0
  have hx1rw : x1w.toNat = x1 := hx1
  rw [hx1rw] at hmap
  have hrep : ProofForgeFin.Sqrt.newtonIter a.toNat k x1 =
      Nat.repeat (ProofForgeFin.Sqrt.newton a.toNat) k x1 := by
    rw [ProofForgeFin.Sqrt.newtonIter_eq_repeat]
  rw [hrep]
  exact hmap

theorem word_iter7 (a : U256) (x0w : U256) (x0 : Nat)
    (hx0 : x0w.toNat = x0)
    (hx0pos : 0 < x0) (hle : x0 ≤ Nat.sqrt a.toNat)
    (hlt2 : Nat.sqrt a.toNat < 2 * x0)
    (hx0b : x0 < 2 ^ 128) (hsb : Nat.sqrt a.toNat < 2 ^ 128)
    (hspos : 0 < Nat.sqrt a.toNat) :
    (iterate (newtonStep a) 7 x0w).toNat =
      ProofForgeFin.Sqrt.newtonIter a.toNat 7 x0 := by
  have hfirst : (newtonStep a x0w).toNat = ProofForgeFin.Sqrt.newton a.toNat x0 :=
    word_first_eq a x0w x0 hx0 hx0pos hlt2 hx0b
  have hs_le_x1 : Nat.sqrt a.toNat ≤ ProofForgeFin.Sqrt.newton a.toNat x0 :=
    ProofForgeFin.Sqrt.sqrt_le_newton hx0pos
  have hx1b : ProofForgeFin.Sqrt.newton a.toNat x0 < 2 ^ 129 :=
    x1_lt a x0 hx0pos hle hlt2 hsb
  have hrest : (iterate (newtonStep a) 6 (newtonStep a x0w)).toNat =
      ProofForgeFin.Sqrt.newtonIter a.toNat 6 (ProofForgeFin.Sqrt.newton a.toNat x0) :=
    word_rest6 a (newtonStep a x0w) (ProofForgeFin.Sqrt.newton a.toNat x0)
      hfirst hs_le_x1 hx1b hsb hspos 6 (Nat.le_refl 6)
  have hadd_w : iterate (newtonStep a) 7 x0w =
      iterate (newtonStep a) 6 (newtonStep a x0w) := by
    have h7 : (7 : Nat) = 1 + 6 := by decide
    rw [h7, iterate_add]
    rfl
  have hadd_n : ProofForgeFin.Sqrt.newtonIter a.toNat 7 x0 =
      ProofForgeFin.Sqrt.newtonIter a.toNat 6 (ProofForgeFin.Sqrt.newton a.toNat x0) := by
    have h7 : (7 : Nat) = 6 + 1 := by decide
    rw [h7, ProofForgeFin.Sqrt.newtonIter_succ]
  rw [hadd_w, hadd_n]
  exact hrest

theorem sqrt_toNat (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  by_cases h0 : a = 0
  · subst h0
    have h1 : (sqrt (0 : U256)).toNat = 0 := by
      have e : sqrt (0 : U256) = 0 := by
        unfold sqrt newtonSqrt
        rw [if_pos rfl]
      rw [e]
      exact ProofForgeFin.WordBridge.toNat_zero'
    rw [h1]
    have h2 : (0 : U256).toNat = 0 :=
      ProofForgeFin.WordBridge.toNat_zero'
    rw [h2]
    rfl
  · have hpos : 0 < a.toNat :=
      ProofForgeFin.WordBridge.ne_zero_iff_toNat_pos.mp h0
    have hspos : 0 < Nat.sqrt a.toNat := ProofForgeFin.Sqrt.sqrt_pos hpos
    have hx0def : ((1 : U256) <<< (log2 a >>> 1)).toNat =
        2 ^ (Nat.log2 a.toNat / 2) := x0_toNat a
    have hle : 2 ^ (Nat.log2 a.toNat / 2) ≤ Nat.sqrt a.toNat :=
      x0_le_sqrt a hpos
    have hlt2 : Nat.sqrt a.toNat < 2 * 2 ^ (Nat.log2 a.toNat / 2) :=
      sqrt_lt_two_mul_x0 a
    have hx0b : 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 128 := x0_lt_pow a
    have hsb : Nat.sqrt a.toNat < 2 ^ 128 := sqrt_lt_pow a
    have hx0pos : 0 < 2 ^ (Nat.log2 a.toNat / 2) := Nat.pow_pos (by decide)
    have hword := word_iter7 a ((1 : U256) <<< (log2 a >>> 1))
      (2 ^ (Nat.log2 a.toNat / 2)) hx0def hx0pos hle hlt2 hx0b hsb hspos
    have hnat := nat_reaches a.toNat (2 ^ (Nat.log2 a.toNat / 2))
      hx0pos hle hlt2 hsb
    have hsqrt_eq : sqrt a = min
        (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) := by
      unfold sqrt newtonSqrt
      rw [if_neg h0]
    have hmin_nat : (min
        (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat =
        Nat.min (ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2)))
          (a.toNat / ProofForgeFin.Sqrt.newtonIter a.toNat 7 (2 ^ (Nat.log2 a.toNat / 2))) := by
      have e1 : (min
          (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
          (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat =
          Nat.min
            (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
            (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := by
        rw [toNat_min]
      have e2 : (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat =
          a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
        ProofForgeFin.WordBridge.toNat_div _ _
      rw [e1, e2, hword]
    rw [hsqrt_eq, hmin_nat]
    have hpos_iter : 0 < ProofForgeFin.Sqrt.newtonIter a.toNat 7
        (2 ^ (Nat.log2 a.toNat / 2)) :=
      ProofForgeFin.Sqrt.newtonIter_pos 7 hspos hx0pos
    exact ProofForgeFin.Sqrt.min_div_eq_sqrt hpos_iter hnat

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  rw [sqrt_toNat]
  exact Nat.sqrt_le a.toNat

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro a
  rw [sqrt_toNat]
  exact Nat.lt_succ_sqrt a.toNat

theorem sqrt_sq_lt : ∀ (a : U256),
    (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
  intro a
  have hsq_lt : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by
    rw [sqrt_toNat]
    exact ProofForgeFin.WordBridge.mul_self_lt_two_pow (sqrt_lt_pow a) (by decide)
  have h := toNat_mul_of_lt (a := sqrt a) (b := sqrt a) hsq_lt
  rw [sqrt_toNat] at h
  exact h

theorem sqrtUp_toNat (a : U256) :
    (sqrtUp sqrt a).toNat =
      Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have e : sqrtUp sqrt a = sqrt a + (if sqrt a * sqrt a < a then (1 : U256) else 0) := rfl
  rw [e]
  have hr : (sqrt a).toNat = Nat.sqrt a.toNat := sqrt_toNat a
  have hsq : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat :=
    sqrt_sq_lt a
  have hiff : (sqrt a * sqrt a < a) ↔
      (Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat) := by
    rw [ProofForgeFin.WordBridge.lt_iff_toNat_lt, hsq]
  by_cases hc : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · have hcw : sqrt a * sqrt a < a := hiff.mpr hc
    rw [if_pos hcw, if_pos hc]
    have h1 : ((1 : U256)).toNat = 1 :=
      ProofForgeFin.WordBridge.toNat_one' (by decide)
    have hadd : (sqrt a + 1).toNat = (sqrt a).toNat + 1 := by
      have hlt : (sqrt a).toNat + (1 : U256).toNat < 2 ^ 256 := by
        rw [h1, hr]
        have hsb := sqrt_lt_pow a
        have h256 : (2 : Nat) ^ 128 < 2 ^ 256 :=
          Nat.pow_lt_pow_right (by decide) (by decide)
        omega
      have h := ProofForgeFin.WordBridge.toNat_add_of_lt' hlt
      rw [h1] at h
      exact h
    rw [hadd, hr]
  · have hcwn : ¬ sqrt a * sqrt a < a := fun h => hc (hiff.mp h)
    rw [if_neg hcwn, if_neg hc]
    have h0 : ((0 : U256)).toNat = 0 :=
      ProofForgeFin.WordBridge.toNat_zero'
    have hadd : (sqrt a + 0).toNat = (sqrt a).toNat := by
      have h : sqrt a + 0 = sqrt a := by simp
      rw [h]
    rw [hadd, hr]
    omega

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  rw [sqrtUp_toNat]
  exact ProofForgeFin.Sqrt.le_mul_self_sqrt_add_ite a.toNat

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a hpos
  rw [sqrtUp_toNat] at hpos ⊢
  exact ProofForgeFin.Sqrt.sqrt_add_ite_sub_one_mul_self_lt hpos

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l h
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some h
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat :=
    toNat_mul_of_lt hprod
  rw [sqrt_toNat, hmul] at hliq
  have hle : Nat.sqrt (a0.toNat * a1.toNat) * Nat.sqrt (a0.toNat * a1.toNat) ≤
      a0.toNat * a1.toNat :=
    Nat.sqrt_le _
  rw [hliq]
  exact hle

theorem req_mint_full : MintFull sqrt := by
  intro a0 a1 l h
  obtain ⟨hprod, hroot, hliq⟩ := firstMint_eq_some h
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat :=
    toNat_mul_of_lt hprod
  rw [sqrt_toNat, hmul] at hliq
  have hlt : a0.toNat * a1.toNat <
      (Nat.sqrt (a0.toNat * a1.toNat) + 1) * (Nat.sqrt (a0.toNat * a1.toNat) + 1) := by
    have h0 : (a0 * a1).toNat <
        (Nat.sqrt (a0 * a1).toNat + 1) * (Nat.sqrt (a0 * a1).toNat + 1) :=
      Nat.lt_succ_sqrt _
    rw [hmul] at h0
    exact h0
  have heq : l.toNat + 1001 = Nat.sqrt (a0.toNat * a1.toNat) + 1 := by
    omega
  rw [heq]
  exact hlt

theorem req_mint_live : MintLive sqrt := by
  intro a0 a1 hprod hbig
  have hmul : (a0 * a1).toNat = a0.toNat * a1.toNat :=
    toNat_mul_of_lt hprod
  apply firstMint_isSome hprod
  rw [sqrt_toNat, hmul]
  have hle : 1001 * 1001 ≤ a0.toNat * a1.toNat := hbig
  have h1001 : 1001 ≤ Nat.sqrt (a0.toNat * a1.toNat) :=
    ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le hle
  omega
theorem req_newton_budget : NewtonBudget sqrt :=
  ⟨7, Nat.le_refl 7, fun a => rfl⟩

end OzSqrt

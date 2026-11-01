import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Rounding

namespace VyperSqrt

open ProofForgeFin.Sqrt

/-- The fix of Vyper pull request 4486: after the deployed Babylonian loop, return the smaller
of the last two iterates (they straddle the root once the loop has converged). -/
def minInt (y z : Int) : Int := if y < z then y else z

def sqrt : SqrtFn := vyperSqrtWith minInt

/-! ## The Newton iteration on natural numbers -/

/-- The scaled radicand: raw input `a` stands for `a / 10^10`, so the root sought is
`Nat.sqrt (a * 10^10)`. -/
def NatsN (a : Nat) : Nat := a * 10 ^ 10

/-- The seed `x / 2.0 + 0.5` on raw values. -/
def seedN (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- The Newton iterates from the seed: `Z 0` is the seed, `Z (n+1)` is one Babylonian step. -/
def Z (a : Nat) : Nat → Nat
  | 0 => seedN a
  | n + 1 => newton (NatsN a) (Z a n)

/-- The true root: the floor of the square root of the scaled radicand. -/
def sn (a : Nat) : Nat := Nat.sqrt (NatsN a)

/-- A square in `Int` is non-negative. -/
theorem sqnn (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total a 0 with h | h
  · have h2 : (0 : Int) ≤ -a := by omega
    have h3 := Int.mul_nonneg h2 h2
    rwa [Int.neg_mul_neg] at h3
  · exact Int.mul_nonneg h h

/-- The seed exceeds the root: `(seed + 1)^2` is above `a * 10^10` for every `q = a / 2`. -/
theorem seed_sq_gt_nat (q : Nat) :
    (2 * q + 1) * 10000000000 < (q + 5000000001) * (q + 5000000001) := by
  have h : (2 * (q : Int) + 1) * 10000000000
      < ((q : Int) + 5000000001) * (((q : Int) + 5000000001)) := by
    have e : ((q : Int) + 5000000001) * (((q : Int) + 5000000001))
        = (2 * (q : Int) + 1) * 10000000000
          + ((((q : Int) - 4999999999) * (((q : Int) - 4999999999)) + 10000000000)) := by
      grind
    have h2 : (0 : Int) ≤ ((q : Int) - 4999999999) * (((q : Int) - 4999999999)) :=
      sqnn _
    omega
  have h2 : ((((2 * q + 1) * 10000000000 : Nat)) : Int)
      < (((((q + 5000000001) * (q + 5000000001) : Nat))) : Int) := by
    simp only [Int.natCast_mul, Int.natCast_add]
    exact h
  exact Int.ofNat_lt.mp h2

/-- Cast injectivity for inequality. -/
theorem castinjNe (u v : Nat) (h : (u : Int) ≠ (v : Int)) : u ≠ v :=
  fun c => h (congrArg (fun (n : Nat) => (n : Int)) c)

/-- Folding the choice function into the mapped loop result. -/
theorem mapMin {y z s : Int} (h : minInt y z = s) :
    ((some (y, z)).map (fun p => minInt p.1 p.2)) = some s := congrArg some h

/-- The root is at least `10^5` for positive input: `100000^2 = 10^10 ≤ a * 10^10`. -/
theorem h100k {a : Nat} (ha : 0 < a) : 100000 ≤ sn a := by
  show 100000 ≤ Nat.sqrt (NatsN a)
  apply le_sqrt_of_mul_self_le (m := 100000)
  show 100000 * 100000 ≤ NatsN a
  have h1 : (100000 * 100000 : Nat) = 10 ^ 10 := by decide
  have h2 : (10 ^ 10 : Nat) ≤ a * 10 ^ 10 := by
    have ha1 : 1 ≤ a := ha
    omega
  have hNN : NatsN a = a * 10 ^ 10 := rfl
  omega

/-- The root is positive for positive input. -/
theorem hs_pos {a : Nat} (ha : 0 < a) : 0 < sn a :=
  Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 100000) (h100k ha)

/-- The seed is positive. -/
theorem hseed_pos (a : Nat) : 0 < seedN a := by
  show 0 < a / 2 + 5 * 10 ^ 9
  have h59 : (0 : Nat) < 5 * 10 ^ 9 := by decide
  omega

/-- The seed is above the root. -/
theorem hs_le_seed {a : Nat} (ha : 0 < a) : sn a ≤ seedN a := by
  have hlt : NatsN a < (seedN a + 1) * (seedN a + 1) := by
    have hq : a ≤ 2 * (a / 2) + 1 := by
      have h1 := Nat.div_add_mod a 2
      have h2 := Nat.mod_lt a (by decide : 0 < 2)
      omega
    have hle2 : a * 10000000000 ≤ (2 * (a / 2) + 1) * 10000000000 := by omega
    have hss : seedN a + 1 = (a / 2) + 5000000001 := by
      show a / 2 + 5 * 10 ^ 9 + 1 = _
      have e5 : (5 * 10 ^ 9 : Nat) = 5000000000 := by decide
      omega
    rw [hss]
    exact Nat.lt_of_le_of_lt hle2 (seed_sq_gt_nat (a / 2))
  have h := sqrt_lt_of_lt_mul_self hlt
  have h' : sn a < seedN a + 1 := h
  omega

/-- Every iterate is above the root. -/
theorem hlow {a : Nat} (ha : 0 < a) (n : Nat) : sn a ≤ Z a n := by
  induction n with
  | zero => show sn a ≤ seedN a; exact hs_le_seed ha
  | succ n ih =>
    have hz : 0 < Z a n := by
      have hp := hs_pos ha
      omega
    show sn a ≤ newton (NatsN a) (Z a n)
    exact sqrt_le_newton hz

/-- Every iterate is positive. -/
theorem hposZ {a : Nat} (ha : 0 < a) (n : Nat) : 0 < Z a n := by
  have h1 := hlow ha n
  have h2 := hs_pos ha
  omega

/-- The quotient `N / z` at any iterate above the root is at most `sn + 2`. -/
theorem hdivN {a : Nat} (ha : 0 < a) (n : Nat) : NatsN a / Z a n ≤ sn a + 2 := by
  have hNs : NatsN a ≤ sn a * (sn a + 2) := by
    have h1' : NatsN a < (sn a + 1) * (sn a + 1) := Nat.lt_succ_sqrt _
    have e : (sn a + 1) * (sn a + 1) = sn a * (sn a + 2) + 1 := by grind
    omega
  have h3 : NatsN a / sn a ≤ sn a + 2 := Nat.div_le_of_le_mul hNs
  have h4 : NatsN a / Z a n ≤ NatsN a / sn a :=
    ProofForgeFin.div_anti_right _ (hs_pos ha) (hlow ha n)
  omega

/-- Every iterate stays below `seed + 1`. -/
theorem hup {a : Nat} (ha : 0 < a) (n : Nat) : Z a n ≤ seedN a + 1 := by
  induction n with
  | zero => exact Nat.le_succ _
  | succ n ih =>
    have hd := hdivN ha n
    show (Z a n + NatsN a / Z a n) / 2 ≤ seedN a + 1
    have hle : (Z a n + NatsN a / Z a n) / 2 ≤ ((seedN a + 1) + (sn a + 2)) / 2 :=
      Nat.div_le_div_right (Nat.add_le_add ih hd)
    have hfin : ((seedN a + 1) + (sn a + 2)) / 2 ≤ seedN a + 1 := by
      have hs := hs_le_seed ha
      omega
    exact Nat.le_trans hle hfin

/-- The seed fits in the decimal range. -/
theorem hseedB {a : Nat} (hle : a ≤ 2 ^ 167 - 1) : seedN a ≤ 2 ^ 166 - 1 + 5000000000 := by
  have h1 : a / 2 ≤ 2 ^ 166 - 1 := by
    have h2 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hle
    have h3 : ((2 ^ 167 - 1) / 2 : Nat) = 2 ^ 166 - 1 := by decide
    omega
  show a / 2 + 5 * 10 ^ 9 ≤ _
  have e5 : (5 * 10 ^ 9 : Nat) = 5000000000 := by decide
  omega

/-- The root fits well below the decimal range. -/
theorem hsB {a : Nat} (hle : a ≤ 2 ^ 167 - 1) : sn a < 2 ^ 101 := by
  show Nat.sqrt (NatsN a) < 2 ^ 101
  apply sqrt_lt_of_lt_mul_self
  have hN : a * 10000000000 ≤ (2 ^ 167 - 1) * 10000000000 := by omega
  have h202 : (2 ^ 167 - 1) * 10000000000 < 2 ^ 101 * 2 ^ 101 := by decide
  have e10 : (10 ^ 10 : Nat) = 10000000000 := by decide
  have hNN : NatsN a = a * 10000000000 := by
    show a * 10 ^ 10 = a * 10000000000
    rw [e10]
  omega

/-- Every loop step stays in the decimal range, so decimal division never reverts. -/
theorem hrange {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) (n : Nat) :
    NatsN a / Z a n + Z a n ≤ 2 ^ 167 - 1 := by
  have h1 := hdivN ha n
  have h2 := hup ha n
  have h3 := hseedB hle
  have h4 := hsB hle
  omega

/-- The halving bound: each step at least halves the error, plus one unit for the floors. -/
theorem hhalf {a : Nat} (ha : 0 < a) (n : Nat) :
    Z a (n + 1) - sn a ≤ (Z a n - sn a) / 2 + 1 := by
  show newton (NatsN a) (Z a n) - sn a ≤ (Z a n - sn a) / 2 + 1
  exact newton_sub_sqrt_le_half (hposZ ha n) (hlow ha n)

/-- Exponential majorant: after `n` halvings the error is below `2^(167-n) + 2`. -/
theorem hmaj {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    ∀ (n : Nat), n ≤ 167 → Z a n - sn a ≤ 2 ^ (167 - n) + 2 := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : Z a 0 = seedN a := rfl
    have hs := hseedB hle
    have hse : seedN a ≤ 2 ^ 167 := by omega
    omega
  | succ n ih =>
    intro h
    have hn : n ≤ 167 := by omega
    have e := ih hn
    have h1 := hhalf ha n
    have hnn : 167 - n = (167 - (n + 1)) + 1 := by omega
    rw [hnn, Nat.pow_succ] at e
    omega

/-- After 167 halvings the error is at most 3. -/
theorem h167 {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) : Z a 167 - sn a ≤ 3 := by
  have h := hmaj ha hle 167 (Nat.le_refl _)
  have e0 : (167 : Nat) - 167 = 0 := by omega
  rw [e0] at h
  exact h

/-- One quadratic step later the iterate is the root or the root plus one. -/
theorem h168 {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    Z a 168 = sn a ∨ Z a 168 = sn a + 1 := by
  have hleZ : sn a ≤ Z a 167 := hlow ha 167
  have h167' := h167 ha hle
  have hpos167 := hposZ ha 167
  have h100 := h100k ha
  have hs' : newton (NatsN a) (Z a 167) - sn a ≤ (Z a 167 - sn a) * (Z a 167 - sn a) / (2 * sn a) + 1 :=
    newton_sub_sqrt_le_sq_div (hs_pos ha) hleZ
  have hsq : (Z a 167 - sn a) * (Z a 167 - sn a) ≤ 9 :=
    Nat.mul_le_mul h167' h167'
  have hdiv : (Z a 167 - sn a) * (Z a 167 - sn a) / (2 * sn a) = 0 :=
    Nat.div_eq_of_lt (by omega)
  have hstep : newton (NatsN a) (Z a 167) - sn a ≤ 1 := by omega
  have hge : sn a ≤ newton (NatsN a) (Z a 167) := sqrt_le_newton hpos167
  have e168 : Z a 168 = newton (NatsN a) (Z a 167) := rfl
  have hdiff : newton (NatsN a) (Z a 167) - sn a = 0
      ∨ newton (NatsN a) (Z a 167) - sn a = 1 := by
    omega
  rcases hdiff with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- From the root or the root plus one, one step stays there. -/
theorem hstep_mem {a : Nat} (ha : 0 < a) (x : Nat) (hx : 0 < x)
    (h1 : sn a ≤ x) (h2 : x ≤ sn a + 1) :
    newton (NatsN a) x = sn a ∨ newton (NatsN a) x = sn a + 1 := by
  have hm := newton_of_mem (a := NatsN a) (x := x) hx h1 h2
  rcases hm with h' | ⟨rfl, h', -⟩
  · exact Or.inl h'
  · exact Or.inr h'

/-- From step 168 on, every iterate is the root or the root plus one. -/
theorem hstab {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) (n : Nat) (hn : 168 ≤ n) :
    Z a n = sn a ∨ Z a n = sn a + 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero =>
    show Z a (168 + 0) = sn a ∨ Z a (168 + 0) = sn a + 1
    exact h168 ha hle
  | succ d ih =>
    have e : 168 + (d + 1) = (168 + d) + 1 := by omega
    show Z a (168 + (d + 1)) = sn a ∨ Z a (168 + (d + 1)) = sn a + 1
    rw [e]
    show newton (NatsN a) (Z a (168 + d)) = sn a
      ∨ newton (NatsN a) (Z a (168 + d)) = sn a + 1
    have ih' : Z a (168 + d) = sn a ∨ Z a (168 + d) = sn a + 1 := ih (by omega)
    exact hstep_mem ha _ (hposZ ha _) (hlow ha _)
      (by rcases ih' with h | h <;> omega)

/-- The deployed loop follows the Newton iterates; its last two iterates straddle the root,
so the smaller one is the root. -/
theorem hloop {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    ∀ (k m : Nat), m + k = 255 →
    ((loop (a : Int) k (Z a m : Int) (Z a (m + 1) : Int)).map
      (fun p => minInt p.1 p.2)) = some (sn a : Int) := by
  intro k
  induction k with
  | zero =>
    intro m hkm
    have hm : m = 255 := by omega
    subst hm
    show ((some ((Z a 255 : Int), (Z a 256 : Int))).map
      (fun p => minInt p.1 p.2)) = some (sn a : Int)
    apply mapMin
    have s255 := hstab ha hle 255 (by omega)
    have s256 := hstab ha hle 256 (by omega)
    have hle256 : (sn a : Int) ≤ (Z a 256 : Int) :=
      Int.ofNat_le.mpr (hlow ha 256)
    have esucc : ((sn a + 1 : Nat) : Int) = (sn a : Int) + 1 := by
      simp only [Int.natCast_add]
      rfl
    have hlt1 : (sn a : Int) < ((sn a + 1 : Nat) : Int) := by omega
    have h256newt : Z a 256 = newton (NatsN a) (Z a 255) := rfl
    rcases s255 with h255 | h255 <;> rcases s256 with h256 | h256
    · rw [h255]
      unfold minInt
      by_cases hlt : (sn a : Int) < (Z a 256 : Int)
      · rw [if_pos hlt]
      · have hzz : (Z a 256 : Int) = (sn a : Int) := by omega
        rw [if_neg hlt, hzz]
    · rw [h255, h256]
      unfold minInt
      rw [if_pos hlt1]
    · rw [h255, h256]
      unfold minInt
      have hnlt : ¬ ((sn a + 1 : Nat) : Int) < (sn a : Int) := by omega
      rw [if_neg hnlt]
    · have h256' : Z a 256 = sn a := by
        rw [h256newt, h255]
        have hm := newton_of_mem (a := NatsN a) (x := sn a + 1)
          (by have h0 := hs_pos ha; omega)
          (show sn a ≤ sn a + 1 from by omega) (Nat.le_refl _)
        rcases hm with h' | ⟨hc, -, -⟩
        · exact h'
        · have hc' : sn a + 1 = sn a := hc
          omega
      have hc : sn a + 1 = sn a := by omega
      omega
  | succ k ih =>
    intro m hkm
    have hk : m + 1 + k = 255 := by omega
    have hzpos : 0 < Z a (m + 1) := hposZ ha _
    have hrg := hrange ha hle (m + 1)
    by_cases heq : (Z a (m + 1) : Int) = (Z a m : Int)
    · have hNat : Z a (m + 1) = Z a m := Int.ofNat.inj heq
      have hfix : newton (NatsN a) (Z a m) = Z a m := by
        have e : Z a (m + 1) = newton (NatsN a) (Z a m) := rfl
        omega
      have hsm : Z a m = sn a := eq_sqrt_of_newton_eq_self (hposZ ha m) hfix
      have estop : loop (a : Int) (k + 1) (Z a m : Int) (Z a (m + 1) : Int)
          = some ((Z a m : Int), (Z a m : Int)) := by
        rw [heq]
        exact loop_stop _ _ _
      rw [estop]
      exact mapMin (by rw [hsm]; unfold minInt; rw [if_neg (by omega)])
    · have hne : Z a (m + 1) ≠ Z a m := castinjNe _ _ heq
      have estep := loop_step (a := a) (y := Z a m) (z := Z a (m + 1)) k hzpos hne hrg
      have eZ : ((a * 10 ^ 10 / Z a (m + 1) + Z a (m + 1)) / 2 : Nat)
          = Z a (m + 1 + 1) := by
        show (a * 10 ^ 10 / Z a (m + 1) + Z a (m + 1)) / 2
          = newton (NatsN a) (Z a (m + 1))
        simp only [newton, NatsN]
        rw [Nat.add_comm (a * 10 ^ 10 / Z a (m + 1)) (Z a (m + 1))]
      rw [estep, eZ]
      exact ih (m + 1) hk

/-- The full routine returns the root on positive decimal input. -/
theorem hmain {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) :
    vyperSqrtWith minInt (a : Int) = some (sn a : Int) := by
  rw [vyperSqrtWith_pos minInt ha hle]
  have hZ0 : ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) = (Z a 0 : Int) := rfl
  rw [hZ0]
  by_cases heq : (Z a 0 : Int) = (a : Int)
  · have hZa : Z a 0 = a := Int.ofNat.inj heq
    have hseed : seedN a = a := hZa
    have hseed2 : a = a / 2 + 5000000000 := by
      have hseed' : a / 2 + 5 * 10 ^ 9 = a := hseed
      have e5 : (5 * 10 ^ 9 : Nat) = 5000000000 := by decide
      omega
    have hqa : a / 2 = 4999999999 ∨ a / 2 = 5000000000 := by omega
    have ha9 : a = 9999999999 ∨ a = 10000000000 := by
      rcases hqa with h | h <;> omega
    rcases ha9 with rfl | rfl
    · have hsn9 : sn 9999999999 = 9999999999 := by
        show Nat.sqrt (NatsN 9999999999) = 9999999999
        apply sqrt_eq_of_bounds
        · decide
        · decide
      rw [hZa, hsn9]
      have e256 : (256 : Nat) = 255 + 1 := by omega
      rw [e256, loop_stop]
      exact mapMin (by unfold minInt; rw [if_neg (by omega)])
    · have hsn10 : sn 10000000000 = 10000000000 := by
        show Nat.sqrt (NatsN 10000000000) = 10000000000
        apply sqrt_eq_of_bounds
        · decide
        · decide
      rw [hZa, hsn10]
      have e256 : (256 : Nat) = 255 + 1 := by omega
      rw [e256, loop_stop]
      exact mapMin (by unfold minInt; rw [if_neg (by omega)])
  · have hne : Z a 0 ≠ a := castinjNe _ _ heq
    have e256 : (256 : Nat) = 255 + 1 := by omega
    rw [e256]
    have estep := loop_step (a := a) (y := a) (z := Z a 0) 255 (hseed_pos a) hne
      (hrange ha hle 0)
    rw [estep]
    have eZ : ((a * 10 ^ 10 / Z a 0 + Z a 0) / 2 : Nat) = Z a (0 + 1) := by
      show (a * 10 ^ 10 / Z a 0 + Z a 0) / 2 = newton (NatsN a) (Z a 0)
      simp only [newton, NatsN]
      rw [Nat.add_comm (a * 10 ^ 10 / Z a 0) (Z a 0)]
    rw [eZ]
    exact hloop ha hle 255 0 (by omega)

/-- A raw input with its decimal bound. -/
theorem hbound {x : Int} (hx : IsDecimal x) (hnn : 0 ≤ x) : x.toNat ≤ 2 ^ 167 - 1 := by
  have h2 := hx.2
  have hxnn : x = (x.toNat : Int) := (Int.toNat_of_nonneg hnn).symm
  rw [max_decimal_eq] at h2
  rw [hxnn] at h2
  exact Int.ofNat_le.mp h2

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith _ x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨minInt, fun _ => rfl⟩

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hnn
  have hxnn : x = (x.toNat : Int) := (Int.toNat_of_nonneg hnn).symm
  have hale := hbound hx hnn
  rcases Nat.eq_zero_or_pos x.toNat with h0 | ha
  · have hx0 : x = 0 := by omega
    subst hx0
    have hs0 : sqrt (0 : Int) = some 0 := by
      unfold sqrt vyperSqrtWith
      rw [if_neg (by decide), if_pos (by decide)]
    rw [hs0]
    trivial
  · have hmain := hmain ha hale
    have hsq : sqrt (x.toNat : Int) = some (sn x.toNat : Int) := hmain
    rw [hxnn, hsq]
    trivial

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hsqrt
  by_cases hneg : x < 0
  · have hnone := req_sqrt_neg_reverts x hneg
    rw [hnone] at hsqrt
    cases hsqrt
  · have hnn : 0 ≤ x := by omega
    have hxnn : x = (x.toNat : Int) := (Int.toNat_of_nonneg hnn).symm
    have hale := hbound hx hnn
    rcases Nat.eq_zero_or_pos x.toNat with h0 | ha
    · have hx0 : x = 0 := by omega
      subst hx0
      have hs0 : sqrt (0 : Int) = some 0 := by
        unfold sqrt vyperSqrtWith
        rw [if_neg (by decide), if_pos (by decide)]
      rw [hs0] at hsqrt
      have hr : r = 0 := Option.some_inj.mp hsqrt.symm
      rw [hr]
      omega
    · have hmain := hmain ha hale
      rw [hxnn] at hsqrt
      have hsq : sqrt (x.toNat : Int) = some (sn x.toNat : Int) := hmain
      rw [hsq] at hsqrt
      have hr : r = (sn x.toNat : Int) := (Option.some_inj.mp hsqrt).symm
      have h1 : sn x.toNat * sn x.toNat ≤ x.toNat * 10 ^ 10 := Nat.sqrt_le _
      have h1c : ((sn x.toNat * sn x.toNat : Nat) : Int)
          ≤ ((x.toNat * 10 ^ 10 : Nat) : Int) := Int.ofNat_le.mpr h1
      simp only [Int.natCast_mul] at h1c
      have eD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
      rw [hxnn, hr, eD]
      exact h1c

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hsqrt
  by_cases hneg : x < 0
  · have hnone := req_sqrt_neg_reverts x hneg
    rw [hnone] at hsqrt
    cases hsqrt
  · have hnn : 0 ≤ x := by omega
    have hxnn : x = (x.toNat : Int) := (Int.toNat_of_nonneg hnn).symm
    have hale := hbound hx hnn
    rcases Nat.eq_zero_or_pos x.toNat with h0 | ha
    · have hx0 : x = 0 := by omega
      subst hx0
      have hs0 : sqrt (0 : Int) = some 0 := by
        unfold sqrt vyperSqrtWith
        rw [if_neg (by decide), if_pos (by decide)]
      rw [hs0] at hsqrt
      have hr : r = 0 := Option.some_inj.mp hsqrt.symm
      rw [hr]
      omega
    · have hmain := hmain ha hale
      rw [hxnn] at hsqrt
      have hsq : sqrt (x.toNat : Int) = some (sn x.toNat : Int) := hmain
      rw [hsq] at hsqrt
      have hr : r = (sn x.toNat : Int) := (Option.some_inj.mp hsqrt).symm
      have h2 : x.toNat * 10 ^ 10 < (sn x.toNat + 1) * (sn x.toNat + 1) :=
        Nat.lt_succ_sqrt _
      have h2c : ((x.toNat * 10 ^ 10 : Nat) : Int)
          < (((sn x.toNat + 1) * (sn x.toNat + 1) : Nat) : Int) :=
        Int.ofNat_lt.mpr h2
      simp only [Int.natCast_mul, Int.natCast_add] at h2c
      have eD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
      rw [hxnn, hr, eD]
      exact h2c

end VyperSqrt

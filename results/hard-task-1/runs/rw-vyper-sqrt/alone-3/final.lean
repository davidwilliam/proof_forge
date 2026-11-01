import VyperSqrt.Spec
import VyperSqrt.Lemmas
import Std

namespace VyperSqrt

/-- Fixed `sqrt`: the deployed loop with the PR-4486 choice `min y z`. -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-! ## Newton iteration on naturals -/

/-- Scale factor as a natural number. -/
private def Dnat : Nat := 10 ^ 10

/-- `N(a) = a * 10^10`, the scaled radicand. -/
private def Nrad (a : Nat) : Nat := a * Dnat

/-- `t(a) = ⌊√N(a)⌋`. -/
private def tval (a : Nat) : Nat := Nat.sqrt (Nrad a)

/-- One Newton step: `(N/s + s)/2`. -/
private def nstep (a s : Nat) : Nat := (Nrad a / s + s) / 2

/-- Seed `a/2 + 5*10^9`. -/
private def nseed (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- Newton sequence from the seed. -/
private def nseq (a : Nat) : Nat → Nat
  | 0 => nseed a
  | n + 1 => nstep a (nseq a n)

/-- Total Nat mirror of `loop`: early stop when `z = y`. -/
private def nloop (a : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, z => (y, z)
  | n + 1, y, z => if z = y then (y, z) else nloop a n z (nstep a z)

/-- `t^2 ≤ N`. -/
private theorem sqrt_le_sq (a : Nat) : tval a * tval a ≤ Nrad a :=
  Nat.sqrt_le (Nrad a)

/-- `N < (t+1)^2`. -/
private theorem sqrt_lt_succ_sq (a : Nat) :
    Nrad a < (tval a + 1) * (tval a + 1) := by
  have h := Nat.lt_succ_sqrt (Nrad a)
  unfold tval
  simpa [Nat.succ_eq_add_one] using h

/-- Key quotient bound: above the root, `N/s ≤ t`. -/
private theorem div_le_tval {a s : Nat} (h : tval a + 1 ≤ s) :
    Nrad a / s ≤ tval a := by
  by_cases h' : Nrad a / s ≤ tval a
  · exact h'
  · have hspos : 0 < s := by omega
    have hle : tval a + 1 ≤ Nrad a / s := by omega
    have hmul : (tval a + 1) * s ≤ Nrad a :=
      (Nat.le_div_iff_mul_le hspos).mp hle
    have hmul2 : (tval a + 1) * (tval a + 1) ≤ Nrad a :=
      calc (tval a + 1) * (tval a + 1)
          ≤ (tval a + 1) * s := Nat.mul_le_mul_left _ h
        _ ≤ Nrad a := hmul
    have hlt := sqrt_lt_succ_sq a
    omega

/-- Newton step contracts from above: `step(s) ≤ t + (s-t)/2`. -/
private theorem step_upper {a s : Nat} (h : tval a + 1 ≤ s) :
    nstep a s ≤ tval a + (s - tval a) / 2 := by
  unfold nstep
  have hq : Nrad a / s ≤ tval a := div_le_tval h
  have h1 : Nrad a / s + s ≤ tval a + s :=
    Nat.add_le_add_right hq s
  have h2 : (Nrad a / s + s) / 2 ≤ (tval a + s) / 2 :=
    Nat.div_le_div_right h1
  have h3 : (tval a + s) / 2 = tval a + (s - tval a) / 2 := by omega
  omega

/-- Expand `(t+d)^2`. -/
private theorem expand_add_sq (t d : Nat) :
    (t + d) * (t + d) = t * t + 2 * (t * d) + d * d := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm d t]
  omega

/-- Expand `t*(t+d)`. -/
private theorem expand_mul_add (t d : Nat) :
    t * (t + d) = t * t + t * d := by
  rw [Nat.mul_add]

/-- Newton step stays above the root: `t ≤ step(s)` for `s ≥ t+1`. -/
private theorem step_lower {a s : Nat} (h : tval a + 1 ≤ s) :
    tval a ≤ nstep a s := by
  unfold nstep
  have hspos : 0 < s := by omega
  have hsuff : 2 * tval a ≤ Nrad a / s + s → tval a ≤ (Nrad a / s + s) / 2 := by
    omega
  apply hsuff
  by_cases hc : 2 * tval a ≤ s
  · have hQ0 : 0 ≤ Nrad a / s := Nat.zero_le _
    omega
  · by_cases h2 : 2 * tval a ≤ Nrad a / s + s
    · exact h2
    · exfalso
      have hst : s < 2 * tval a := by omega
      have hQlt : Nrad a / s < 2 * tval a - s := by omega
      have hQle : Nrad a / s ≤ 2 * tval a - s - 1 := by omega
      have hmod : Nrad a % s < s := Nat.mod_lt _ hspos
      have hdm : s * (Nrad a / s) + Nrad a % s = Nrad a := Nat.div_add_mod _ _
      have hmul : s * (Nrad a / s) ≤ s * (2 * tval a - s - 1) :=
        Nat.mul_le_mul_left s hQle
      have hexp : s * (2 * tval a - s - 1 + 1) = s * (2 * tval a - s - 1) + s := by
        rw [Nat.mul_add, Nat.mul_one]
      have hc1 : 2 * tval a - s - 1 + 1 = 2 * tval a - s := by omega
      have hNlt : Nrad a < s * (2 * tval a - s) := by
        rw [← hc1, hexp]
        omega
      have hle : s * s ≤ s * (2 * tval a) := Nat.mul_le_mul_left s (by omega)
      have heq : s * (2 * tval a - s) + s * s = 2 * tval a * s := by
        rw [Nat.mul_sub, Nat.sub_add_cancel hle, Nat.mul_comm s]
      have hchain : Nrad a + s * s < 2 * tval a * s := by omega
      have hsq : tval a * tval a ≤ Nrad a := sqrt_le_sq a
      have hcontra : tval a * tval a + s * s < 2 * tval a * s := by omega
      have hex : ∃ d, s = tval a + d := ⟨s - tval a, by omega⟩
      cases hex with
      | intro d hs =>
        have e1 : s * s = tval a * tval a + 2 * (tval a * d) + d * d := by
          rw [hs]
          exact expand_add_sq _ _
        have e2 : tval a * s = tval a * tval a + tval a * d := by
          rw [hs]
          exact expand_mul_add _ _
        have hjn : (2 * tval a) * s = 2 * (tval a * s) := Nat.mul_assoc _ _ _
        omega

/-- The root is positive for positive input: `1 ≤ a → 1 ≤ t`. -/
private theorem tval_pos {a : Nat} (ha : 1 ≤ a) : 1 ≤ tval a := by
  by_cases h' : 1 ≤ tval a
  · exact h'
  · exfalso
    have ht0 : tval a = 0 := by omega
    have hlt := sqrt_lt_succ_sq a
    rw [ht0] at hlt
    have e : (0 + 1) * (0 + 1) = 1 := by omega
    rw [e] at hlt
    have hD : 1 ≤ Dnat := by unfold Dnat; omega
    have hNge : 1 ≤ Nrad a := by
      unfold Nrad
      have hcc := Nat.mul_le_mul ha hD
      have e1 : (1 : Nat) * 1 = 1 := Nat.mul_one 1
      rw [e1] at hcc
      exact hcc
    omega

/-- Step from the root stays at/above it (positive root). -/
private theorem step_at_t_lower {a : Nat} (ht : 0 < tval a) :
    tval a ≤ nstep a (tval a) := by
  unfold nstep
  have hle : tval a * tval a ≤ Nrad a := sqrt_le_sq a
  have hq : tval a ≤ Nrad a / tval a :=
    (Nat.le_div_iff_mul_le ht).mpr hle
  omega

/-- Step from the root stays close (positive root). -/
private theorem step_at_t_upper {a : Nat} (ht : 0 < tval a) :
    nstep a (tval a) ≤ tval a + 1 := by
  unfold nstep
  have hq : Nrad a / tval a ≤ tval a + 2 := by
    by_cases h' : Nrad a / tval a ≤ tval a + 2
    · exact h'
    · exfalso
      have h3 : tval a + 3 ≤ Nrad a / tval a := by omega
      have hmul : (tval a + 3) * tval a ≤ Nrad a :=
        (Nat.le_div_iff_mul_le ht).mp h3
      have e1 : (tval a + 3) * tval a = tval a * tval a + 3 * tval a := by
        rw [Nat.add_mul]
      have e2 : (tval a + 1) * (tval a + 1) =
          tval a * tval a + 2 * tval a + 1 := by
        have hhex := expand_add_sq (tval a) 1
        have m1 : tval a * 1 = tval a := Nat.mul_one _
        have o1 : (1 : Nat) * 1 = 1 := Nat.mul_one 1
        rw [m1, o1] at hhex
        exact hhex
      have hlt := sqrt_lt_succ_sq a
      omega
  omega

/-- From `t+1` the step lands exactly on `t`. -/
private theorem step_succ (a : Nat) : nstep a (tval a + 1) = tval a := by
  have hup := step_upper (a := a) (s := tval a + 1) (by omega)
  have h1 : tval a + 1 - tval a = 1 := by omega
  rw [h1] at hup
  have hlow := step_lower (a := a) (s := tval a + 1) (by omega)
  omega

/-- AM-GM: `u * 10^10 ≤ u^2 + 25*10^18`. -/
private theorem am_gm (u : Nat) : u * 10 ^ 10 ≤ u * u + 25 * 10 ^ 18 := by
  have e10 : (10 ^ 10 : Nat) = 2 * (5 * 10 ^ 9) := by omega
  have e5 : (5 * 10 ^ 9) * (5 * 10 ^ 9) = 25 * 10 ^ 18 := by omega
  by_cases h : u ≤ 5 * 10 ^ 9
  · have hex : ∃ d, 5 * 10 ^ 9 = u + d := ⟨5 * 10 ^ 9 - u, by omega⟩
    cases hex with
    | intro d hd =>
      have e := expand_add_sq u d
      rw [← hd] at e
      rw [e5] at e
      have ed : u * (5 * 10 ^ 9) = u * u + u * d := by
        rw [hd, Nat.mul_add]
      have eu : u * 10 ^ 10 = 2 * (u * u + u * d) := by
        rw [e10, Nat.mul_left_comm, ed]
      omega
  · have hex : ∃ d, u = 5 * 10 ^ 9 + d := ⟨u - 5 * 10 ^ 9, by omega⟩
    cases hex with
    | intro d hd =>
      have e := expand_add_sq (5 * 10 ^ 9) d
      rw [← hd] at e
      have ed : (5 * 10 ^ 9) * d = d * (5 * 10 ^ 9) := Nat.mul_comm _ _
      have eu : u * 10 ^ 10 =
          (5 * 10 ^ 9) * (10 ^ 10) + d * (10 ^ 10) := by
        rw [hd, Nat.add_mul]
      have e59 : (5 * 10 ^ 9) * (10 ^ 10) =
          2 * ((5 * 10 ^ 9) * (5 * 10 ^ 9)) := by
        rw [e10, Nat.mul_left_comm]
      have ed2 : d * 10 ^ 10 = 2 * (d * (5 * 10 ^ 9)) := by
        rw [e10, Nat.mul_left_comm]
      omega

/-- The seed square exceeds the radicand: `N < (s₀+1)^2`. -/
private theorem seed_sq_gt (a : Nat) :
    Nrad a < (nseed a + 1) * (nseed a + 1) := by
  have hdm : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hmod : a % 2 ≤ 1 := by
    have := Nat.mod_lt a (by omega : 0 < 2)
    omega
  have eD : (10 ^ 10 : Nat) = 2 * (5 * 10 ^ 9) := rfl
  have ec : (5 * 10 ^ 9 + 1) * (5 * 10 ^ 9 + 1) =
      25 * 10 ^ 18 + 10 ^ 10 + 1 := rfl
  have hs : nseed a + 1 = a / 2 + (5 * 10 ^ 9 + 1) := by
    unfold nseed
    exact Nat.add_assoc _ _ _
  have e := expand_add_sq (a / 2) (5 * 10 ^ 9 + 1)
  have ham := am_gm (a / 2)
  rw [hs, e]
  unfold Nrad Dnat
  omega

/-- The seed is above the root: `t ≤ s₀`. -/
private theorem seed_ge (a : Nat) : tval a ≤ nseed a := by
  by_cases h' : tval a ≤ nseed a
  · exact h'
  · exfalso
    have hc : nseed a + 1 ≤ tval a := by omega
    have hmul : (nseed a + 1) * (nseed a + 1) ≤ tval a * tval a :=
      Nat.mul_le_mul hc hc
    have hsq := sqrt_le_sq a
    have hgt := seed_sq_gt a
    omega

/-- Decimal max as a natural number. -/
private def MAXLIT : Nat := 187072209578355573530071658587684226515959365500927

/-- Loose upper bound for the root: `3 * 10^30`. -/
private def Sbound : Nat := 3000000000000000000000000000000

/-- The root is below `Sbound` for decimal inputs. -/
private theorem tval_lt_S {a : Nat} (ha : a ≤ MAXLIT) : tval a < Sbound := by
  by_cases h' : tval a < Sbound
  · exact h'
  · exfalso
    have hle : Sbound ≤ tval a := by omega
    have hmul : Sbound * Sbound ≤ tval a * tval a :=
      Nat.mul_le_mul hle hle
    have hsq := sqrt_le_sq a
    have hN : Nrad a ≤ MAXLIT * 10 ^ 10 := by
      unfold Nrad Dnat
      exact Nat.mul_le_mul_right _ ha
    have hSS : MAXLIT * 10 ^ 10 < Sbound * Sbound := by
      unfold MAXLIT Sbound
      omega
    omega

/-- The seed is a decimal for decimal inputs. -/
private theorem nseed_le_MAX {a : Nat} (ha : a ≤ MAXLIT) : nseed a ≤ MAXLIT := by
  unfold nseed at ⊢
  unfold MAXLIT at ha ⊢
  omega

/-- Iterates stay in range: `N/s + s ≤ MAXLIT`. -/
private theorem range_bound {a s : Nat} (ha : a ≤ MAXLIT) (ha1 : 1 ≤ a)
    (hts : tval a ≤ s) (hsb : s ≤ nseed a + 1) :
    Nrad a / s + s ≤ MAXLIT := by
  have ht1 := tval_pos ha1
  have htS := tval_lt_S ha
  unfold Sbound at htS
  have hs0h : nseed a ≤ MAXLIT / 2 + 5000000000 := by
    unfold nseed at ⊢
    unfold MAXLIT at ha ⊢
    omega
  unfold MAXLIT at ha hs0h ⊢
  by_cases hs1 : tval a + 1 ≤ s
  · have hq : Nrad a / s ≤ tval a := div_le_tval hs1
    omega
  · have hseq : s = tval a := by omega
    have hst := step_at_t_upper (a := a) (by omega)
    unfold nstep at hst
    rw [hseq]
    omega

/-- Halving fuel: starts at `MAXLIT`, halves each round. -/
private def Ebound : Nat → Nat
  | 0 => 187072209578355573530071658587684226515959365500927
  | k + 1 => Ebound k / 2

/-- Eight halvings equal one division by 256. -/
private theorem Ebound_add8 (m : Nat) : Ebound (m + 8) = Ebound m / 256 := by
  have r1 : Ebound (m + 1) = Ebound m / 2 := rfl
  have r2 : Ebound (m + 2) = Ebound (m + 1) / 2 := rfl
  have r3 : Ebound (m + 3) = Ebound (m + 2) / 2 := rfl
  have r4 : Ebound (m + 4) = Ebound (m + 3) / 2 := rfl
  have r5 : Ebound (m + 5) = Ebound (m + 4) / 2 := rfl
  have r6 : Ebound (m + 6) = Ebound (m + 5) / 2 := rfl
  have r7 : Ebound (m + 7) = Ebound (m + 6) / 2 := rfl
  have r8 : Ebound (m + 8) = Ebound (m + 7) / 2 := rfl
  rw [r8, r7, r6, r5, r4, r3, r2, r1,
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul]

/-- Closed form at multiples of 8. -/
private theorem Ebound8_eq : ∀ j, Ebound (8 * j) = MAXLIT / 256 ^ j := by
  intro j
  induction j with
  | zero =>
    have b0 : 8 * 0 = 0 := by omega
    have p0 : (256 : Nat) ^ 0 = 1 := Nat.pow_zero 256
    have d1 : MAXLIT / 1 = MAXLIT := by omega
    have hE0 : Ebound 0 = MAXLIT := rfl
    rw [b0, p0, d1, hE0]
  | succ j ih =>
    have h8 : 8 * (j + 1) = 8 * j + 8 := by
      rw [Nat.mul_add, Nat.mul_one]
    have ps : (256 : Nat) ^ (j + 1) = 256 ^ j * 256 := by
      rw [← Nat.succ_eq_add_one]
      exact Nat.pow_succ 256 j
    rw [h8, Ebound_add8, ih, ps, Nat.div_div_eq_div_mul]

/-- Fuel vanishes after 168 halvings. -/
private theorem Ebound_168 : Ebound 168 = 0 := by
  have h := Ebound8_eq 21
  have h21 : 8 * 21 = 168 := by omega
  rw [h21] at h
  have hlt : MAXLIT < (256 : Nat) ^ 21 := by
    unfold MAXLIT
    omega
  have hz : MAXLIT / (256 : Nat) ^ 21 = 0 := Nat.div_eq_of_lt hlt
  rw [hz] at h
  exact h

/-- Fuel stays zero thereafter. -/
private theorem Ebound_ge : ∀ k, Ebound (168 + k) = 0 := by
  intro k
  induction k with
  | zero =>
    have h : 168 + 0 = 168 := by omega
    rw [h]
    exact Ebound_168
  | succ k ih =>
    have hstep : Ebound (168 + (k + 1)) = Ebound (168 + k) / 2 := by
      have : 168 + (k + 1) = (168 + k) + 1 := by omega
      rw [this]
      rfl
    rw [hstep, ih]

private theorem Ebound_255 : Ebound 255 = 0 := by
  have h := Ebound_ge 87
  have : 168 + 87 = 255 := by omega
  rw [this] at h
  exact h

private theorem Ebound_256 : Ebound 256 = 0 := by
  have h := Ebound_ge 88
  have : 168 + 88 = 256 := by omega
  rw [this] at h
  exact h

/-- Strict decrease above the root. -/
private theorem step_lt {a s : Nat} (h : tval a + 1 ≤ s) :
    nstep a s < s := by
  have hup := step_upper h
  have hts : tval a ≤ s := by omega
  have he : s - tval a ≥ 1 := by omega
  have hhalf : (s - tval a) / 2 < s - tval a := by omega
  omega

/-- Sequence invariants: stays above `t`, near the seed, and contracts with fuel. -/
private theorem nseq_inv {a : Nat} (ha : a ≤ MAXLIT) (ha1 : 1 ≤ a) :
    ∀ k, tval a ≤ nseq a k ∧ nseq a k ≤ nseed a + 1 ∧
      nseq a k ≤ tval a + Ebound k + 1 := by
  have ht1 := tval_pos ha1
  have hge := seed_ge a
  have hs0 := nseed_le_MAX ha
  intro k
  induction k with
  | zero =>
    show tval a ≤ nseed a ∧ nseed a ≤ nseed a + 1 ∧
      nseed a ≤ tval a + Ebound 0 + 1
    have hE0 : Ebound 0 = MAXLIT := rfl
    rw [hE0]
    exact ⟨hge, by omega, by omega⟩
  | succ k ih =>
    have ih1 := ih.1
    have ih2 := ih.2.1
    have ih3 := ih.2.2
    show tval a ≤ nstep a (nseq a k) ∧ nstep a (nseq a k) ≤ nseed a + 1 ∧
      nstep a (nseq a k) ≤ tval a + Ebound (k + 1) + 1
    have hEk : Ebound (k + 1) = Ebound k / 2 := rfl
    rw [hEk]
    by_cases hs1 : tval a + 1 ≤ nseq a k
    · have hlo := step_lower hs1
      have hup := step_upper hs1
      omega
    · have hseq : nseq a k = tval a := by omega
      have hlo := step_at_t_lower (a := a) (by omega)
      have hup := step_at_t_upper (a := a) (by omega)
      rw [hseq]
      omega

/-- Seed fixed point forces the root: `s₀ = a → t = a`. -/
private theorem seed_eq_self {a : Nat} (h : nseed a = a) : tval a = a := by
  have haD : a ≤ 10000000000 := by
    unfold nseed at h
    omega
  have ha9 : 9999999999 ≤ a := by
    unfold nseed at h
    omega
  have hsq1 : a * a ≤ Nrad a := by
    unfold Nrad Dnat
    exact Nat.mul_le_mul_left a haD
  have e2 : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
    have hex := expand_add_sq a 1
    have m1 : a * 1 = a := Nat.mul_one _
    have o1 : (1 : Nat) * 1 = 1 := Nat.mul_one 1
    rw [m1, o1] at hex
    exact hex
  have e10 : (10 ^ 10 : Nat) = 10000000000 := rfl
  have hD : (10000000000 : Nat) = a + (10000000000 - a) := by omega
  have eN : a * 10000000000 = a * a + a * (10000000000 - a) := by
    rw [← Nat.mul_add, ← hD]
  have hsmall : a * (10000000000 - a) ≤ 2 * a := by
    have hd1 : 10000000000 - a ≤ 1 := by omega
    have hm := Nat.mul_le_mul_left a hd1
    have m1 : a * 1 = a := Nat.mul_one _
    rw [m1] at hm
    omega
  have hsq2 : Nrad a < (a + 1) * (a + 1) := by
    unfold Nrad Dnat
    rw [e10]
    omega
  have hle1 : a ≤ tval a := by
    by_cases h' : a ≤ tval a
    · exact h'
    · exfalso
      have hc : tval a + 1 ≤ a := by omega
      have hm := Nat.mul_le_mul hc hc
      have hlt := sqrt_lt_succ_sq a
      omega
  have hle2 : tval a ≤ a := by
    by_cases h' : tval a ≤ a
    · exact h'
    · exfalso
      have hc : a + 1 ≤ tval a := by omega
      have hm := Nat.mul_le_mul hc hc
      have hsq := sqrt_le_sq a
      omega
  omega

/-- One unfolding of the Newton sequence. -/
private theorem nseq_succ (a m : Nat) : nseq a (m + 1) = nstep a (nseq a m) := rfl

/-- The Nat loop chooses the floor after 256 iterations. -/
private theorem nloop_min {a : Nat} (ha : a ≤ MAXLIT) (ha1 : 1 ≤ a) :
    ∀ n y z k, k + n = 256 →
      ((k = 0 ∧ y = a ∧ z = nseq a 0) ∨ (0 < k ∧ y = nseq a (k - 1) ∧ z = nseq a k)) →
      (if (nloop a n y z).1 < (nloop a n y z).2 then (nloop a n y z).1
        else (nloop a n y z).2) = tval a := by
  have ht1 := tval_pos ha1
  intro n
  induction n with
  | zero =>
    intro y z k hkn hst
    have hk256 : k = 256 := by omega
    cases hst with
    | inl h => exfalso; omega
    | inr h =>
      have hy : y = nseq a (k - 1) := h.2.1
      have hz : z = nseq a k := h.2.2
      rw [hk256] at hy hz
      have hy255 : y = nseq a 255 := hy
      have hz256 : z = nseq a 256 := hz
      have i255 := nseq_inv ha ha1 255
      have i256 := nseq_inv ha ha1 256
      rw [Ebound_255] at i255
      rw [Ebound_256] at i256
      have h255 : (256 : Nat) = 255 + 1 := rfl
      have hnl : nloop a 0 y z = (y, z) := rfl
      rw [hnl]
      show (if y < z then y else z) = tval a
      have hrel : z = nstep a y := by
        rw [hz256, hy255, h255]
        exact nseq_succ a 255
      have hyb1 : tval a ≤ y := by omega
      have hyb2 : y ≤ tval a + 1 := by omega
      have hzb1 : tval a ≤ z := by omega
      have hzb2 : z ≤ tval a + 1 := by omega
      have hyv : y = tval a ∨ y = tval a + 1 := by omega
      cases hyv with
      | inl hyt =>
        by_cases hlt : y < z
        · rw [if_pos hlt]
          exact hyt
        · rw [if_neg hlt]
          omega
      | inr hyt1 =>
        have hzt : z = tval a := by rw [hrel, hyt1]; exact step_succ a
        have hneg : ¬ y < z := by omega
        rw [if_neg hneg]
        exact hzt
  | succ n ih =>
    intro y z k hkn hst
    have hnl : nloop a (n + 1) y z =
        (if z = y then (y, z) else nloop a n z (nstep a z)) := rfl
    rw [hnl]
    by_cases hzy : z = y
    · rw [if_pos hzy]
      show (if y < z then y else z) = tval a
      rw [hzy]
      have hne : ¬ y < y := by omega
      rw [if_neg hne]
      cases hst with
      | inl h =>
        have hya : y = a := h.2.1
        have hzs : z = nseq a 0 := h.2.2
        have e0 : nseq a 0 = nseed a := rfl
        have hseq : nseed a = a := by
          rw [← e0, ← hzs, hzy, hya]
        have hat := seed_eq_self hseq
        omega
      | inr h =>
        have hkpos : 0 < k := h.1
        have hex : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        cases hex with
        | intro j hj =>
          have hy : y = nseq a (k - 1) := h.2.1
          have hz : z = nseq a k := h.2.2
          rw [hj] at hy hz
          have hy' : y = nseq a j := hy
          have hstep : z = nstep a y := by
            rw [hz, hy']
            exact nseq_succ a j
          have hty := (nseq_inv ha ha1 j).1
          by_cases hs1 : tval a + 1 ≤ y
          · exfalso
            have hlt := step_lt hs1
            omega
          · omega
    · rw [if_neg hzy]
      have hkn' : (k + 1) + n = 256 := by omega
      cases hst with
      | inl h =>
        have hk0 : k = 0 := h.1
        have hya : y = a := h.2.1
        have hzs : z = nseq a 0 := h.2.2
        have e1 : z = nseq a ((k + 1) - 1) := by rw [hk0, hzs]
        have e2 : nstep a z = nseq a (k + 1) := by
          rw [hk0, hzs]
          exact (nseq_succ a 0).symm
        exact ih z (nstep a z) (k + 1) hkn' (Or.inr ⟨by omega, e1, e2⟩)
      | inr h =>
        have hy : y = nseq a (k - 1) := h.2.1
        have hz : z = nseq a k := h.2.2
        have e1k : (k + 1) - 1 = k := by omega
        have e1 : z = nseq a ((k + 1) - 1) := by rw [e1k]; exact hz
        have e2 : nstep a z = nseq a (k + 1) := by
          rw [hz]
          exact (nseq_succ a k).symm
        exact ih z (nstep a z) (k + 1) hkn' (Or.inr ⟨by omega, e1, e2⟩)

/-- The Int loop mirrors the Nat loop. -/
private theorem loop_corr {a : Nat} (ha : a ≤ MAXLIT) (ha1 : 1 ≤ a) :
    ∀ n (y z : Nat), tval a ≤ z → z ≤ nseed a + 1 →
      loop (a : Int) n (y : Int) (z : Int) =
        some (((nloop a n y z).1 : Int), ((nloop a n y z).2 : Int)) := by
  have ht1 := tval_pos ha1
  intro n
  induction n with
  | zero =>
    intro y z _ _
    rfl
  | succ n ih =>
    intro y z htz hsb
    have hrange : Nrad a / z + z ≤ MAXLIT := range_bound ha ha1 htz hsb
    have hmax : Nrad a / z + z ≤ 2 ^ 167 - 1 := hrange
    by_cases hzy : y = z
    · rw [hzy]
      rw [loop_stop]
      simp only [nloop, if_true]
    · have hzpos : 0 < z := by omega
      have hst := loop_step n hzpos (Ne.symm hzy) hmax
      have hn : nloop a (n + 1) y z = nloop a n z (nstep a z) := by
        simp only [nloop]
        rw [if_neg (Ne.symm hzy)]
      rw [hst, hn]
      have htz' : tval a ≤ nstep a z := by
        by_cases hs1 : tval a + 1 ≤ z
        · exact step_lower hs1
        · have hze : z = tval a := by omega
          rw [hze]
          exact step_at_t_lower (a := a) (by omega)
      have hsb' : nstep a z ≤ nseed a + 1 := by
        have hge := seed_ge a
        by_cases hs1 : tval a + 1 ≤ z
        · have hup := step_upper hs1
          omega
        · have hze : z = tval a := by omega
          have hup := step_at_t_upper (a := a) (by omega)
          rw [hze]
          omega
      exact ih z (nstep a z) htz' hsb'

/-- Every non-negative decimal is a Nat cast. -/
private theorem nat_of_decimal {x : Int} (hx : IsDecimal x) (h0 : 0 ≤ x) :
    ∃ a : Nat, x = (a : Int) ∧ a ≤ MAXLIT := by
  refine ⟨x.toNat, (Int.toNat_of_nonneg h0).symm, ?_⟩
  unfold IsDecimal at hx
  have hxmax : x ≤ MAX_DECIMAL := hx.2
  have h2 : ((x.toNat : Nat) : Int) ≤ MAX_DECIMAL := by
    rw [Int.toNat_of_nonneg h0]
    exact hxmax
  unfold MAX_DECIMAL at h2
  unfold MAXLIT
  omega

/-- The Int choice matches the Nat choice under cast. -/
private theorem choice_cast (y z : Nat) :
    (if (y : Int) < (z : Int) then (y : Int) else (z : Int)) =
      (((if y < z then y else z : Nat)) : Int) := by
  by_cases h : y < z
  · rw [if_pos h]
    have hI : (y : Int) < (z : Int) := by omega
    rw [if_pos hI]
  · rw [if_neg h]
    have hI : ¬ (y : Int) < (z : Int) := by omega
    rw [if_neg hI]

/-- On positive decimals, `sqrt` is the floor. -/
private theorem sqrt_pos_floor {x : Int} (hx : IsDecimal x) (hpos : 0 < x) :
    ∃ a : Nat, x = (a : Int) ∧ 1 ≤ a ∧ a ≤ MAXLIT ∧
      sqrt x = some ((tval a : Nat) : Int) := by
  have h0 : 0 ≤ x := by omega
  have hex := nat_of_decimal hx h0
  cases hex with
  | intro a ha =>
    have hxa : x = (a : Int) := ha.1
    have haMAX : a ≤ MAXLIT := ha.2
    have ha1 : 1 ≤ a := by omega
    refine ⟨a, hxa, ha1, haMAX, ?_⟩
    rw [hxa]
    unfold sqrt
    have hpos' : 0 < a := by omega
    have hbound : a ≤ 2 ^ 167 - 1 := haMAX
    rw [vyperSqrtWith_pos _ hpos' hbound]
    have htz : tval a ≤ nseed a := seed_ge a
    have hsb : nseed a ≤ nseed a + 1 := by omega
    have eseed : (a / 2 + 5 * 10 ^ 9 : Nat) = nseed a := rfl
    rw [eseed]
    have hloop := loop_corr haMAX ha1 256 a (nseed a) htz hsb
    have e0 : nseq a 0 = nseed a := rfl
    have hmin := nloop_min haMAX ha1 256 a (nseed a) 0 (by omega) (Or.inl ⟨rfl, rfl, e0.symm⟩)
    rw [hloop]
    show some (if ((nloop a 256 a (nseed a)).1 : Int) < ((nloop a 256 a (nseed a)).2 : Int)
      then ((nloop a 256 a (nseed a)).1 : Int) else ((nloop a 256 a (nseed a)).2 : Int)) =
      some (((tval a : Nat)) : Int)
    rw [choice_cast, hmin]

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  simp [hx]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨(fun y z => if y < z then y else z), fun _ => rfl⟩

/-- `sqrt 0 = some 0`. -/
private theorem sqrt_zero : sqrt (0 : Int) = some 0 := by
  unfold sqrt vyperSqrtWith
  rw [if_neg (by omega : ¬ (0 : Int) < 0), if_pos rfl]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hr
  by_cases hx0 : x = 0
  · subst hx0
    rw [sqrt_zero] at hr
    cases hr
    unfold DIVISOR
    omega
  · by_cases hneg : x < 0
    · have hnone := req_sqrt_neg_reverts x hneg
      rw [hnone] at hr
      cases hr
    · have hpos : 0 < x := by omega
      have hex := sqrt_pos_floor hx hpos
      cases hex with
      | intro a ha =>
        have hxa : x = (a : Int) := ha.1
        have heq := ha.2.2.2
        rw [heq] at hr
        cases hr
        rw [hxa]
        have hsq : tval a * tval a ≤ a * 10 ^ 10 := sqrt_le_sq a
        rw [divisor_eq]
        exact_mod_cast hsq

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hr
  by_cases hx0 : x = 0
  · subst hx0
    rw [sqrt_zero] at hr
    cases hr
    unfold DIVISOR
    omega
  · by_cases hneg : x < 0
    · have hnone := req_sqrt_neg_reverts x hneg
      rw [hnone] at hr
      cases hr
    · have hpos : 0 < x := by omega
      have hex := sqrt_pos_floor hx hpos
      cases hex with
      | intro a ha =>
        have hxa : x = (a : Int) := ha.1
        have heq := ha.2.2.2
        rw [heq] at hr
        cases hr
        rw [hxa]
        have hlt : a * 10 ^ 10 < (tval a + 1) * (tval a + 1) := sqrt_lt_succ_sq a
        rw [divisor_eq]
        exact_mod_cast hlt

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx h0
  by_cases hx0 : x = 0
  · subst hx0
    simp [sqrt_zero]
  · have hpos : 0 < x := by omega
    have hex := sqrt_pos_floor hx hpos
    cases hex with
    | intro a ha =>
      have heq := ha.2.2.2
      simp [heq]

end VyperSqrt

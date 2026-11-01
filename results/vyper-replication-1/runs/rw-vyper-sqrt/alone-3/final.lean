import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

def minFin : Int → Int → Int := fun y z => if y < z then y else z

def sqrt : SqrtFn := vyperSqrtWith minFin

theorem sqSucc (r : Nat) : (r + 1) * (r + 1) = r * r + (2 * r + 1) := by
  have e1 : (r + 1) * (r + 1) = (r + 1) * r + (r + 1) * 1 := by rw [Nat.mul_add]
  have e2 : (r + 1) * r = r * r + r := by rw [Nat.add_mul, Nat.one_mul]
  have e3 : (r + 1) * 1 = r + 1 := Nat.mul_one _
  omega

theorem floorEx : ∀ S : Nat, ∃ r, r * r ≤ S ∧ S < (r + 1) * (r + 1) := by
  intro S
  induction S with
  | zero => exact ⟨0, Nat.zero_le _, by decide⟩
  | succ n ih =>
    obtain ⟨r, hr1, hr2⟩ := ih
    by_cases h : n + 1 < (r + 1) * (r + 1)
    · exact ⟨r, by omega, h⟩
    · have hle : (r + 1) * (r + 1) ≤ n + 1 := by omega
      have hle2 : n + 1 ≤ (r + 1) * (r + 1) := by omega
      have heq : (r + 1) * (r + 1) = n + 1 := by omega
      have g1 : (r + 1) * (r + 1) < (r + 1) * ((r + 1) + 1) :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) (Nat.succ_pos _)
      have g2 : (r + 1) * ((r + 1) + 1) ≤ ((r + 1) + 1) * (((r + 1) + 1)) :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)
      have hlt : (r + 1) * (r + 1) < ((r + 1) + 1) * (((r + 1) + 1)) :=
        Nat.lt_of_lt_of_le g1 g2
      exact ⟨r + 1, by omega, heq ▸ hlt⟩

def stepN (S z : Nat) : Nat := (S / z + z) / 2

def seqN (S s : Nat) : Nat → Nat
  | 0 => s
  | n + 1 => stepN S (seqN S s n)

theorem seqSucc {S s k : Nat} : seqN S s (k + 1) = stepN S (seqN S s k) := rfl

theorem seqZero {S s : Nat} : seqN S s 0 = s := rfl

theorem quotLe {S r z : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hz : r + 1 ≤ z) : S / z ≤ r := by
  by_cases hr : r = 0
  · subst hr
    have e : (0 + 1) * (0 + 1) = 1 := by decide
    rw [e] at h2
    have hS0 : S = 0 := by omega
    subst hS0
    exact Nat.div_le_self _ _
  · have hr1 : 1 ≤ r := by omega
    have h3 : (r + 1) * (r + 1) ≤ z * (r + 1) := Nat.mul_le_mul_right _ hz
    have h4 : S < z * (r + 1) := Nat.lt_of_lt_of_le h2 h3
    by_cases hle : S / z ≤ r
    · exact hle
    · have hgt : r + 1 ≤ S / z := by omega
      have h5 : (r + 1) * z ≤ S / z * z := Nat.mul_le_mul_right _ hgt
      have h6 : S / z * z ≤ S := Nat.div_mul_le_self _ _
      have h7 : z * (r + 1) = (r + 1) * z := Nat.mul_comm _ _
      omega

theorem stepUpper {S r z : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hle : r + 1 ≤ z) : stepN S z ≤ r + (z - r) / 2 := by
  have hrz : r ≤ z := by omega
  have hq : S / z ≤ r := quotLe h1 h2 hle
  have e : z = r + (z - r) := by omega
  unfold stepN
  have h3 : S / z + z ≤ (z - r) + 2 * r := by omega
  have h4 : ((z - r) + 2 * r) / 2 = (z - r) / 2 + r :=
    Nat.add_mul_div_left _ _ (show (0 : Nat) < 2 by decide)
  have h5 : (S / z + z) / 2 ≤ ((z - r) + 2 * r) / 2 := Nat.div_le_div_right h3
  omega

theorem stepLower {S r z : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hrz : r ≤ z) (hz : 0 < z) : r ≤ stepN S z := by
  unfold stepN
  by_cases hr0 : r = 0
  · subst hr0
    exact Nat.zero_le _
  · have hr1 : 1 ≤ r := by omega
    have hsuff : 2 * r ≤ S / z + z := by
      have hnn : 0 ≤ S / z := Nat.zero_le _
      by_cases hz2 : 2 * r ≤ z
      · omega
      · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hrz
        subst he
        have her : e < r := by omega
        have hsub : 2 * r - (r + e) = r - e := by omega
        have hexpand : (r - e) * (r + e) = r * r - e * e := by
          have a1 : (r - e) * (r + e) = (r - e) * r + (r - e) * e := Nat.mul_add _ _ _
          have a2 : (r - e) * r = r * r - e * r := Nat.sub_mul _ _ _
          have a3 : (r - e) * e = r * e - e * e := Nat.sub_mul _ _ _
          have a4 : e * r = r * e := Nat.mul_comm _ _
          have m1 : e * r ≤ r * r := Nat.mul_le_mul_right _ (by omega : e ≤ r)
          have m2 : e * e ≤ e * r := Nat.mul_le_mul_left _ (by omega : e ≤ r)
          omega
        have hzpos : 0 < r + e := by omega
        have hmul : (2 * r - (r + e)) * (r + e) ≤ S := by
          rw [hsub, hexpand]
          exact Nat.le_trans (Nat.sub_le _ _) h1
        have hle : 2 * r - (r + e) ≤ S / (r + e) :=
          (Nat.le_div_iff_mul_le hzpos).mpr hmul
        omega
    have h2r : 2 * r / 2 = r := Nat.mul_div_cancel_left _ (show (0 : Nat) < 2 by decide)
    have hle2 : 2 * r / 2 ≤ (S / z + z) / 2 := Nat.div_le_div_right hsuff
    omega

theorem stepStrict {S r z : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hle : r + 1 ≤ z) : stepN S z < z := by
  have hrz : r ≤ z := by omega
  have hup := stepUpper h1 h2 hle
  have hlt : (z - r) / 2 < z - r := by omega
  omega

theorem stepAtRUpper {S r : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1)) :
    stepN S r ≤ r + 1 := by
  by_cases hr0 : r = 0
  · subst hr0
    have e : (0 + 1) * (0 + 1) = 1 := by decide
    rw [e] at h2
    have hS0 : S = 0 := by omega
    unfold stepN
    rw [hS0]
    decide
  · have hr1 : 1 ≤ r := by omega
    have e1 := sqSucc r
    have hSle : S ≤ r * r + 2 * r := by omega
    have hlt : S < r * (r + 3) := by
      have a1 : r * (r + 3) = r * r + r * 3 := Nat.mul_add _ _ _
      have c : r * 3 = 3 * r := Nat.mul_comm _ _
      omega
    have hq : S / r ≤ r + 2 := by
      by_cases hle2 : S / r ≤ r + 2
      · exact hle2
      · have hgt : r + 3 ≤ S / r := by omega
        have h5 : (r + 3) * r ≤ S / r * r := Nat.mul_le_mul_right _ hgt
        have h6 : S / r * r ≤ S := Nat.div_mul_le_self _ _
        have h7 : r * (r + 3) = (r + 3) * r := Nat.mul_comm _ _
        omega
    unfold stepN
    have h3 : S / r + r ≤ 2 * r + 2 := by omega
    have h4 : (2 * r + 2) / 2 = r + 1 := by
      have d : (2 : Nat) / 2 = 1 := by decide
      have e2 : 2 * r + 2 = 2 + 2 * r := by omega
      rw [e2, Nat.add_mul_div_left _ _ (show (0 : Nat) < 2 by decide), d]
      omega
    have h5 : (S / r + r) / 2 ≤ (2 * r + 2) / 2 := Nat.div_le_div_right h3
    omega

theorem stepAtSucc {S r : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1)) :
    stepN S (r + 1) = r := by
  have hlo : r ≤ stepN S (r + 1) :=
    stepLower h1 h2 (Nat.le_succ _) (Nat.succ_pos _)
  have hq : S / (r + 1) ≤ r := quotLe h1 h2 (Nat.le_refl _)
  have hup : stepN S (r + 1) ≤ r := by
    unfold stepN
    have h3 : S / (r + 1) + (r + 1) ≤ 2 * r + 1 := by omega
    have h4 : (2 * r + 1) / 2 = r := by
      have d0 : (1 : Nat) / 2 = 0 := by decide
      have e1 : 2 * r + 1 = 1 + 2 * r := by omega
      rw [e1, Nat.add_mul_div_left _ _ (show (0 : Nat) < 2 by decide), d0]
      omega
    have h5 : (S / (r + 1) + (r + 1)) / 2 ≤ (2 * r + 1) / 2 :=
      Nat.div_le_div_right h3
    omega
  omega

theorem stepFixed {S r w : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hrw : r ≤ w) (hfix : stepN S w = w) : w = r := by
  by_cases hle : r + 1 ≤ w
  · have hlt := stepStrict h1 h2 hle
    omega
  · omega

theorem sqNonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h2 : 0 ≤ -x := by omega
    have h3 := Int.mul_nonneg h2 h2
    rwa [Int.neg_mul_neg] at h3

theorem seedKey (k : Nat) :
    (2 * k + 1) * (2 * 5000000000) < (k + 5000000000 + 1) * (k + 5000000000 + 1) := by
  rw [← Int.ofNat_lt]
  have p1 : ((((2 * k + 1) * (2 * 5000000000) : Nat)) : Int)
      = (2 * (k : Int) + 1) * (2 * 5000000000) := by simp
  have p2 : ((((k + 5000000000 + 1) * (k + 5000000000 + 1) : Nat)) : Int)
      = ((k : Int) + 5000000000 + 1) * ((k : Int) + 5000000000 + 1) := by simp
  rw [p1, p2]
  have hsq := sqNonneg ((k : Int) - 5000000000)
  have hK : 0 ≤ (k : Int) := by simp
  have eX : ((k : Int) + 5000000000) * ((k : Int) + 5000000000)
      = (k : Int) * (k : Int) + (k : Int) * 5000000000
        + (5000000000 * (k : Int) + 5000000000 * 5000000000) := by
    have d1 : ((k : Int) + 5000000000) * ((k : Int) + 5000000000)
        = (k : Int) * ((k : Int) + 5000000000)
          + 5000000000 * ((k : Int) + 5000000000) := Int.add_mul _ _ _
    have d2 : (k : Int) * ((k : Int) + 5000000000)
        = (k : Int) * (k : Int) + (k : Int) * 5000000000 := Int.mul_add _ _ _
    have d3 : (5000000000 : Int) * ((k : Int) + 5000000000)
        = 5000000000 * (k : Int) + 5000000000 * 5000000000 := Int.mul_add _ _ _
    omega
  have eP : ((k : Int) + 5000000000 + 1) * ((k : Int) + 5000000000 + 1)
      = ((k : Int) - 5000000000) * ((k : Int) - 5000000000)
        + (k : Int) * 20000000000 + 2 * (k : Int) + 10000000001 := by
    have a1 : ((k : Int) + 5000000000 + 1) * ((k : Int) + 5000000000 + 1)
        = ((k : Int) + 5000000000) * ((k : Int) + 5000000000)
          + ((k : Int) + 5000000000) + (((k : Int) + 5000000000) + 1) := by
      have b1 : ((k : Int) + 5000000000 + 1) * ((k : Int) + 5000000000 + 1)
          = ((k : Int) + 5000000000) * ((k : Int) + 5000000000 + 1)
            + 1 * ((k : Int) + 5000000000 + 1) := Int.add_mul _ _ _
      have b2 : ((k : Int) + 5000000000) * ((k : Int) + 5000000000 + 1)
          = ((k : Int) + 5000000000) * ((k : Int) + 5000000000)
            + ((k : Int) + 5000000000) * 1 := Int.mul_add _ _ _
      have m1 : (((k : Int) + 5000000000) : Int) * 1 = (k : Int) + 5000000000 :=
        Int.mul_one _
      have o1 : (1 : Int) * ((k : Int) + 5000000000 + 1)
          = (k : Int) + 5000000000 + 1 := Int.one_mul _
      omega
    have a2 : ((k : Int) - 5000000000) * ((k : Int) - 5000000000)
        = (k : Int) * (k : Int) - (k : Int) * 5000000000
          - (5000000000 * (k : Int) - 5000000000 * 5000000000) := by
      have c1 : ((k : Int) - 5000000000) * ((k : Int) - 5000000000)
          = (k : Int) * ((k : Int) - 5000000000)
            - 5000000000 * ((k : Int) - 5000000000) := Int.sub_mul _ _ _
      have c2 : (k : Int) * ((k : Int) - 5000000000)
          = (k : Int) * (k : Int) - (k : Int) * 5000000000 := Int.mul_sub _ _ _
      have c3 : (5000000000 : Int) * ((k : Int) - 5000000000)
          = 5000000000 * (k : Int) - 5000000000 * 5000000000 := Int.mul_sub _ _ _
      omega
    have c1 : (k : Int) * 5000000000 = 5000000000 * (k : Int) := Int.mul_comm _ _
    have d1 : (5000000000 : Int) * 5000000000 = 25000000000000000000 := by decide
    omega
  have eL : (2 * (k : Int) + 1) * (2 * 5000000000)
      = (2 * (k : Int)) * 10000000000 + 1 * 10000000000 := by
    have dw : (2 : Int) * 5000000000 = 10000000000 := by decide
    rw [dw]
    exact Int.add_mul _ _ _
  have c1 : (k : Int) * 5000000000 = 5000000000 * (k : Int) := Int.mul_comm _ _
  omega

theorem seedLower {S r a : Nat} (hS : S = a * 10 ^ 10)
    (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1)) : r ≤ a / 2 + 5 * 10 ^ 9 := by
  by_cases hle : r ≤ a / 2 + 5 * 10 ^ 9
  · exact hle
  · have hlt : a / 2 + 5 * 10 ^ 9 + 1 ≤ r := by omega
    have hmod := Nat.div_add_mod a 2
    have hlt2 := Nat.mod_lt a (show (0 : Nat) < 2 by decide)
    have hAle : a ≤ 2 * (a / 2) + 1 := by omega
    have hSle : S ≤ (2 * (a / 2) + 1) * (10 ^ 10) := by
      rw [hS]
      exact Nat.mul_le_mul_right _ hAle
    have mval : 5 * 10 ^ 9 = 5000000000 := by decide
    rw [mval] at hlt
    have hsq : (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) ≤ r * r :=
      Nat.mul_le_mul hlt hlt
    have h10 : (10 : Nat) ^ 10 = 2 * 5000000000 := by decide
    rw [h10] at hSle
    have key := seedKey (a / 2)
    omega

theorem floorPos {S r a : Nat} (hS : S = a * 10 ^ 10) (ha : 1 ≤ a)
    (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1)) : 1 ≤ r := by
  by_cases hr0 : r = 0
  · subst hr0
    have e : (0 + 1) * (0 + 1) = 1 := by decide
    rw [e] at h2
    have o : (1 : Nat) * 10 ^ 10 = 10000000000 := by decide
    have h10 : (1 : Nat) * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha
    omega
  · exact Nat.pos_of_ne_zero hr0

theorem rBound {S r a : Nat} (hS : S = a * 10 ^ 10) (ha : a ≤ 2 ^ 167 - 1)
    (h1 : r * r ≤ S) : r < 2 ^ 101 := by
  have mval : (10 : Nat) ^ 10 < 2 ^ 34 := by decide
  have hS1 : S < 2 ^ 201 := by
    have hle : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 := Nat.mul_le_mul_right _ ha
    have hle2 : (2 ^ 167 - 1) * 10 ^ 10 ≤ (2 ^ 167 - 1) * 2 ^ 34 :=
      Nat.mul_le_mul_left _ (by omega)
    have e201 : (2 ^ 167 - 1) * 2 ^ 34 = 2 ^ 201 - 2 ^ 34 := by
      have p : (2 : Nat) ^ 167 * 2 ^ 34 = 2 ^ 201 := by decide
      have s1 : (2 ^ 167 - 1) * 2 ^ 34 = 2 ^ 167 * 2 ^ 34 - 1 * 2 ^ 34 :=
        Nat.sub_mul _ _ _
      have o1 : (1 : Nat) * 2 ^ 34 = 2 ^ 34 := Nat.one_mul _
      omega
    omega
  have e202 : (2 : Nat) ^ 101 * (2 ^ 101) = 2 ^ 202 := by decide
  have c : (2 : Nat) ^ 201 ≤ 2 ^ 202 := by decide
  by_cases hle : r < 2 ^ 101
  · exact hle
  · have hge : (2 : Nat) ^ 101 * (2 ^ 101) ≤ r * r :=
      Nat.mul_le_mul (by omega : (2 : Nat) ^ 101 ≤ r) (by omega : (2 : Nat) ^ 101 ≤ r)
    omega

theorem rangeBound {a r : Nat} (ha : a ≤ 2 ^ 167 - 1) (hr : r < 2 ^ 101) :
    a / 2 + 5 * 10 ^ 9 + (r + 2) + 1 ≤ 2 ^ 167 - 1 := by
  have p167 : (0 : Nat) < 2 ^ 167 := by decide
  have p101 : (0 : Nat) < 2 ^ 101 := by decide
  have hadd : (2 : Nat) ^ 166 + 2 ^ 101 + 5000000000 + 1 ≤ 2 ^ 167 - 1 := by decide
  have mval : 5 * 10 ^ 9 = 5000000000 := by decide
  have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right ha
  have ediv : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
  omega

theorem loopRange {a S r z : Nat} (hS : S = a * 10 ^ 10) (ha : a ≤ 2 ^ 167 - 1)
    (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1)) (hr101 : r < 2 ^ 101)
    (hr1 : 1 ≤ r) (hrz : r ≤ z) (hz : z ≤ a / 2 + 5 * 10 ^ 9 + 1) :
    S / z + z ≤ 2 ^ 167 - 1 := by
  have e1 := sqSucc r
  have hSle : S ≤ r * r + 2 * r := by omega
  have hlt : S < z * (r + 3) := by
    have a1 : z * (r + 3) = z * r + z * 3 := Nat.mul_add _ _ _
    have b1 : r * r ≤ z * r := Nat.mul_le_mul_right _ hrz
    have b2 : r * 3 ≤ z * 3 := Nat.mul_le_mul_right _ hrz
    have c1 : r * 3 = 3 * r := Nat.mul_comm _ _
    have c2 : z * 3 = 3 * z := Nat.mul_comm _ _
    omega
  have hq : S / z ≤ r + 2 := by
    by_cases hle2 : S / z ≤ r + 2
    · exact hle2
    · have hgt : r + 3 ≤ S / z := by omega
      have h5 : (r + 3) * z ≤ S / z * z := Nat.mul_le_mul_right _ hgt
      have h6 : S / z * z ≤ S := Nat.div_mul_le_self _ _
      have h7 : z * (r + 3) = (r + 3) * z := Nat.mul_comm _ _
      omega
  have hrb := rangeBound ha hr101
  omega

theorem seqBounds {S r s : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hr1 : 1 ≤ r) (hs0 : r ≤ s) :
    ∀ k, r ≤ seqN S s k ∧ seqN S s k ≤ s + 1 := by
  intro k
  induction k with
  | zero => exact ⟨hs0, Nat.le_succ _⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hz : 0 < seqN S s k := by omega
    have hlo := stepLower h1 h2 ih1 hz
    have hup : stepN S (seqN S s k) ≤ s + 1 := by
      by_cases hle : r + 1 ≤ seqN S s k
      · have h := stepUpper h1 h2 hle
        have h2' : r + (seqN S s k - r) / 2 ≤ seqN S s k := by omega
        omega
      · have hzr : seqN S s k = r := by omega
        have h := stepAtRUpper h1 h2
        rw [hzr]
        omega
    show r ≤ stepN S (seqN S s k) ∧ stepN S (seqN S s k) ≤ s + 1
    exact ⟨hlo, hup⟩

theorem seqConverge {S r s : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hb : ∀ k, r ≤ seqN S s k) (hs0 : r ≤ s) :
    ∀ k, seqN S s k ≤ r + 1 ∨ 2 ^ k * (seqN S s k - r) ≤ s - r := by
  intro k
  induction k with
  | zero =>
    refine Or.inr ?_
    have p : (2 : Nat) ^ 0 = 1 := by decide
    rw [p, seqZero, Nat.one_mul]
    exact Nat.le_refl _
  | succ k ih =>
    by_cases hle : seqN S s k ≤ r + 1
    · refine Or.inl ?_
      have hbk := hb k
      by_cases heq : seqN S s k = r
      · have hup := stepAtRUpper h1 h2
        rw [seqSucc, heq]
        exact hup
      · have heq2 : seqN S s k = r + 1 := by omega
        rw [seqSucc, heq2, stepAtSucc h1 h2]
        exact Nat.le_succ _
    · have hbk := hb k
      have hle2 : r + 1 ≤ seqN S s k := by omega
      have hB := Or.resolve_left ih hle
      have hup := stepUpper h1 h2 hle2
      have hbkk : r ≤ seqN S s (k + 1) := hb (k + 1)
      rw [seqSucc] at hbkk
      have hstep_sub : stepN S (seqN S s k) - r ≤ (seqN S s k - r) / 2 := by omega
      have h2x : 2 * (stepN S (seqN S s k) - r) ≤ seqN S s k - r := by
        have dm := Nat.div_mul_le_self (seqN S s k - r) 2
        have ml := Nat.mul_le_mul_left 2 hstep_sub
        have c : (2 : Nat) * ((seqN S s k - r) / 2) = (seqN S s k - r) / 2 * 2 :=
          Nat.mul_comm _ _
        omega
      have p : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ _ _
      have hfin : 2 ^ (k + 1) * (seqN S s (k + 1) - r) ≤ s - r := by
        rw [seqSucc, p]
        have m1 : (2 ^ k * 2) * (stepN S (seqN S s k) - r)
            = 2 ^ k * (2 * (stepN S (seqN S s k) - r)) := Nat.mul_assoc _ _ _
        rw [m1]
        exact Nat.le_trans (Nat.mul_le_mul_left _ h2x) hB
      exact Or.inr hfin

theorem stepStable {S r z : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hrz : r ≤ z) (hz : z ≤ r + 1) : stepN S z ≤ r + 1 := by
  by_cases heq : z = r
  · rw [heq]
    exact stepAtRUpper h1 h2
  · have heq2 : z = r + 1 := by omega
    rw [heq2, stepAtSucc h1 h2]
    exact Nat.le_succ _

theorem seqStable167 {S r s : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hb : ∀ k, r ≤ seqN S s k) (hs0 : r ≤ s)
    (hconv : ∀ k, seqN S s k ≤ r + 1 ∨ 2 ^ k * (seqN S s k - r) ≤ s - r)
    (hsr : s - r < 2 ^ 167) : seqN S s 167 ≤ r + 1 := by
  have h := hconv 167
  cases h with
  | inl h => exact h
  | inr h =>
    have hb167 := hb 167
    by_cases he : seqN S s 167 - r = 0
    · omega
    · have hpos : 1 ≤ seqN S s 167 - r := Nat.pos_of_ne_zero he
      have hge : 2 ^ 167 ≤ 2 ^ 167 * (seqN S s 167 - r) := by
        have m := Nat.mul_le_mul_left (2 ^ 167) hpos
        have o : (2 : Nat) ^ 167 * 1 = 2 ^ 167 := Nat.mul_one _
        omega
      omega

theorem seqStableAll {S r s : Nat} (h1 : r * r ≤ S) (h2 : S < (r + 1) * (r + 1))
    (hb : ∀ k, r ≤ seqN S s k)
    (h167 : seqN S s 167 ≤ r + 1) :
    ∀ k, 167 ≤ k → seqN S s k ≤ r + 1 := by
  intro k hk
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  subst hd
  induction d with
  | zero =>
    have e : 167 + 0 = 167 := by omega
    rw [e]
    exact h167
  | succ d ih =>
    have h1d := hb (167 + d)
    have e : 167 + (d + 1) = (167 + d) + 1 := by omega
    rw [e, seqSucc]
    by_cases heq : seqN S s (167 + d) = r
    · rw [heq]
      exact stepAtRUpper h1 h2
    · have heq2 : seqN S s (167 + d) = r + 1 := by omega
      rw [heq2, stepAtSucc h1 h2]
      exact Nat.le_succ _

theorem advanceStep {a r j n : Nat}
    (ha : a ≤ 2 ^ 167 - 1) (ha1 : 1 ≤ a)
    (h1 : r * r ≤ a * 10 ^ 10) (h2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hr101 : r < 2 ^ 101) (hr1 : 1 ≤ r)
    (hb : ∀ k, r ≤ seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k)
    (hs0 : r ≤ a / 2 + 5 * 10 ^ 9)
    (hne : ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
      ≠ ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)) :
    loop (a : Int) (n + 1) ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
      ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
    = loop (a : Int) n ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
      ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 2) : Nat) : Int) := by
  have hz : 0 < seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) := by
    have hbj := hb (j + 1)
    omega
  have hneN : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1)
      ≠ seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j :=
    fun h => hne (congrArg (fun n : Nat => (n : Int)) h)
  have hbound := (seqBounds h1 h2 hr1 hs0) (j + 1)
  have hrange : a * 10 ^ 10 / seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1)
      + seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) ≤ 2 ^ 167 - 1 :=
    loopRange rfl ha h1 h2 hr101 hr1 hbound.1 hbound.2
  have hstep := loop_step (a := a)
    (y := seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j)
    (z := seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1)) n hz hneN hrange
  have e : (((a * 10 ^ 10 / seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1)
      + seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1)) / 2 : Nat) : Int)
      = ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 2) : Nat) : Int) := rfl
  rw [e] at hstep
  exact hstep

theorem advanceOr2 {a r : Nat}
    (ha : a ≤ 2 ^ 167 - 1) (ha1 : 1 ≤ a)
    (h1 : r * r ≤ a * 10 ^ 10) (h2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hr101 : r < 2 ^ 101) (hr1 : 1 ≤ r)
    (hb : ∀ k, r ≤ seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k)
    (hs0 : r ≤ a / 2 + 5 * 10 ^ 9)
    (t : Nat) (ht : 1 + t ≤ 168) :
    loop (a : Int) 255 ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
      ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) 1 : Nat) : Int)
    = loop (a : Int) (255 - t)
      ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t : Nat) : Int)
      ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (t + 1) : Nat) : Int)
    ∨ loop (a : Int) 255 ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
      ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) 1 : Nat) : Int)
      = some ((r : Int), (r : Int)) := by
  induction t with
  | zero =>
    exact Or.inl rfl
  | succ t ih =>
    have ht' : 1 + t ≤ 168 := by omega
    have ih' := ih ht'
    cases ih' with
    | inr h => exact Or.inr h
    | inl h =>
      have hne : 255 - t ≠ 0 := by omega
      obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [hu] at h
      by_cases hEq : ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (t + 1) : Nat) : Int)
          = ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t : Nat) : Int)
      · have hNt1 : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (t + 1)
            = seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t := Int.ofNat.inj hEq
        have hstep : stepN (a * 10 ^ 10) (seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t)
            = seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t := by
          rw [←seqSucc]
          exact hNt1
        have hfix : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t = r :=
          stepFixed h1 h2 (hb t) hstep
        have hstop : loop (a : Int) (u.succ)
            ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t : Nat) : Int)
            ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (t + 1) : Nat) : Int)
            = some ((r : Int), (r : Int)) := by
          rw [hEq]
          have hs : loop (a : Int) (u.succ)
              ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t : Nat) : Int)
              ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t : Nat) : Int)
              = some ((((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t : Nat) : Int)),
                (((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) t : Nat) : Int))) :=
            loop_stop _ _ _
          rw [hs, hfix]
        exact Or.inr (h.trans hstop)
      · have hadv := advanceStep ha ha1 h1 h2 hr101 hr1 hb hs0 (n := u) (j := t) hEq
        have huv : u = 255 - (t + 1) := by omega
        have hmid : loop (a : Int) 255 ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
            ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) 1 : Nat) : Int)
            = loop (a : Int) u
              ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (t + 1) : Nat) : Int)
              ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (t + 2) : Nat) : Int) :=
          h.trans hadv
        rw [huv] at hmid
        exact Or.inl hmid

theorem stableOutcome {a r : Nat}
    (ha : a ≤ 2 ^ 167 - 1) (ha1 : 1 ≤ a)
    (h1 : r * r ≤ a * 10 ^ 10) (h2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hr101 : r < 2 ^ 101) (hr1 : 1 ≤ r)
    (hb : ∀ k, r ≤ seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k)
    (hs0 : r ≤ a / 2 + 5 * 10 ^ 9)
    (h167 : ∀ k, 167 ≤ k → seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k ≤ r + 1)
    (t j : Nat) (hj : 167 ≤ j) (hjt : j + t ≤ 256) :
    (loop (a : Int) t ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
      ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)).map
      (fun p => minFin p.1 p.2) = some (r : Int) := by
  induction t generalizing j with
  | zero =>
    have hbj := hb j
    have hbj1 := hb (j + 1)
    have hsj := h167 j hj
    have hsj1 := h167 (j + 1) (by omega)
    have e0 : loop (a : Int) 0 ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
        ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
        = some ((((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)),
          (((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int))) := rfl
    rw [e0]
    have hmin : (if ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
        < ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
        then ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
        else ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int))
        = (r : Int) := by
      by_cases hyr : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j = r
      · rw [hyr]
        by_cases hlt : (r : Int)
            < ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
        · rw [if_pos hlt]
        · rw [if_neg hlt]
          exact Int.le_antisymm (by omega) (Int.ofNat_le.mpr (hb (j + 1)))
      · have hyr1 : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j = r + 1 := by omega
        by_cases hzr : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) = r
        · rw [hyr1, hzr, if_neg (by omega)]
        · have hz1 : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) = r + 1 := by omega
          have hstep : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1)
              = stepN (a * 10 ^ 10) (seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j) :=
            seqSucc
          rw [hyr1] at hstep
          rw [stepAtSucc h1 h2] at hstep
          omega
    show some (if ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
        < ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
        then ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
        else ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int))
        = some (r : Int)
    rw [hmin]
  | succ t ih =>
    by_cases hEq : ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
        = ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
    · have hNt1 : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1)
          = seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j := Int.ofNat.inj hEq
      have hstep : stepN (a * 10 ^ 10) (seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j)
          = seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j := by
        rw [←seqSucc]
        exact hNt1
      have hfix : seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j = r :=
        stepFixed h1 h2 (hb j) hstep
      have hstop : loop (a : Int) (t + 1)
          ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
          ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (j + 1) : Nat) : Int)
          = some ((((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)),
            (((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int))) := by
        rw [hEq]
        exact loop_stop _ _ _
      rw [hstop]
      show some (if ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
          < ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
          then ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int)
          else ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) j : Nat) : Int))
          = some (r : Int)
      rw [if_neg (by omega), hfix]
    · have hadv := advanceStep ha ha1 h1 h2 hr101 hr1 hb hs0 (n := t) (j := j) hEq
      rw [hadv]
      exact ih (j + 1) (by omega) (by omega)

theorem masterLoop {a : Nat} (ha1 : 1 ≤ a) (ha2 : a ≤ 2 ^ 167 - 1) :
    ∃ m : Nat, vyperSqrtWith minFin (a : Int)
      = some ((m : Nat) : Int) ∧ m * m ≤ a * 10 ^ 10 ∧ a * 10 ^ 10 < (m + 1) * (m + 1) := by
  obtain ⟨r, h1, h2⟩ := floorEx (a * 10 ^ 10)
  have hr1 := floorPos rfl ha1 h1 h2
  have hr101 := rBound rfl ha2 h1
  have hs0 := seedLower rfl h1 h2
  have hb : ∀ k, r ≤ seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k :=
    fun k => (seqBounds h1 h2 hr1 hs0 k).1
  have hconv := seqConverge h1 h2 hb hs0
  have hsr : a / 2 + 5 * 10 ^ 9 - r < 2 ^ 167 := by
    have hrb := rangeBound ha2 hr101
    have p167 : (0 : Nat) < 2 ^ 167 := by decide
    omega
  have h167pt := seqStable167 h1 h2 hb hs0 hconv hsr
  have h167all := seqStableAll h1 h2 hb h167pt
  have hpos := vyperSqrtWith_pos minFin ha1 ha2
  rw [hpos]
  by_cases heq0 : (a : Int) = ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
  · have haN : a = a / 2 + 5 * 10 ^ 9 := Int.ofNat.inj heq0
    have hmod := Nat.div_add_mod a 2
    have hlt2 := Nat.mod_lt a (show (0 : Nat) < 2 by decide)
    have mval : 5 * 10 ^ 9 = 5000000000 := by decide
    have ha10 : a = 10000000000 ∨ a = 9999999999 := by omega
    have hloop : loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
        = some ((a : Int), (a : Int)) := by
      have e256 : (256 : Nat) = 255 + 1 := by decide
      rw [e256, heq0]
      exact loop_stop _ _ _
    rw [hloop]
    have hmap : ((some ((a : Int), (a : Int))).map (fun p => minFin p.1 p.2))
        = some (a : Int) := by
      show some (if (a : Int) < (a : Int) then (a : Int) else (a : Int)) = some (a : Int)
      rw [if_neg (by omega)]
    rw [hmap]
    cases ha10 with
    | inl h =>
      subst h
      exact ⟨10000000000, rfl, by decide, by decide⟩
    | inr h =>
      subst h
      exact ⟨9999999999, rfl, by decide, by decide⟩
  · have hz0 : 0 < a / 2 + 5 * 10 ^ 9 := by
      have h5 : 0 < 5 * 10 ^ 9 := by decide
      omega
    have hrange0 : a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9) + (a / 2 + 5 * 10 ^ 9)
        ≤ 2 ^ 167 - 1 :=
      loopRange rfl ha2 h1 h2 hr101 hr1 hs0 (by omega)
    have hstepA := loop_step (a := a) (y := a) (z := a / 2 + 5 * 10 ^ 9) 255 hz0
      (fun h => heq0 (congrArg (fun n : Nat => (n : Int)) h).symm) hrange0
    have eA : (((a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9) + (a / 2 + 5 * 10 ^ 9)) / 2 : Nat) : Int)
        = ((seqN (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) 1 : Nat) : Int) := rfl
    rw [eA] at hstepA
    rw [hstepA]
    have hadv := advanceOr2 ha2 ha1 h1 h2 hr101 hr1 hb hs0 167 (by decide)
    have e88 : (255 : Nat) - 167 = 88 := by decide
    cases hadv with
    | inr hR =>
      rw [hR]
      refine ⟨r, ?_, h1, h2⟩
      show some (if (r : Int) < (r : Int) then (r : Int) else (r : Int))
        = some ((r : Nat) : Int)
      rw [if_neg (by omega)]
    | inl hL =>
      rw [e88] at hL
      rw [hL]
      refine ⟨r, ?_, h1, h2⟩
      exact stableOutcome ha2 ha1 h1 h2 hr101 hr1 hb hs0 h167all 88 167
        (by decide) (by decide)

theorem sqrtSome {x : Int} (hx : IsDecimal x) (hx0 : 0 ≤ x) :
    ∃ a m : Nat, x = ((a : Nat) : Int) ∧ sqrt x = some ((m : Nat) : Int)
      ∧ m * m ≤ a * 10 ^ 10 ∧ a * 10 ^ 10 < (m + 1) * (m + 1)
      ∧ a ≤ 2 ^ 167 - 1 := by
  unfold IsDecimal at hx
  obtain ⟨hlo, hhi⟩ := hx
  have hmax : MAX_DECIMAL = ((2 ^ 167 - 1 : Nat) : Int) := max_decimal_eq
  rw [hmax] at hhi
  obtain ⟨a, ha⟩ : ∃ a : Nat, ((a : Nat) : Int) = x := ⟨x.toNat, Int.toNat_of_nonneg hx0⟩
  subst ha
  have ha2 : a ≤ 2 ^ 167 - 1 := Int.ofNat_le.mp hhi
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : sqrt (((0 : Nat)) : Int) = some (((0 : Nat)) : Int) := by
      show vyperSqrtWith minFin ((0 : Nat) : Int) = some (((0 : Nat)) : Int)
      unfold vyperSqrtWith
      simp
    exact ⟨0, 0, rfl, h0, by decide, by decide, by decide⟩
  · have ha1 : 1 ≤ a := by omega
    obtain ⟨m, hm, hml, hmu⟩ := masterLoop ha1 ha2
    have hm2 : sqrt ((a : Nat) : Int) = some ((m : Nat) : Int) := hm
    exact ⟨a, m, rfl, hm2, hml, hmu, ha2⟩

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith minFin x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hr
  by_cases hx0 : x < 0
  · have hnone := req_sqrt_neg_reverts x hx0
    rw [hr] at hnone
    simp at hnone
  · have hx0' : 0 ≤ x := by omega
    obtain ⟨a, m, hxa, hsm, hml, hmu, ha2⟩ := sqrtSome hx hx0'
    have hmr : ((m : Nat) : Int) = r := Option.some_inj.mp (hsm.symm.trans hr)
    subst hmr
    rw [hxa]
    have d : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
    rw [d]
    have c1 : (m : Int) * (m : Int) = ((m * m : Nat) : Int) := by simp
    have c2 : (a : Int) * (((10 ^ 10 : Nat)) : Int) = ((a * 10 ^ 10 : Nat) : Int) := by simp
    rw [c1, c2]
    exact Int.ofNat_le.mpr hml

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hr
  by_cases hx0 : x < 0
  · have hnone := req_sqrt_neg_reverts x hx0
    rw [hr] at hnone
    simp at hnone
  · have hx0' : 0 ≤ x := by omega
    obtain ⟨a, m, hxa, hsm, hml, hmu, ha2⟩ := sqrtSome hx hx0'
    have hmr : ((m : Nat) : Int) = r := Option.some_inj.mp (hsm.symm.trans hr)
    subst hmr
    rw [hxa]
    have d : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
    rw [d]
    have c2 : (a : Int) * (((10 ^ 10 : Nat)) : Int) = ((a * 10 ^ 10 : Nat) : Int) := by simp
    have c3 : ((m : Int) + 1) * ((m : Int) + 1) = (((m + 1) * (m + 1) : Nat) : Int) := by simp
    rw [c2, c3]
    exact Int.ofNat_lt.mpr hmu

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hx0
  obtain ⟨a, m, hxa, hsm, hml, hmu, ha2⟩ := sqrtSome hx hx0
  rw [hsm]
  rfl

theorem req_deployed_loop : DeployedLoop sqrt := by
  exact ⟨minFin, fun x => rfl⟩

end VyperSqrt

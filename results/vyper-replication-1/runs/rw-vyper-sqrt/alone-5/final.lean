import Init.Data.Nat.Lemmas
import Init.Data.Int.Lemmas
import VyperSqrt.Spec
import VyperSqrt.Lemmas

/-! Fix: round the Babylonian loop result down by taking the minimum of the
last two iterates (Vyper PR 4486). The rest of this file proves that this
routine returns the integer square root rounded down. -/

namespace VyperSqrt

-- Basic square expansion, proved by distributivity then linear arithmetic.
theorem sq_succ_eq (r : Nat) : (r + 1) * (r + 1) = r * r + (2 * r + 1) := by
  have e : (r + 1) * (r + 1) = r * r + (r + (r + 1)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  omega

-- If x + y ≤ 2 * r then x * y ≤ r * r.
theorem prod_le_sq (x y r : Nat) (h : x + y ≤ 2 * r) : x * y ≤ r * r := by
  rcases Nat.le_total x y with hxy | hyx
  · have hxr : x ≤ r := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxr
    have hy : y ≤ x + (d + d) := by omega
    have h1 : x * y ≤ x * (x + (d + d)) := Nat.mul_le_mul_left x hy
    have e : (x + d) * (x + d) = x * (x + (d + d)) + d * d := by
      have c1 : d * x = x * d := Nat.mul_comm _ _
      simp only [Nat.add_mul, Nat.mul_add, c1]
      omega
    have h2 : x * (x + (d + d)) ≤ (x + d) * (x + d) := by omega
    exact Nat.le_trans h1 h2
  · have hyr : y ≤ r := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hyr
    have hx : x ≤ y + (d + d) := by omega
    have h1 : x * y = y * x := Nat.mul_comm _ _
    have h2 : y * x ≤ y * (y + (d + d)) := Nat.mul_le_mul_left y hx
    have e : (y + d) * (y + d) = y * (y + (d + d)) + d * d := by
      have c1 : d * y = y * d := Nat.mul_comm _ _
      simp only [Nat.add_mul, Nat.mul_add, c1]
      omega
    have h3 : y * (y + (d + d)) ≤ (y + d) * (y + d) := by omega
    rw [h1]
    exact Nat.le_trans h2 h3

-- Every natural has an integer square root (floor), with spec.
theorem exists_sqrt : ∀ N : Nat, ∃ r : Nat, r * r ≤ N ∧ N < (r + 1) * (r + 1) := by
  intro N
  induction N with
  | zero => exact ⟨0, Nat.zero_le _, by decide⟩
  | succ n ih =>
    obtain ⟨r, h1, h2⟩ := ih
    by_cases h : n + 1 < (r + 1) * (r + 1)
    · exact ⟨r, by omega, h⟩
    · have hle : (r + 1) * (r + 1) ≤ n + 1 := by omega
      have hsucc : n + 1 ≤ (r + 1) * (r + 1) := Nat.succ_le_of_lt h2
      have heq : n + 1 = (r + 1) * (r + 1) := by omega
      refine ⟨r + 1, by omega, ?_⟩
      have e : (r + 1 + 1) * (r + 1 + 1)
          = (r + 1) * (r + 1) + (2 * (r + 1) + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      omega

-- Newton step and iterates for `N = a * 10^10`, seed `a / 2 + 5 * 10^9`.
def nstep (N s : Nat) : Nat := (N / s + s) / 2

def nseq (a : Nat) : Nat → Nat
  | 0 => a / 2 + 5 * 10 ^ 9
  | n + 1 => nstep (a * 10 ^ 10) (nseq a n)

-- If `r + 1 ≤ s` then `N / s ≤ r`.
theorem q_le_of_ge_succ {N r s : Nat} (hr2 : N < (r + 1) * (r + 1))
    (hs : r + 1 ≤ s) : N / s ≤ r := by
  have hmul : (r + 1) * (r + 1) ≤ s * (r + 1) := Nat.mul_le_mul_right _ hs
  have hlt : N < s * (r + 1) := by omega
  have hlt2 : N < (r + 1) * s := by
    have c : s * (r + 1) = (r + 1) * s := Nat.mul_comm _ _
    omega
  have h3 : N / s < r + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < s)).mpr hlt2
  omega

-- If `r ≤ s` then `N / s ≤ r + 2`.
theorem q_le_of_ge {N r s : Nat} (hr2 : N < (r + 1) * (r + 1))
    (hrs : r ≤ s) : N / s ≤ r + 2 := by
  have e : (r + 1) * (r + 1) = r * (r + 2) + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have hN : N ≤ r * (r + 2) := by omega
  have hmul : r * (r + 2) ≤ s * (r + 2) := Nat.mul_le_mul_right _ hrs
  have hle : N ≤ s * (r + 2) := Nat.le_trans hN hmul
  exact Nat.div_le_of_le_mul hle

-- The Newton step never goes below `r`.
theorem newton_ge {N r s : Nat} (hr1 : r * r ≤ N) (hs : 1 ≤ s) :
    r ≤ (N / s + s) / 2 := by
  cases r with
  | zero => exact Nat.zero_le _
  | succ r =>
    by_cases hlt : (N / s + s) / 2 < r + 1
    · have h2 : N / s + s < (r + 1) * 2 :=
        (Nat.div_lt_iff_lt_mul (by decide)).mp hlt
      have h3 : (N / s + 1) + s ≤ 2 * (r + 1) := by omega
      have h4 : (N / s + 1) * s ≤ (r + 1) * (r + 1) := prod_le_sq _ _ _ h3
      have hmod := Nat.div_add_mod N s
      have hrem := Nat.mod_lt N (by omega : 0 < s)
      have h5 : N < (N / s + 1) * s := by
        have e3 : s * (N / s + 1) = s * (N / s) + s := by
          rw [Nat.mul_add, Nat.mul_one]
        have e4 : s * (N / s + 1) = (N / s + 1) * s := Nat.mul_comm _ _
        omega
      have h6 : (N / s + 1) * s ≤ N := Nat.le_trans h4 hr1
      omega
    · omega

-- Above `r`, the Newton step strictly decreases.
theorem newton_lt {N r s : Nat} (hr2 : N < (r + 1) * (r + 1))
    (hs : r + 1 ≤ s) : (N / s + s) / 2 < s := by
  have hge : (r + 1) * (r + 1) ≤ s * s := Nat.mul_le_mul hs hs
  have hNss : N < s * s := by omega
  have hq : N / s < s :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < s)).mpr hNss
  have hqq : N / s + s < s * 2 := by
    have e := Nat.mul_two s
    omega
  exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hqq

-- Above `r`, the distance to `r + 1` at least halves.
theorem newton_half {N r s : Nat} (hr2 : N < (r + 1) * (r + 1))
    (hs : r + 1 ≤ s) : (N / s + s) / 2 - (r + 1) ≤ (s - (r + 1)) / 2 := by
  have hq : N / s ≤ r := q_le_of_ge_succ hr2 hs
  have hdiv : 2 * ((N / s + s) / 2) ≤ N / s + s := by
    have h := Nat.div_mul_le_self (N / s + s) 2
    omega
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  omega

-- The seed is a decimal whenever the input is.
theorem seed_le_max {a : Nat} (h : a ≤ 2 ^ 167 - 1) :
    a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := by
  omega

-- Strict seed inequality: `((w + w) + 1) * (v + v) < (w + v + 1)^2`.
theorem seed_strict (w v : Nat) :
    ((w + w) + 1) * (v + v) < (w + v + 1) * (w + v + 1) := by
  rcases Nat.le_total w v with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have c1 : w * d = d * w := Nat.mul_comm _ _
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, c1]
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have c1 : v * d = d * v := Nat.mul_comm _ _
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, c1]
    omega

-- The seed is at least `r`.
theorem seed_ge {a r : Nat} (hr1 : r * r ≤ a * 10 ^ 10)
    (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1)) : r ≤ a / 2 + 5 * 10 ^ 9 := by
  by_cases hle : r ≤ a / 2 + 5 * 10 ^ 9
  · exact hle
  · have hlt : a / 2 + 5 * 10 ^ 9 + 1 ≤ r := by omega
    have hsq : (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) ≤ r * r :=
      Nat.mul_le_mul hlt hlt
    have ha : a ≤ (a / 2 + a / 2) + 1 := by
      have hdm := Nat.div_add_mod a 2
      have hm := Nat.mod_lt a (by decide : 0 < 2)
      omega
    have hD : (10 ^ 10 : Nat) = (5 * 10 ^ 9) + (5 * 10 ^ 9) := by decide
    have hle2 : (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1)
        ≤ ((a / 2 + a / 2) + 1) * ((5 * 10 ^ 9) + (5 * 10 ^ 9)) := by
      have g3 : a * 10 ^ 10
          ≤ ((a / 2 + a / 2) + 1) * ((5 * 10 ^ 9) + (5 * 10 ^ 9)) := by
        have m1 : a ≤ (a / 2 + a / 2) + 1 := ha
        have m2 : (10 ^ 10 : Nat) ≤ (5 * 10 ^ 9) + (5 * 10 ^ 9) := by
          rw [hD]
          exact Nat.le_refl _
        exact Nat.mul_le_mul m1 m2
      exact Nat.le_trans hsq (Nat.le_trans hr1 g3)
    have hstrict := seed_strict (a / 2) (5 * 10 ^ 9)
    omega

-- Positive input has positive root.
theorem r_pos_of_a_pos {a r : Nat} (ha : 1 ≤ a) (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1)) :
    1 ≤ r := by
  by_cases h : 1 ≤ r
  · exact h
  · have hr0 : r = 0 := by omega
    rw [hr0] at hr2
    have hN : 1 * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha
    omega

-- All iterates stay at least `r`.
theorem nseq_ge {a r : Nat} (hr1 : r * r ≤ a * 10 ^ 10)
    (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hrpos : 1 ≤ r) (hseed : r ≤ a / 2 + 5 * 10 ^ 9) :
    ∀ i, r ≤ nseq a i := by
  intro i
  induction i with
  | zero =>
    show r ≤ a / 2 + 5 * 10 ^ 9
    exact hseed
  | succ k ih =>
    have h1 : 1 ≤ nseq a k := Nat.le_trans hrpos ih
    show r ≤ nstep (a * 10 ^ 10) (nseq a k)
    show r ≤ (a * 10 ^ 10 / nseq a k + nseq a k) / 2
    exact newton_ge hr1 h1

-- The step from `r + 1` lands exactly on `r`.
theorem newton_at_succ {N r : Nat} (hr1 : r * r ≤ N)
    (hr2 : N < (r + 1) * (r + 1)) (hrpos : 1 ≤ r) :
    (N / (r + 1) + (r + 1)) / 2 = r := by
  have hq1 : N / (r + 1) ≤ r := q_le_of_ge_succ hr2 (Nat.le_refl _)
  have e : r * r = (r - 1) * (r + 1) + 1 := by
    cases r with
    | zero => omega
    | succ t =>
      have s1 := sq_succ_eq t
      have p1 : (t + 1 - 1) = t := Nat.add_sub_cancel _ _
      have p2 : (t + 1 + 1) = t + 2 := by omega
      rw [p1, p2]
      have m1 : t * (t + 2) = t * t + (t + t) := by
        simp only [Nat.mul_add]
        rw [Nat.mul_two]
      omega
  have hle : (r - 1) * (r + 1) ≤ N := by omega
  have hq2 : r - 1 ≤ N / (r + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < r + 1)).mpr hle
  omega

-- The step from `r` stays in `{r, r + 1}`.
theorem newton_at {N r : Nat} (hr1 : r * r ≤ N)
    (hr2 : N < (r + 1) * (r + 1)) (hrpos : 1 ≤ r) :
    (N / r + r) / 2 = r ∨ (N / r + r) / 2 = r + 1 := by
  have hq1 : N / r ≤ r + 2 := q_le_of_ge hr2 (Nat.le_refl _)
  have hq2 : r ≤ N / r := (Nat.le_div_iff_mul_le hrpos).mpr hr1
  have hq : N / r = r ∨ N / r = r + 1 ∨ N / r = r + 2 := by omega
  rcases hq with h | h | h
  · have e : r + r = r * 2 := (Nat.mul_two r).symm
    have h2 : (r + r) / 2 = r := by
      rw [e]
      exact Nat.mul_div_cancel r (by decide)
    have c : N / r + r = r + r := by omega
    rw [c]
    exact Or.inl h2
  · have e : (r + 1) + r = r * 2 + 1 := by
      have t := Nat.mul_two r
      omega
    have h2 : (r * 2 + 1) / 2 = r := by
      have f : r * 2 + 1 = 1 + r * 2 := Nat.add_comm _ _
      rw [f, Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
      have g : (1 : Nat) / 2 = 0 := by decide
      rw [g, Nat.zero_add]
    have c : N / r + r = r * 2 + 1 := by omega
    rw [c]
    exact Or.inl h2
  · have e : (r + 2) + r = (r + 1) * 2 := by omega
    have h2 : ((r + 1) * 2) / 2 = r + 1 := Nat.mul_div_cancel _ (by decide)
    have c : N / r + r = (r + 1) * 2 := by omega
    rw [c]
    exact Or.inr h2

-- All iterates stay below `seed + 1`.
theorem nseq_le {a r : Nat} (hr1 : r * r ≤ a * 10 ^ 10)
    (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hrpos : 1 ≤ r) (hseed : r ≤ a / 2 + 5 * 10 ^ 9) :
    ∀ i, nseq a i ≤ (a / 2 + 5 * 10 ^ 9) + 1 := by
  intro i
  induction i with
  | zero =>
    show a / 2 + 5 * 10 ^ 9 ≤ (a / 2 + 5 * 10 ^ 9) + 1
    omega
  | succ k ih =>
    have hge : r ≤ nseq a k := nseq_ge hr1 hr2 hrpos hseed k
    show nstep (a * 10 ^ 10) (nseq a k) ≤ (a / 2 + 5 * 10 ^ 9) + 1
    show (a * 10 ^ 10 / nseq a k + nseq a k) / 2 ≤ (a / 2 + 5 * 10 ^ 9) + 1
    by_cases h : r + 1 ≤ nseq a k
    · have hlt := newton_lt (N := a * 10 ^ 10) hr2 h
      omega
    · have hrk : nseq a k = r := by omega
      have hfr : (a * 10 ^ 10 / nseq a k + nseq a k) / 2 ≤ r + 1 := by
        rw [hrk]
        have hat := newton_at (N := a * 10 ^ 10) hr1 hr2 hrpos
        omega
      omega

-- Power bound on `r`.
theorem r_le_pow {a r : Nat} (hamax : a ≤ 2 ^ 167 - 1)
    (hr1 : r * r ≤ a * 10 ^ 10) : r ≤ 2 ^ 101 := by
  by_cases h : r ≤ 2 ^ 101
  · exact h
  · have hlt : 2 ^ 101 ≤ r := by omega
    have h1 : (2 ^ 101) * (2 ^ 101) ≤ r * r := Nat.mul_le_mul hlt hlt
    have h2 : ((2 ^ 101) * (2 ^ 101) : Nat) = 2 ^ 202 := by decide
    have hN : a * 10 ^ 10 ≤ 2 ^ 167 * 2 ^ 34 := by
      have m1 : a ≤ 2 ^ 167 := by omega
      have m2 : (10 ^ 10 : Nat) ≤ 2 ^ 34 := by decide
      exact Nat.mul_le_mul m1 m2
    have h3 : (2 ^ 167 * 2 ^ 34 : Nat) = 2 ^ 201 := by decide
    omega

-- Every Newton quotient-plus-iterate stays within the decimal range.
theorem nseq_sum_le {a r : Nat} (hamax : a ≤ 2 ^ 167 - 1)
    (hr1 : r * r ≤ a * 10 ^ 10) (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hrpos : 1 ≤ r) (hseed : r ≤ a / 2 + 5 * 10 ^ 9) :
    ∀ i, a * 10 ^ 10 / nseq a i + nseq a i ≤ 2 ^ 167 - 1 := by
  intro i
  have hge : r ≤ nseq a i := nseq_ge hr1 hr2 hrpos hseed i
  have hle : nseq a i ≤ (a / 2 + 5 * 10 ^ 9) + 1 := nseq_le hr1 hr2 hrpos hseed i
  have hq : a * 10 ^ 10 / nseq a i ≤ r + 2 := q_le_of_ge hr2 hge
  have hrbound : r ≤ 2 ^ 101 := r_le_pow hamax hr1
  have hsbound : a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 166 + 5 * 10 ^ 9 := by
    have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hamax
    have h2 : ((2 ^ 167 - 1) / 2 : Nat) = 2 ^ 166 - 1 := by decide
    omega
  have hconc : (2 ^ 101 : Nat) + (2 ^ 166 + 5 * 10 ^ 9) + 3 ≤ 2 ^ 167 - 1 := by decide
  omega

-- After at most 167 steps the iterate is at most `r + 1`.
theorem nseq_reach {a r : Nat} (hamax : a ≤ 2 ^ 167 - 1)
    (hr1 : r * r ≤ a * 10 ^ 10) (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hrpos : 1 ≤ r) (hseed : r ≤ a / 2 + 5 * 10 ^ 9) :
    ∃ j, j ≤ 167 ∧ nseq a j ≤ r + 1 := by
  have key : ∀ k, k ≤ 167 →
      (∃ j, j ≤ k ∧ nseq a j ≤ r + 1) ∨
      (nseq a k - (r + 1) ≤ (nseq a 0 - (r + 1)) / 2 ^ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      by_cases h : nseq a 0 ≤ r + 1
      · exact Or.inl ⟨0, Nat.le_refl _, h⟩
      · have hD : nseq a 0 - (r + 1) = (nseq a 0 - (r + 1)) / 2 ^ 0 := by
          rw [Nat.pow_zero, Nat.div_one]
        exact Or.inr (by omega)
    | succ k ih =>
      intro hk
      have hk' : k ≤ 167 := by omega
      rcases ih hk' with h | h
      · obtain ⟨j, hjk, hj⟩ := h
        exact Or.inl ⟨j, Nat.le_trans hjk (Nat.le_succ _), hj⟩
      · by_cases hkk : nseq a (k + 1) ≤ r + 1
        · exact Or.inl ⟨k + 1, Nat.le_refl _, hkk⟩
        · by_cases hsk : nseq a k ≤ r + 1
          · exact Or.inl ⟨k, Nat.le_succ _, hsk⟩
          · have hsk' : r + 1 ≤ nseq a k := by omega
            have hhalf := newton_half (N := a * 10 ^ 10) hr2 hsk'
            have hdiv : (nseq a k - (r + 1)) / 2
                ≤ ((nseq a 0 - (r + 1)) / 2 ^ k) / 2 :=
              Nat.div_le_div_right h
            have heq : ((nseq a 0 - (r + 1)) / 2 ^ k) / 2
                = (nseq a 0 - (r + 1)) / 2 ^ (k + 1) := by
              have p : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
              rw [p, ← Nat.div_div_eq_div_mul]
            have hfin : (nseq a k - (r + 1)) / 2
                ≤ (nseq a 0 - (r + 1)) / 2 ^ (k + 1) := heq ▸ hdiv
            exact Or.inr (show (a * 10 ^ 10 / nseq a k + nseq a k) / 2 - (r + 1)
              ≤ (nseq a 0 - (r + 1)) / 2 ^ (k + 1) from Nat.le_trans hhalf hfin)
  rcases key 167 (Nat.le_refl _) with h | h
  · exact h
  · have hD0 : nseq a 0 - (r + 1) < 2 ^ 167 := by
      have hs0 := seed_le_max (a := a) hamax
      have hshow : nseq a 0 = a / 2 + 5 * 10 ^ 9 := rfl
      omega
    have hz : (nseq a 0 - (r + 1)) / 2 ^ 167 = 0 := Nat.div_eq_of_lt hD0
    have h0 : nseq a 167 - (r + 1) = 0 := by omega
    exact ⟨167, Nat.le_refl _, by omega⟩

-- Once in `{r, r + 1}`, the next iterate stays there.
theorem nseq_mem {a r : Nat} (hr1 : r * r ≤ a * 10 ^ 10)
    (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1)) (hrpos : 1 ≤ r) (i : Nat)
    (h : nseq a i = r ∨ nseq a i = r + 1) :
    nseq a (i + 1) = r ∨ nseq a (i + 1) = r + 1 := by
  have e0 : nseq a (i + 1) = nstep (a * 10 ^ 10) (nseq a i) := rfl
  have e1 : ∀ s : Nat, nstep (a * 10 ^ 10) s
      = (a * 10 ^ 10 / s + s) / 2 := fun s => rfl
  rcases h with h | h
  · have hat := newton_at (N := a * 10 ^ 10) hr1 hr2 hrpos
    have e : nseq a (i + 1) = (a * 10 ^ 10 / r + r) / 2 := by
      calc nseq a (i + 1) = nstep (a * 10 ^ 10) (nseq a i) := rfl
      _ = nstep (a * 10 ^ 10) r := by rw [h]
      _ = (a * 10 ^ 10 / r + r) / 2 := rfl
    rw [e]
    exact hat
  · have hat := newton_at_succ (N := a * 10 ^ 10) hr1 hr2 hrpos
    have e : nseq a (i + 1) = (a * 10 ^ 10 / (r + 1) + (r + 1)) / 2 := by
      calc nseq a (i + 1) = nstep (a * 10 ^ 10) (nseq a i) := rfl
      _ = nstep (a * 10 ^ 10) (r + 1) := by rw [h]
      _ = (a * 10 ^ 10 / (r + 1) + (r + 1)) / 2 := rfl
    rw [e, hat]
    exact Or.inl rfl

-- Every iterate from index 167 on is in `{r, r + 1}`.
theorem nseq_eventually {a r : Nat} (hamax : a ≤ 2 ^ 167 - 1)
    (hr1 : r * r ≤ a * 10 ^ 10) (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hrpos : 1 ≤ r) (hseed : r ≤ a / 2 + 5 * 10 ^ 9) :
    ∀ i, 167 ≤ i → nseq a i = r ∨ nseq a i = r + 1 := by
  obtain ⟨jstar, hj167, hjle⟩ := nseq_reach hamax hr1 hr2 hrpos hseed
  have hge : r ≤ nseq a jstar := nseq_ge hr1 hr2 hrpos hseed jstar
  have hmem : nseq a jstar = r ∨ nseq a jstar = r + 1 := by omega
  have hclosed : ∀ k, nseq a (jstar + k) = r ∨ nseq a (jstar + k) = r + 1 := by
    intro k
    induction k with
    | zero =>
      have z : jstar + 0 = jstar := Nat.add_zero _
      rw [z]
      exact hmem
    | succ k ih =>
      have s : jstar + (k + 1) = (jstar + k) + 1 := by omega
      rw [s]
      exact nseq_mem hr1 hr2 hrpos _ ih
  intro i hi
  have hex : ∃ k, jstar + k = i := ⟨i - jstar, by omega⟩
  obtain ⟨k, rfl⟩ := hex
  exact hclosed k

-- The deployed loop follows the Nat iterates: it either stops early at
-- `(r, r)` or runs `n` steps to `(s_{j+n}, s_{j+n+1})`.
theorem loop_follow {a r : Nat} (hamax : a ≤ 2 ^ 167 - 1)
    (hr1 : r * r ≤ a * 10 ^ 10) (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1))
    (hrpos : 1 ≤ r) (hseed : r ≤ a / 2 + 5 * 10 ^ 9) :
    ∀ n j, loop (a : Int) n ((nseq a j : Nat) : Int) ((nseq a (j + 1) : Nat) : Int)
      = some (((r : Nat) : Int), ((r : Nat) : Int))
      ∨ loop (a : Int) n ((nseq a j : Nat) : Int) ((nseq a (j + 1) : Nat) : Int)
      = some ((((nseq a (j + n) : Nat)) : Int), (((nseq a (j + n + 1) : Nat)) : Int)) := by
  intro n
  induction n with
  | zero =>
    intro j
    exact Or.inr rfl
  | succ n ih =>
    intro j
    by_cases heq : (((nseq a (j + 1) : Nat)) : Int) = (((nseq a j : Nat)) : Int)
    · have heqN : nseq a (j + 1) = nseq a j := by omega
      have hns : (a * 10 ^ 10 / nseq a j + nseq a j) / 2 = nseq a j := heqN
      have hfix : nseq a j = r := by
        have hge : r ≤ nseq a j := nseq_ge hr1 hr2 hrpos hseed j
        by_cases hle : r + 1 ≤ nseq a j
        · have hlt := newton_lt (N := a * 10 ^ 10) hr2 hle
          omega
        · omega
      have hstop : loop (a : Int) (n + 1) ((nseq a j : Nat) : Int)
            ((nseq a (j + 1) : Nat) : Int)
          = some ((((nseq a j : Nat)) : Int), (((nseq a j : Nat)) : Int)) := by
        rw [heq]
        exact loop_stop _ _ _
      rw [hstop, hfix]
      exact Or.inl rfl
    · have hne : nseq a (j + 1) ≠ nseq a j := fun c => heq (by omega)
      have hge2 : r ≤ nseq a (j + 1) := nseq_ge hr1 hr2 hrpos hseed (j + 1)
      have hz : 0 < nseq a (j + 1) := by omega
      have hb : a * 10 ^ 10 / nseq a (j + 1) + nseq a (j + 1) ≤ 2 ^ 167 - 1 :=
        nseq_sum_le hamax hr1 hr2 hrpos hseed (j + 1)
      have hstep := loop_step (a := a) (y := nseq a j) (z := nseq a (j + 1))
        n hz hne hb
      have hZ : (((a * 10 ^ 10 / nseq a (j + 1) + nseq a (j + 1)) / 2 : Nat) : Int)
          = (((nseq a ((j + 1) + 1) : Nat)) : Int) := rfl
      have e1 : (j + 1) + n = j + (n + 1) := by omega
      have ihj := ih (j + 1)
      rw [e1] at ihj
      rw [hstep, hZ]
      exact ihj

-- Uniqueness of the floor: spec determines it.
theorem floor_eq {N C r : Nat} (hr1 : r * r ≤ N) (hr2 : N < (r + 1) * (r + 1))
    (hc1 : C * C ≤ N) (hc2 : N < (C + 1) * (C + 1)) : r = C := by
  have h1 : r ≤ C := by
    by_cases h : r ≤ C
    · exact h
    · have h2 : C + 1 ≤ r := by omega
      have h3 : (C + 1) * (C + 1) ≤ r * r := Nat.mul_le_mul h2 h2
      omega
  have h2 : C ≤ r := by
    by_cases h : C ≤ r
    · exact h
    · have h3 : r + 1 ≤ C := by omega
      have h4 : (r + 1) * (r + 1) ≤ C * C := Nat.mul_le_mul h3 h3
      omega
  omega

-- The minimum of two consecutive iterates in `{r, r + 1}` is `r`.
theorem min_consec {a r p : Nat} (hr1 : r * r ≤ a * 10 ^ 10)
    (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1)) (hrpos : 1 ≤ r)
    (hp : nseq a p = r ∨ nseq a p = r + 1) :
    (if ((nseq a p : Nat) : Int) < ((nseq a (p + 1) : Nat) : Int)
      then ((nseq a p : Nat) : Int)
      else ((nseq a (p + 1) : Nat) : Int)) = ((r : Nat) : Int) := by
  rcases hp with hp | hp
  · have hat := newton_at (N := a * 10 ^ 10) hr1 hr2 hrpos
    have e : nseq a (p + 1) = (a * 10 ^ 10 / r + r) / 2 := by
      calc nseq a (p + 1) = nstep (a * 10 ^ 10) (nseq a p) := rfl
      _ = nstep (a * 10 ^ 10) r := by rw [hp]
      _ = (a * 10 ^ 10 / r + r) / 2 := rfl
    rcases hat with hq | hq
    · have hq' : nseq a (p + 1) = r := by rw [e]; exact hq
      rw [hp, hq', if_neg (by omega : ¬ (r : Int) < (r : Int))]
    · have hq' : nseq a (p + 1) = r + 1 := by rw [e]; exact hq
      rw [hp, hq', if_pos (by omega : (r : Int) < (((r + 1 : Nat)) : Int))]
  · have hat := newton_at_succ (N := a * 10 ^ 10) hr1 hr2 hrpos
    have e : nseq a (p + 1) = r := by
      calc nseq a (p + 1) = nstep (a * 10 ^ 10) (nseq a p) := rfl
      _ = nstep (a * 10 ^ 10) (r + 1) := by rw [hp]
      _ = (a * 10 ^ 10 / (r + 1) + (r + 1)) / 2 := rfl
      _ = r := hat
    rw [hp, e, if_neg (by omega : ¬ (((r + 1 : Nat)) : Int) < (r : Int))]

-- The fixed routine: the PR 4486 choice, minimum of the last two iterates.
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt := by
  exact ⟨fun y z => if y < z then y else z, fun x => rfl⟩

-- On a positive decimal, `sqrt` returns the cast floor root.
theorem sqrt_pos_eq {a r : Nat} (hamax : a ≤ 2 ^ 167 - 1) (ha : 1 ≤ a)
    (hr1 : r * r ≤ a * 10 ^ 10) (hr2 : a * 10 ^ 10 < (r + 1) * (r + 1)) :
    sqrt (a : Int) = some ((r : Nat) : Int) := by
  have hrpos : 1 ≤ r := r_pos_of_a_pos ha hr2
  have hseed : r ≤ a / 2 + 5 * 10 ^ 9 := seed_ge hr1 hr2
  have hpos : sqrt ((a : Nat) : Int)
      = (loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)).map
        (fun p => if p.1 < p.2 then p.1 else p.2) :=
    vyperSqrtWith_pos _ ha hamax
  have hloop : (loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)).map
        (fun p => if p.1 < p.2 then p.1 else p.2) = some ((r : Nat) : Int) := by
    by_cases heq0 : ((a : Int)) = (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)
    · have ha0 : a = a / 2 + 5 * 10 ^ 9 := by omega
      have hstop : loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)
          = some (((a : Int)), ((a : Int))) := by
        have hcast : (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) = ((a : Int)) := by omega
        rw [hcast]
        show loop _ (255 + 1) _ _ = _
        exact loop_stop _ _ _
      rw [hstop]
      show some (if (a : Int) < (a : Int) then (a : Int) else (a : Int))
        = some ((r : Nat) : Int)
      rw [if_neg (by omega)]
      have har : ((a : Int)) = ((r : Nat) : Int) := by
        have hcases : a = 9999999999 ∨ a = 10000000000 := by omega
        rcases hcases with hC | hC
        · have h1 : r = 9999999999 := by
            apply floor_eq hr1 hr2
            · rw [hC]; decide
            · rw [hC]; decide
          omega
        · have h1 : r = 10000000000 := by
            apply floor_eq hr1 hr2
            · rw [hC]; decide
            · rw [hC]; decide
          omega
      rw [har]
    · have hne0 : a ≠ a / 2 + 5 * 10 ^ 9 := by omega
      have hstep := loop_step (a := a) (y := a) (z := a / 2 + 5 * 10 ^ 9) 255
        (by omega : 0 < a / 2 + 5 * 10 ^ 9)
        (by omega : a / 2 + 5 * 10 ^ 9 ≠ a)
        (nseq_sum_le hamax hr1 hr2 hrpos hseed 0)
      have hZnat : (a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9)
          + (a / 2 + 5 * 10 ^ 9)) / 2 = nseq a 1 := rfl
      have hZ : (((a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9)
          + (a / 2 + 5 * 10 ^ 9)) / 2 : Nat) : Int)
          = ((nseq a 1 : Nat) : Int) := by rw [hZnat]
      have hs0nat : a / 2 + 5 * 10 ^ 9 = nseq a 0 := rfl
      have hs0 : (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)
          = ((nseq a 0 : Nat) : Int) := by rw [hs0nat]
      have hj1nat : (0 + 1 : Nat) = 1 := rfl
      have hj1 : ((nseq a (0 + 1) : Nat) : Int)
          = ((nseq a 1 : Nat) : Int) := by rw [hj1nat]
      have hfollow := loop_follow hamax hr1 hr2 hrpos hseed 255 0
      rw [hj1] at hfollow
      show (loop (a : Int) (255 + 1) (a : Int)
          (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)).map
          (fun p => if p.1 < p.2 then p.1 else p.2) = some ((r : Nat) : Int)
      rw [hstep, hs0, hZ]
      rcases hfollow with h | h
      · rw [h]
        show some (if ((r : Nat) : Int) < ((r : Nat) : Int)
          then ((r : Nat) : Int) else ((r : Nat) : Int)) = some ((r : Nat) : Int)
        rw [if_neg (by omega)]
      · rw [h]
        have hp := nseq_eventually hamax hr1 hr2 hrpos hseed _ (by omega : 167 ≤ 0 + 255)
        have hmin := min_consec (a := a) hr1 hr2 hrpos hp
        show some (if (((nseq a (0 + 255) : Nat)) : Int)
            < (((nseq a (0 + 255 + 1) : Nat)) : Int)
          then (((nseq a (0 + 255) : Nat)) : Int)
          else (((nseq a (0 + 255 + 1) : Nat)) : Int)) = some ((r : Nat) : Int)
        rw [hmin]
  rw [hpos]
  exact hloop

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hsqrt
  by_cases hxneg : x < 0
  · have hnone : sqrt x = none := req_sqrt_neg_reverts x hxneg
    rw [hnone] at hsqrt
    cases hsqrt
  · have hnonneg : 0 ≤ x := by omega
    by_cases hx0 : x = 0
    · have hr0 : r = 0 := by
        have h0 : sqrt (0 : Int) = some 0 := by
          unfold sqrt vyperSqrtWith
          rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]
        rw [hx0] at hsqrt
        rw [h0] at hsqrt
        cases hsqrt with
        | refl => rfl
      rw [hx0, hr0]
      decide
    · have hxpos : 0 < x := by omega
      obtain ⟨a, rfl⟩ : ∃ a : Nat, x = ((a : Nat) : Int) :=
        ⟨x.toNat, (Int.toNat_of_nonneg hnonneg).symm⟩
      have ha : 1 ≤ a := by omega
      have hamax : a ≤ 2 ^ 167 - 1 := by
        have h2 := hx.2
        rw [max_decimal_eq] at h2
        exact_mod_cast h2
      obtain ⟨rv, hr1, hr2⟩ := exists_sqrt (a * 10 ^ 10)
      have hrv := sqrt_pos_eq hamax ha hr1 hr2
      rw [hrv] at hsqrt
      cases hsqrt with
      | refl =>
        have hD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
        have e0 : ((rv : Nat) : Int) * ((rv : Nat) : Int)
            = ((rv * rv : Nat) : Int) := by rw [← Int.natCast_mul]
        have eA : ((a : Nat) : Int) * DIVISOR = ((a * 10 ^ 10 : Nat) : Int) := by
          rw [hD, ← Int.natCast_mul]
        rw [e0, eA]
        exact_mod_cast hr1

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hsqrt
  by_cases hxneg : x < 0
  · have hnone : sqrt x = none := req_sqrt_neg_reverts x hxneg
    rw [hnone] at hsqrt
    cases hsqrt
  · have hnonneg : 0 ≤ x := by omega
    by_cases hx0 : x = 0
    · have hr0 : r = 0 := by
        have h0 : sqrt (0 : Int) = some 0 := by
          unfold sqrt vyperSqrtWith
          rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]
        rw [hx0] at hsqrt
        rw [h0] at hsqrt
        cases hsqrt with
        | refl => rfl
      rw [hx0, hr0]
      decide
    · have hxpos : 0 < x := by omega
      obtain ⟨a, rfl⟩ : ∃ a : Nat, x = ((a : Nat) : Int) :=
        ⟨x.toNat, (Int.toNat_of_nonneg hnonneg).symm⟩
      have ha : 1 ≤ a := by omega
      have hamax : a ≤ 2 ^ 167 - 1 := by
        have h2 := hx.2
        rw [max_decimal_eq] at h2
        exact_mod_cast h2
      obtain ⟨rv, hr1, hr2⟩ := exists_sqrt (a * 10 ^ 10)
      have hrv := sqrt_pos_eq hamax ha hr1 hr2
      rw [hrv] at hsqrt
      cases hsqrt with
      | refl =>
        have hD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
        have e1 : ((rv : Nat) : Int) + 1 = ((rv + 1 : Nat) : Int) := by
          rw [Int.natCast_add, Int.natCast_one]
        have e2 : (((rv : Nat) : Int) + 1) * (((rv : Nat) : Int) + 1)
            = (((rv + 1) * (rv + 1) : Nat) : Int) := by
          rw [e1, ← Int.natCast_mul]
        have eA : ((a : Nat) : Int) * DIVISOR = ((a * 10 ^ 10 : Nat) : Int) := by
          rw [hD, ← Int.natCast_mul]
        rw [eA, e2]
        exact_mod_cast hr2

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hnonneg
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : sqrt (0 : Int) = some 0 := by
      unfold sqrt vyperSqrtWith
      rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]
    rw [h0]
    decide
  · have hxpos : 0 < x := by omega
    obtain ⟨a, rfl⟩ : ∃ a : Nat, x = ((a : Nat) : Int) :=
      ⟨x.toNat, (Int.toNat_of_nonneg hnonneg).symm⟩
    have ha : 1 ≤ a := by omega
    have hamax : a ≤ 2 ^ 167 - 1 := by
      have h2 := hx.2
      rw [max_decimal_eq] at h2
      exact_mod_cast h2
    obtain ⟨rv, hr1, hr2⟩ := exists_sqrt (a * 10 ^ 10)
    have hrv := sqrt_pos_eq hamax ha hr1 hr2
    simp [hrv]

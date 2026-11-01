import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin

namespace VyperSqrt

open ProofForgeFin.Sqrt (newton sqrt_le_sqrt le_sqrt_of_mul_self_le sqrt_lt_of_lt_mul_self
  sqrt_eq_of_bounds newton_sub_sqrt_le_half sqrt_le_newton newton_lt_self
  eq_sqrt_of_newton_eq_self newton_le_sqrt_add_one newton_of_mem min_newton_eq_sqrt
  sqrt_lt_two_pow)
open ProofForgeFin (div_anti_right div_mono_left div_div)

/-- The fixed routine: the deployed loop followed by the smaller of the last two iterates
(PR 4486: `if y < z: z = y`). -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-- Scale: raw input `a` stands for `a / 10^10`; the integer under the root is `a * 10^10`. -/
def Aval (a : Nat) : Nat := a * 10 ^ 10

/-- The seed `x / 2.0 + 0.5` on raw values: `a / 2 + 5 * 10^9`. -/
def seedN (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- Ghost Newton sequence: `t 0 = seed`, `t (i+1) = newton A (t i)`. -/
def gseq (a : Nat) : Nat → Nat
  | 0 => seedN a
  | n + 1 => newton (Aval a) (gseq a n)

/-- Natural-number mirror of `loop`: no failure, values are `Nat`s. -/
def mloop (A : Nat) (n y z : Nat) : Nat × Nat :=
  match n with
  | 0 => (y, z)
  | n + 1 => if z = y then (y, z) else mloop A n z (newton A z)

/-- The seed square strictly exceeds the scaled input: the root is below the seed. -/
theorem sq_seed : ∀ a : Nat, Aval a < (seedN a + 1) * (seedN a + 1) := by
  intro a
  have hQM : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hM : a % 2 < 2 := Nat.mod_lt a (by decide)
  have eA : Aval a = 2 * (a / 2) * 10 ^ 10 + (a % 2) * 10 ^ 10 := by
    unfold Aval
    have eA' : a * 10 ^ 10 = (2 * (a / 2) + a % 2) * 10 ^ 10 := by rw [hQM]
    rw [eA', Nat.add_mul]
  have h5 : (5 : Nat) * 10 ^ 9 = 5000000000 := by decide
  have eS : seedN a + 1 = (a / 2) + 5000000001 := by
    unfold seedN; rw [h5]
  have key : ∀ q μ : Int, 0 ≤ μ → μ ≤ 1 →
      2 * q * 10000000000 + μ * 10000000000
        < (q + 5000000001) * (q + 5000000001) := by
    intro q μ h0 h1
    have e1 : (q + 5000000001) * (q + 5000000001)
        = q * q + 2 * 5000000001 * q + 5000000001 * 5000000001 := by grind
    have e2 : (q - 4999999999) * (q - 4999999999)
        = q * q - 2 * 4999999999 * q + 4999999999 * 4999999999 := by grind
    have hsq : 0 ≤ (q - 4999999999) * (q - 4999999999) := by
      by_cases h : q < 4999999999
      · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact Int.mul_nonneg (by omega) (by omega)
    rw [e1]; rw [e2] at hsq; omega
  rw [eA, eS]
  have hM1 : a % 2 ≤ 1 := Nat.le_of_lt_succ hM
  have h0 : (0 : Int) ≤ ((a % 2 : Nat) : Int) := by omega
  have h1 : ((a % 2 : Nat) : Int) ≤ 1 := by omega
  have hK := key ((a / 2 : Nat) : Int) ((a % 2 : Nat) : Int) h0 h1
  have hde : (((a / 2 : Nat) : Int) + 5000000001) * (((a / 2 : Nat) : Int) + 5000000001)
      = ((a / 2 + 5000000001 : Nat) : Int) * ((a / 2 + 5000000001 : Nat) : Int) := by
    rw [Int.natCast_add]; rfl
  have hK' : ((2 * (a / 2) * 10 ^ 10 + (a % 2) * 10 ^ 10 : Nat) : Int)
      < ((((a / 2) + 5000000001) * ((a / 2) + 5000000001) : Nat) : Int) := by
    omega
  exact Int.ofNat_lt.mp hK'

/-- The seed is at least the root. -/
theorem seed_ge : ∀ a : Nat, 0 < a → Nat.sqrt (Aval a) ≤ seedN a := by
  intro a ha
  have h := sq_seed a
  have hlt : Nat.sqrt (Aval a) < seedN a + 1 := sqrt_lt_of_lt_mul_self h
  omega

/-- The scaled input is positive. -/
theorem Aval_pos : ∀ a : Nat, 0 < a → 0 < Aval a := by
  intro a ha; unfold Aval; omega

/-- The root of a positive scaled input is at least `10^5`. -/
theorem s_ge100k : ∀ a : Nat, 0 < a → 100000 ≤ Nat.sqrt (Aval a) := by
  intro a ha
  have hA : (100000 : Nat) * 100000 ≤ Aval a := by
    unfold Aval
    have h1 : (1 : Nat) * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha
    have h2 : (100000 : Nat) * 100000 = 10 ^ 10 := by decide
    omega
  exact le_sqrt_of_mul_self_le hA

/-- Every ghost iterate is positive and at least the root. -/
theorem gseq_bounds : ∀ (a n : Nat), 0 < a →
    0 < gseq a n ∧ Nat.sqrt (Aval a) ≤ gseq a n := by
  intro a n ha; induction n with
  | zero =>
    refine ⟨?_, seed_ge a ha⟩
    unfold gseq seedN; omega
  | succ n ih =>
    obtain ⟨hpos, hle⟩ := ih
    have hnew := sqrt_le_newton (a := Aval a) (x := gseq a n) hpos
    have h1 : 1 ≤ Nat.sqrt (Aval a) := by
      have := s_ge100k a ha; omega
    have hpos' : 0 < newton (Aval a) (gseq a n) := by omega
    show 0 < newton (Aval a) (gseq a n) ∧ _
    exact ⟨hpos', hnew⟩

/-- Every ghost iterate is at most one past the seed. -/
theorem gseq_upper : ∀ (a n : Nat), 0 < a → gseq a n ≤ seedN a + 1 := by
  intro a n ha; induction n with
  | zero => exact Nat.le_succ _
  | succ n ih =>
    have ⟨hpos, hle⟩ := gseq_bounds a n ha
    have e : gseq a (n + 1) = newton (Aval a) (gseq a n) := rfl
    rw [e]
    rcases Nat.lt_or_ge (Nat.sqrt (Aval a)) (gseq a n) with h | h
    · exact Nat.le_trans (Nat.le_of_lt (newton_lt_self (a := Aval a) h)) ih
    · have hxs : gseq a n = Nat.sqrt (Aval a) := Nat.le_antisymm h hle
      have h1 : newton (Aval a) (gseq a n) ≤ Nat.sqrt (Aval a) + 1 := by
        apply newton_le_sqrt_add_one hpos hle
        rw [hxs, Nat.sub_self]; exact Nat.zero_le _
      exact Nat.le_trans h1 (Nat.add_le_add_right (seed_ge a ha) _)

/-- The root is below `2^101`: the scaled input is below `2^202`. -/
theorem s_lt_pow : ∀ a : Nat, 0 < a → a ≤ 2 ^ 167 - 1 →
    Nat.sqrt (Aval a) < 2 ^ 101 := by
  intro a ha hle
  apply sqrt_lt_two_pow (k := 101)
  have h10 : (10 : Nat) ^ 10 ≤ 2 ^ 34 := by decide
  have e1 : Aval a ≤ (2 ^ 167 - 1) * 10 ^ 10 := Nat.mul_le_mul_right _ hle
  have e2 : (2 ^ 167 - 1) * 10 ^ 10 ≤ (2 ^ 167 - 1) * 2 ^ 34 :=
    Nat.mul_le_mul_left _ h10
  have h2 : ((2 ^ 167 - 1) + 1) * 2 ^ 34 = (2 ^ 167 - 1) * 2 ^ 34 + 2 ^ 34 :=
    Nat.add_mul _ _ _
  have hsub : (2 ^ 167 - 1) + 1 = 2 ^ 167 :=
    Nat.sub_add_cancel (by decide : (1 : Nat) ≤ 2 ^ 167)
  have e3' : (2 ^ 167 - 1) * 2 ^ 34 + 2 ^ 34 = 2 ^ 167 * 2 ^ 34 := by
    rw [← h2, hsub]
  have h34 : 0 < (2 : Nat) ^ 34 := by decide
  have e3 : (2 ^ 167 - 1) * 2 ^ 34 < 2 ^ 167 * 2 ^ 34 := by
    rw [← e3']; exact Nat.lt_add_of_pos_right h34
  have e4 : (2 : Nat) ^ 167 * 2 ^ 34 = 2 ^ 201 := by decide
  have e5 : (2 : Nat) ^ 201 < 2 ^ 202 := by decide
  have hfin : (2 : Nat) ^ (2 * 101) = 2 ^ 202 := by decide
  have e6 : (2 : Nat) ^ 167 * 2 ^ 34 < 2 ^ 202 := by
    rw [e4]; exact e5
  rw [hfin]
  exact Nat.lt_of_le_of_lt (Nat.le_trans e1 e2) (Nat.lt_trans e3 e6)

/-- The Newton quotient stays near the root. -/
theorem quot_le : ∀ (a i : Nat), 0 < a → a ≤ 2 ^ 167 - 1 →
    Aval a / gseq a i ≤ Nat.sqrt (Aval a) + 2 := by
  intro a i ha hle
  have ⟨hpos, hle2⟩ := gseq_bounds a i ha
  have hspos : 0 < Nat.sqrt (Aval a) := by
    have := s_ge100k a ha; omega
  have hup := Nat.lt_succ_sqrt (Aval a)
  simp only [Nat.succ_eq_add_one] at hup
  have hexp : (Nat.sqrt (Aval a) + 1) * (Nat.sqrt (Aval a) + 1)
      = Nat.sqrt (Aval a) * Nat.sqrt (Aval a)
        + (Nat.sqrt (Aval a) + Nat.sqrt (Aval a)) + 1 := by grind
  have h2 : Aval a
      ≤ Nat.sqrt (Aval a) * Nat.sqrt (Aval a)
        + (Nat.sqrt (Aval a) + Nat.sqrt (Aval a)) := by omega
  have h1 : Aval a / gseq a i ≤ Aval a / Nat.sqrt (Aval a) :=
    div_anti_right _ hspos hle2
  have hmul : Nat.sqrt (Aval a) * (Nat.sqrt (Aval a) + 2)
      = Nat.sqrt (Aval a) * Nat.sqrt (Aval a)
        + (Nat.sqrt (Aval a) + Nat.sqrt (Aval a)) := by grind
  rw [← hmul] at h2
  have h3 : Aval a / Nat.sqrt (Aval a) ≤ Nat.sqrt (Aval a) + 2 := by
    have h3' : Aval a / Nat.sqrt (Aval a)
        ≤ (Nat.sqrt (Aval a) * (Nat.sqrt (Aval a) + 2)) / Nat.sqrt (Aval a) :=
      Nat.div_le_div_right h2
    have h4 : Nat.sqrt (Aval a) * (Nat.sqrt (Aval a) + 2) / Nat.sqrt (Aval a)
        = Nat.sqrt (Aval a) + 2 := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_cancel _ hspos
    rw [h4] at h3'; exact h3'
  exact Nat.le_trans h1 h3

/-- Every Newton step stays in decimal range. -/
theorem range_ok : ∀ (a i : Nat), 0 < a → a ≤ 2 ^ 167 - 1 →
    Aval a / gseq a i + gseq a i ≤ 2 ^ 167 - 1 := by
  intro a i ha hle
  have hq := quot_le a i ha hle
  have hup := gseq_upper a i ha
  have hs := s_lt_pow a ha hle
  have h1 : Aval a / gseq a i + gseq a i
      ≤ (Nat.sqrt (Aval a) + 2) + (seedN a + 1) := Nat.add_le_add hq hup
  have hseed : seedN a ≤ (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 := by
    unfold seedN
    exact Nat.add_le_add_right (Nat.div_le_div_right hle) _
  have hhalf : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
  have hseed2 : seedN a ≤ (2 ^ 166 - 1) + 5 * 10 ^ 9 := by
    rw [← hhalf]; exact hseed
  have key : 2 ^ 101 + 2 + ((2 ^ 166 - 1) + 5 * 10 ^ 9 + 1) ≤ 2 ^ 167 - 1 := by
    decide
  have h2 : (Nat.sqrt (Aval a) + 2) + (seedN a + 1)
      ≤ (2 ^ 101 + 2) + ((2 ^ 166 - 1) + 5 * 10 ^ 9 + 1) := by
    have g1 : Nat.sqrt (Aval a) + 2 ≤ 2 ^ 101 + 2 :=
      Nat.add_le_add_right (Nat.le_of_lt hs) _
    have g2 : seedN a + 1 ≤ ((2 ^ 166 - 1) + 5 * 10 ^ 9) + 1 :=
      Nat.add_le_add_right hseed2 _
    exact Nat.add_le_add g1 g2
  exact Nat.le_trans h1 (Nat.le_trans h2 key)

/-- Halving bound with an explicit closed form. -/
theorem err_bound : ∀ (a k : Nat), 0 < a → a ≤ 2 ^ 167 - 1 →
    gseq a k - Nat.sqrt (Aval a)
      ≤ (gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ k + 2 := by
  intro a k ha hle; induction k with
  | zero =>
    rw [Nat.pow_zero, Nat.div_one]; exact Nat.le_add_right _ _
  | succ k ih =>
    have ⟨hpos, hle2⟩ := gseq_bounds a k ha
    have hstep : gseq a (k + 1) - Nat.sqrt (Aval a)
        ≤ (gseq a k - Nat.sqrt (Aval a)) / 2 + 1 := by
      have h := newton_sub_sqrt_le_half (a := Aval a) (x := gseq a k) hpos hle2
      show newton (Aval a) (gseq a k) - _ ≤ _
      exact h
    have key : (gseq a k - Nat.sqrt (Aval a)) / 2 + 1
        ≤ ((gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ k + 2) / 2 + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right ih) _
    have hdd : ((gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ k) / 2
        = (gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ (k + 1) := by
      rw [div_div, Nat.pow_succ]
    have hfin : ((gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ k + 2) / 2 + 1
        = (gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ (k + 1) + 2 := by
      revert hdd
      generalize (gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ k = U
      generalize (gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ (k + 1) = U'
      intro hdd
      omega
    rw [← hfin]
    exact Nat.le_trans hstep key

/-- After 254 steps the error is at most 2. -/
theorem err254 : ∀ a : Nat, 0 < a → a ≤ 2 ^ 167 - 1 →
    gseq a 254 - Nat.sqrt (Aval a) ≤ 2 := by
  intro a ha hle
  have h := err_bound a 254 ha hle
  have hE : gseq a 0 - Nat.sqrt (Aval a) ≤ (2 ^ 166 - 1) + 5 * 10 ^ 9 := by
    have h1 : gseq a 0 - Nat.sqrt (Aval a) ≤ gseq a 0 := Nat.sub_le _ _
    have h2 : gseq a 0 ≤ (2 ^ 166 - 1) + 5 * 10 ^ 9 := by
      have ha2 : a / 2 ≤ 2 ^ 166 - 1 := by
        have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hle
        have h2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
        rw [h2] at h1; exact h1
      show seedN a ≤ _
      unfold seedN
      exact Nat.add_le_add_right ha2 _
    exact Nat.le_trans h1 h2
  have h0 : (gseq a 0 - Nat.sqrt (Aval a)) / 2 ^ 254 = 0 := by
    apply Nat.div_eq_of_lt
    have key : (2 ^ 166 - 1) + 5 * 10 ^ 9 < 2 ^ 254 := by decide
    omega
  rw [h0] at h
  omega

/-- Step 255 lands within one of the root. -/
theorem close255 : ∀ a : Nat, 0 < a → a ≤ 2 ^ 167 - 1 →
    gseq a 255 ≤ Nat.sqrt (Aval a) + 1 := by
  intro a ha hle
  have ⟨hpos254, hle254⟩ := gseq_bounds a 254 ha
  have he := err254 a ha hle
  have hs2 : 2 ≤ Nat.sqrt (Aval a) := by
    have := s_ge100k a ha; omega
  have hsq : (gseq a 254 - Nat.sqrt (Aval a)) * (gseq a 254 - Nat.sqrt (Aval a))
      ≤ 2 * Nat.sqrt (Aval a) := by
    have h1 : (gseq a 254 - Nat.sqrt (Aval a)) * (gseq a 254 - Nat.sqrt (Aval a))
        ≤ 2 * 2 := Nat.mul_le_mul he he
    omega
  have hle255 : newton (Aval a) (gseq a 254) ≤ Nat.sqrt (Aval a) + 1 :=
    newton_le_sqrt_add_one hpos254 hle254 hsq
  have e255 : gseq a 255 = newton (Aval a) (gseq a 254) := rfl
  rw [e255]; exact hle255

/-- The Nat mirror follows the ghost sequence. -/
theorem mloop_pair : ∀ (a i n : Nat), ∃ k, k ≤ n
    ∧ (i + k = i + n ∨ gseq a (i + k + 1) = gseq a (i + k))
    ∧ mloop (Aval a) n (gseq a i) (gseq a (i + 1))
      = (gseq a (i + k), gseq a (i + k + 1)) := by
  intro a i n; induction n generalizing i with
  | zero => exact ⟨0, Nat.le_refl _, Or.inl rfl, rfl⟩
  | succ n ih =>
    have e : mloop (Aval a) (n + 1) (gseq a i) (gseq a (i + 1))
        = (if gseq a (i + 1) = gseq a i then (gseq a i, gseq a (i + 1))
          else mloop (Aval a) n (gseq a (i + 1))
            (newton (Aval a) (gseq a (i + 1)))) := rfl
    by_cases h : gseq a (i + 1) = gseq a i
    · refine ⟨0, Nat.zero_le _, Or.inr h, ?_⟩
      rw [e, if_pos h]
      rfl
    · obtain ⟨k', hk', hdisj, heq⟩ := ih (i + 1)
      refine ⟨k' + 1, Nat.succ_le_succ hk', ?_, ?_⟩
      · have e1 : i + (k' + 1) = (i + 1) + k' := by omega
        have e2 : i + (k' + 1) + 1 = ((i + 1) + k') + 1 := by omega
        rcases hdisj with hfin | hfix
        · left; omega
        · right; rw [e2, e1]; exact hfix
      · have e1 : i + (k' + 1) = (i + 1) + k' := by omega
        have e2 : i + (k' + 1) + 1 = ((i + 1) + k') + 1 := by omega
        have e3 : newton (Aval a) (gseq a (i + 1)) = gseq a ((i + 1) + 1) := rfl
        rw [e, if_neg h, e3, e2, e1]
        exact heq

/-- The deployed loop follows the ghost sequence. -/
theorem loop_ghost : ∀ (a n i : Nat), 0 < a → a ≤ 2 ^ 167 - 1 → i + n ≤ 256 →
    ∃ k, k ≤ n ∧ (i + k = i + n ∨ gseq a (i + k + 1) = gseq a (i + k))
      ∧ loop (a : Int) n ((gseq a i : Nat) : Int) ((gseq a (i + 1) : Nat) : Int)
        = some (((gseq a (i + k) : Nat) : Int), (((gseq a (i + k + 1) : Nat)) : Int)) := by
  intro a n i ha hle hin; induction n generalizing i with
  | zero =>
    refine ⟨0, Nat.le_refl _, Or.inl rfl, rfl⟩
  | succ n ih =>
    by_cases h : ((gseq a (i + 1) : Nat) : Int) = ((gseq a i : Nat) : Int)
    · have hNat : gseq a (i + 1) = gseq a i := Int.ofNat.inj h
      have hstop := loop_stop (a : Int) n ((gseq a i : Nat) : Int)
      refine ⟨0, Nat.zero_le _, Or.inr ?_, ?_⟩
      · exact hNat
      · rw [hNat]; exact hstop
    · have hne : gseq a (i + 1) ≠ gseq a i := fun e => h (by rw [e])
      have hpos : 0 < gseq a (i + 1) := (gseq_bounds a (i + 1) ha).1
      have hrange := range_ok a (i + 1) ha hle
      have hstep := loop_step (a := a) (y := gseq a i) (z := gseq a (i + 1))
        (n := n) hpos hne hrange
      obtain ⟨k', hk', hdisj, heq⟩ := ih (i + 1) (by omega)
      refine ⟨k' + 1, Nat.succ_le_succ hk', ?_, ?_⟩
      · have e1 : i + (k' + 1) = (i + 1) + k' := by omega
        have e2 : i + (k' + 1) + 1 = ((i + 1) + k') + 1 := by omega
        rcases hdisj with hfin | hfix
        · left; omega
        · right; rw [e2, e1]; exact hfix
      · have hAval : Aval a = a * 10 ^ 10 := rfl
        have hz' : ((((a * 10 ^ 10 / gseq a (i + 1) + gseq a (i + 1)) / 2 : Nat)) : Int)
            = ((gseq a ((i + 1) + 1) : Nat) : Int) := by
          have hnat : (a * 10 ^ 10 / gseq a (i + 1) + gseq a (i + 1)) / 2
              = gseq a ((i + 1) + 1) := by
            have e : gseq a ((i + 1) + 1)
                = (gseq a (i + 1) + Aval a / gseq a (i + 1)) / 2 := rfl
            rw [e, hAval, Nat.add_comm (a * 10 ^ 10 / gseq a (i + 1)) (gseq a (i + 1))]
          exact congrArg (fun n : Nat => ((n : Nat) : Int)) hnat
        have e1 : i + (k' + 1) = (i + 1) + k' := by omega
        have e2 : i + (k' + 1) + 1 = ((i + 1) + k') + 1 := by omega
        rw [hstep, hz', e2, e1]; exact heq

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith (fun y z => if y < z then y else z) x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

/-- Steps 255 and 256 bracket the root. -/
theorem min255 : ∀ a : Nat, 0 < a → a ≤ 2 ^ 167 - 1 →
    Nat.min (gseq a 255) (gseq a (255 + 1)) = Nat.sqrt (Aval a) := by
  intro a ha hle
  have hb := gseq_bounds a 255 ha
  have h255 := close255 a ha hle
  have hm := min_newton_eq_sqrt hb.1 hb.2 h255
  have e : newton (Aval a) (gseq a 255) = gseq a (255 + 1) := rfl
  rw [e] at hm
  exact hm

/-- The routine returns the integer square root on positive inputs. -/
theorem sqrt_val : ∀ a : Nat, 0 < a → a ≤ 2 ^ 167 - 1 →
    vyperSqrtWith (fun y z => if y < z then y else z) (a : Int)
      = some ((Nat.sqrt (Aval a) : Int)) := by
  intro a ha hle
  have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha hle
  rw [hpos]
  have es : ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) = ((gseq a 0 : Nat) : Int) := rfl
  rw [es]
  by_cases hseed : ((gseq a 0 : Nat) : Int) = (a : Int)
  · have hNat : gseq a 0 = a := Int.ofNat.inj hseed
    have hsa : a / 2 + 5000000000 = a := hNat
    have hcase : a = 10000000000 ∨ a = 10000000000 - 1 := by
      have hqm := Nat.div_add_mod a 2
      have hm := Nat.mod_lt a (show 0 < 2 by decide)
      have hm01 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases hm01 with hm0 | hm0
      · left; omega
      · right; omega
    have hloop0 : loop (a : Int) 256 (a : Int) (a : Int)
        = some ((a : Int), (a : Int)) := by
      have e : (256 : Nat) = 255 + 1 := rfl
      rw [e]
      exact loop_stop _ _ _
    have hs_eq : Nat.sqrt (Aval a) = a := by
      rcases hcase with rfl | rfl
      · have hA : Aval 10000000000 = 10000000000 * 10000000000 := rfl
        rw [hA]
        exact sqrt_eq_of_bounds (by decide) (by decide)
      · have hA : Aval (10000000000 - 1) = (10000000000 - 1) * 10000000000 := rfl
        rw [hA]
        exact sqrt_eq_of_bounds (by decide) (by decide)
    rw [hNat, hloop0]
    show some (if (a : Int) < (a : Int) then (a : Int) else (a : Int))
      = some ((Nat.sqrt (Aval a) : Int))
    rw [if_neg (by omega : ¬ (a : Int) < (a : Int)), hs_eq]
  · have hne : gseq a 0 ≠ a := fun e => hseed (by rw [e])
    have hpos0 : 0 < gseq a 0 := (gseq_bounds a 0 ha).1
    have hrange0 := range_ok a 0 ha hle
    have hstep := loop_step (a := a) (y := a) (z := gseq a 0) (n := 255)
      hpos0 hne hrange0
    have hAval : Aval a = a * 10 ^ 10 := rfl
    have hz' : ((((a * 10 ^ 10 / gseq a 0 + gseq a 0) / 2 : Nat)) : Int)
        = ((gseq a (0 + 1) : Nat) : Int) := by
      have hnat : (a * 10 ^ 10 / gseq a 0 + gseq a 0) / 2
          = gseq a (0 + 1) := by
        have e : gseq a (0 + 1)
            = (gseq a 0 + Aval a / gseq a 0) / 2 := rfl
        rw [e, hAval, Nat.add_comm (a * 10 ^ 10 / gseq a 0) (gseq a 0)]
      exact congrArg (fun n : Nat => ((n : Nat) : Int)) hnat
    obtain ⟨k, hk255, hdisj, heq⟩ := loop_ghost a 255 0 ha hle (by omega)
    have e0 : (0 : Nat) + k = k := Nat.zero_add k
    rw [e0] at heq hdisj
    have hfuel : (256 : Nat) = 255 + 1 := rfl
    rw [hfuel, hstep, hz', heq]
    have hmin : (if ((gseq a k : Nat) : Int) < ((gseq a (k + 1) : Nat) : Int)
          then ((gseq a k : Nat) : Int) else ((gseq a (k + 1) : Nat) : Int))
        = ((Nat.min (gseq a k) (gseq a (k + 1)) : Nat) : Int) := by
      by_cases hlt : ((gseq a k : Nat) : Int) < ((gseq a (k + 1) : Nat) : Int)
      · rw [if_pos hlt]
        have hle' : gseq a k ≤ gseq a (k + 1) :=
          Int.ofNat_le.mp (Int.le_of_lt hlt)
        have hmin' : Nat.min (gseq a k) (gseq a (k + 1)) = gseq a k :=
          Nat.min_eq_left hle'
        rw [hmin']
      · rw [if_neg hlt]
        have hle' : gseq a (k + 1) ≤ gseq a k := by
          have hle'' : ((gseq a (k + 1) : Nat) : Int) ≤ ((gseq a k : Nat) : Int) := by
            omega
          exact Int.ofNat_le.mp hle''
        have hmin' : Nat.min (gseq a k) (gseq a (k + 1)) = gseq a (k + 1) :=
          Nat.min_eq_right hle'
        rw [hmin']
    have hminval : Nat.min (gseq a k) (gseq a (k + 1)) = Nat.sqrt (Aval a) := by
      rcases hdisj with hfin | hfix
      · have hk255' : k = 255 := by omega
        rw [hk255']
        exact min255 a ha hle
      · have hnew : newton (Aval a) (gseq a k) = gseq a k := by
          have e : gseq a (k + 1) = newton (Aval a) (gseq a k) := rfl
          exact e.symm.trans hfix
        have hposk := (gseq_bounds a k ha).1
        have hs_eq : gseq a k = Nat.sqrt (Aval a) :=
          eq_sqrt_of_newton_eq_self hposk hnew
        have hmin0 : Nat.min (gseq a k) (gseq a (k + 1)) = gseq a k := by
          rw [hfix]
          exact Nat.min_eq_left (Nat.le_refl _)
        rw [hmin0]; exact hs_eq
    show some (if ((gseq a k : Nat) : Int) < ((gseq a (k + 1) : Nat) : Int)
        then ((gseq a k : Nat) : Int) else ((gseq a (k + 1) : Nat) : Int))
      = some ((Nat.sqrt (Aval a) : Int))
    rw [hmin, hminval]

/-- The routine returns zero on zero. -/
theorem sqrt0 : sqrt (0 : Int) = some 0 := by
  show vyperSqrtWith (fun y z => if y < z then y else z) 0 = some 0
  unfold vyperSqrtWith
  rw [if_neg (by omega : ¬ (0 : Int) < 0), if_pos rfl]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hdec hsome
  obtain ⟨hlo, hhi⟩ := hdec
  by_cases hx0 : x = 0
  · subst hx0
    have hr : r = 0 := Option.some_inj.mp (hsome.symm.trans sqrt0)
    subst hr
    omega
  · by_cases hxneg : x < 0
    · rw [req_sqrt_neg_reverts x hxneg] at hsome
      cases hsome
    · have hxpos : 0 < x := by omega
      have hx0' : 0 ≤ x := by omega
      obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
        ⟨x.toNat, (Int.toNat_of_nonneg hx0').symm⟩
      have ha : 0 < a := by
        have hpos' : (0 : Int) < ((a : Nat) : Int) := hxpos
        exact_mod_cast hpos'
      have hle : a ≤ 2 ^ 167 - 1 := by
        have h2 : ((a : Nat) : Int) ≤ MAX_DECIMAL := hhi
        rw [max_decimal_eq] at h2
        exact Int.ofNat_le.mp h2
      have hval := sqrt_val a ha hle
      have hsome2 : vyperSqrtWith (fun y z => if y < z then y else z) (a : Int)
          = some r := hsome
      rw [hval] at hsome2
      have hr : r = ((Nat.sqrt (Aval a) : Int)) := Option.some_inj.mp hsome2.symm
      rw [hr, divisor_eq]
      exact_mod_cast Nat.sqrt_le (Aval a)

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hdec hsome
  obtain ⟨hlo, hhi⟩ := hdec
  by_cases hx0 : x = 0
  · subst hx0
    have hr : r = 0 := Option.some_inj.mp (hsome.symm.trans sqrt0)
    subst hr
    show (0 : Int) * DIVISOR < (0 + 1) * (0 + 1)
    omega
  · by_cases hxneg : x < 0
    · rw [req_sqrt_neg_reverts x hxneg] at hsome
      cases hsome
    · have hxpos : 0 < x := by omega
      have hx0' : 0 ≤ x := by omega
      obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
        ⟨x.toNat, (Int.toNat_of_nonneg hx0').symm⟩
      have ha : 0 < a := by
        have hpos' : (0 : Int) < ((a : Nat) : Int) := hxpos
        exact_mod_cast hpos'
      have hle : a ≤ 2 ^ 167 - 1 := by
        have h2 : ((a : Nat) : Int) ≤ MAX_DECIMAL := hhi
        rw [max_decimal_eq] at h2
        exact Int.ofNat_le.mp h2
      have hval := sqrt_val a ha hle
      have hsome2 : vyperSqrtWith (fun y z => if y < z then y else z) (a : Int)
          = some r := hsome
      rw [hval] at hsome2
      have hr : r = ((Nat.sqrt (Aval a) : Int)) := Option.some_inj.mp hsome2.symm
      have hlt := Nat.lt_succ_sqrt (Aval a)
      simp only [Nat.succ_eq_add_one] at hlt
      rw [hr, divisor_eq]
      exact_mod_cast hlt

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hdec hx0
  obtain ⟨hlo, hhi⟩ := hdec
  by_cases hx00 : x = 0
  · subst hx00
    rw [sqrt0]
    rfl
  · have hxpos : 0 < x := by omega
    obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
      ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
    have ha : 0 < a := by
      have hx00' : ((a : Nat) : Int) ≠ 0 := hx00
      have hane : a ≠ 0 := fun e => hx00' (by rw [e]; simp)
      exact Nat.pos_of_ne_zero hane
    have hle : a ≤ 2 ^ 167 - 1 := by
      have h2 : ((a : Nat) : Int) ≤ MAX_DECIMAL := hhi
      rw [max_decimal_eq] at h2
      exact Int.ofNat_le.mp h2
    have hval := sqrt_val a ha hle
    have e : sqrt (a : Int)
        = vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) := rfl
    rw [e, hval]
    rfl

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨_, fun _ => rfl⟩

end VyperSqrt

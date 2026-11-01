import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
import ProofForgeFin.Rounding
/-!
Port of the code the Vyper compiler v0.4.0 (commit
e9db8d9f7486ea38f5b86531629019ad28f514e) inlines for the builtin
`sqrt(d: decimal) -> decimal`, with the fix of pull request 4486
(released in v0.4.1): after the loop, `if y < z: z = y`, i.e. the
result is the smaller of the last two iterates (the root rounded
down, never up).
-/
namespace VyperSqrt

open ProofForgeFin.Sqrt

/-- The fixed routine: the deployed loop followed by the minimum of the
last two iterates. -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-- Newton iteration on naturals for `N = a * 10^10`, from the seed. -/
def iter (a : Nat) : Nat → Nat
  | 0 => a / 2 + 5 * 10 ^ 9
  | n + 1 => newton (a * 10 ^ 10) (iter a n)

/-- The seed inequality: `(seed + 1)^2 > a * 10^10`. -/
theorem seed_ge_sqrt_aux (a : Nat) :
    a * 10 ^ 10 < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) := by
  have h5 : (5 : Nat) * 10 ^ 9 = 5000000000 := by decide
  have h10 : (10 ^ 10 : Nat) = 10000000000 := by decide
  have h51 : (5000000001 : Nat) = 5 * 10 ^ 9 + 1 := by decide
  have ha : a ≤ 2 * (a / 2) + 1 := by
    have h1 := Nat.div_add_mod a 2
    have h2 := Nat.mod_lt a (show 0 < 2 by decide)
    omega
  have e1 : a * 10 ^ 10 ≤ (2 * (a / 2) + 1) * 10 ^ 10 := Nat.mul_le_mul_right _ ha
  have gA : ∀ q d : Nat, (2 * q + 1) * (2 * (q + d)) < (2 * q + d + 1) * (2 * q + d + 1) := by
    intro q d; grind
  have gB : ∀ e : Nat, (2 * (5000000000 + e) + 1) * 10000000000
      < (5000000000 + e + 5000000001) * (5000000000 + e + 5000000001) := by
    intro e; grind
  rcases Nat.le_total (a / 2) 5000000000 with hle | hle
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have e2 : (10 ^ 10 : Nat) = 2 * ((a / 2) + d) := by
      rw [h10, ← hd]
    have e3 : (a / 2 + 5 * 10 ^ 9 + 1) = (2 * (a / 2) + d + 1) := by rw [h5, hd]; omega
    have g := gA (a / 2) d
    rw [← e2, ← e3] at g
    exact Nat.lt_of_le_of_lt e1 g
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
    have g := gB e
    rw [← h10, ← he, h51] at g
    exact Nat.lt_of_le_of_lt e1 g

/-- The seed is at least the root. -/
theorem seed_ge_sqrt (a : Nat) : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := by
  have h := seed_ge_sqrt_aux a
  have hlt : a * 10 ^ 10 < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) := h
  have := sqrt_lt_of_lt_mul_self hlt
  omega

/-- The iterate in loop form, matching `Lemmas.loop_step`. -/
theorem iter_loop_form (a n : Nat) :
    iter a (n + 1) = (a * 10 ^ 10 / iter a n + iter a n) / 2 := by
  have h : iter a (n + 1) = (iter a n + a * 10 ^ 10 / iter a n) / 2 := rfl
  rw [h, Nat.add_comm]

theorem iter_zero_eq (a : Nat) : iter a 0 = a / 2 + 5 * 10 ^ 9 := rfl

theorem iter_succ_eq (a k : Nat) :
    iter a (k + 1) = newton (a * 10 ^ 10) (iter a k) := rfl

theorem N_le_s_mul (a : Nat) :
    a * 10 ^ 10 ≤ Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2) := by
  have h := Nat.lt_succ_sqrt (a * 10 ^ 10)
  grind

theorem s_big {a : Nat} (ha : 1 ≤ a) : 100000 ≤ Nat.sqrt (a * 10 ^ 10) := by
  apply le_sqrt_of_mul_self_le
  have h100 : (100000 * 100000 : Nat) = 10 ^ 10 := by decide
  omega

theorem Ndiv_le_succ {a z : Nat} (hs : 0 < Nat.sqrt (a * 10 ^ 10))
    (hz : Nat.sqrt (a * 10 ^ 10) ≤ z) :
    a * 10 ^ 10 / z ≤ Nat.sqrt (a * 10 ^ 10) + 2 := by
  have h1 : a * 10 ^ 10 / z ≤ a * 10 ^ 10 / Nat.sqrt (a * 10 ^ 10) :=
    ProofForgeFin.div_anti_right _ hs hz
  have h2 : a * 10 ^ 10 ≤ (Nat.sqrt (a * 10 ^ 10) + 2) * Nat.sqrt (a * 10 ^ 10) := by
    have h := N_le_s_mul a
    have hc : Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2)
        = (Nat.sqrt (a * 10 ^ 10) + 2) * Nat.sqrt (a * 10 ^ 10) := Nat.mul_comm _ _
    omega
  have h3 := ProofForgeFin.div_le_of_le_mul' h2
  omega

theorem s_lt_pow {a : Nat} (h : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (a * 10 ^ 10) < 2 ^ 101 := by
  apply sqrt_lt_two_pow
  omega

theorem iter_ge (a : Nat) (ha : 0 < a) (k : Nat) :
    Nat.sqrt (a * 10 ^ 10) ≤ iter a k := by
  have hs : 0 < Nat.sqrt (a * 10 ^ 10) := by
    apply sqrt_pos
    exact Nat.mul_pos ha (by decide)
  induction k with
  | zero => exact seed_ge_sqrt a
  | succ k ih =>
    rw [iter_succ_eq]
    exact sqrt_le_newton (a := a * 10 ^ 10) (Nat.lt_of_lt_of_le hs ih)

theorem seed_le_half {a : Nat} (h : a ≤ 2 ^ 167 - 1) :
    a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 166 - 1 + 5000000000 := by
  have hhalf : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by omega
  have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := ProofForgeFin.div_mono_left 2 h
  omega

theorem iter_le (a : Nat) (ha : 0 < a) (k : Nat) :
    iter a k ≤ a / 2 + 5 * 10 ^ 9 + 1 := by
  have hs : 0 < Nat.sqrt (a * 10 ^ 10) := by
    apply sqrt_pos
    exact Nat.mul_pos ha (by decide)
  have hss : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := seed_ge_sqrt a
  induction k with
  | zero => rw [iter_zero_eq]; exact Nat.le_succ _
  | succ k ih =>
    rw [iter_succ_eq]
    show newton (a * 10 ^ 10) (iter a k) ≤ _
    unfold newton
    have h1 : a * 10 ^ 10 / iter a k ≤ Nat.sqrt (a * 10 ^ 10) + 2 :=
      Ndiv_le_succ hs (iter_ge a ha k)
    have h2 : iter a k + a * 10 ^ 10 / iter a k
        ≤ (a / 2 + 5 * 10 ^ 9 + 1) + (Nat.sqrt (a * 10 ^ 10) + 2) :=
      Nat.add_le_add ih h1
    have h3 : (iter a k + a * 10 ^ 10 / iter a k) / 2
        ≤ ((a / 2 + 5 * 10 ^ 9 + 1) + (Nat.sqrt (a * 10 ^ 10) + 2)) / 2 :=
      ProofForgeFin.div_mono_left 2 h2
    omega

theorem H_all {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) (k : Nat) :
    a * 10 ^ 10 / iter a k + iter a k ≤ 2 ^ 167 - 1 := by
  have hs : 0 < Nat.sqrt (a * 10 ^ 10) := by
    have := s_big ha; omega
  have hge := iter_ge a (by omega) k
  have hle := iter_le a (by omega) k
  have hN := Ndiv_le_succ hs hge
  have hseed := seed_le_half hM
  have hs2 := s_lt_pow hM
  omega

theorem err_bound (a : Nat) (ha : 1 ≤ a) (k : Nat) :
    iter a k - Nat.sqrt (a * 10 ^ 10)
      ≤ 2 + (a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10)) / 2 ^ k := by
  have hs100 := s_big ha
  have ha0 : 0 < a := by omega
  induction k with
  | zero =>
    have e : (2 ^ 0 : Nat) = 1 := rfl
    rw [iter_zero_eq, e]
    omega
  | succ k ih =>
    rw [iter_succ_eq]
    show newton (a * 10 ^ 10) (iter a k) - Nat.sqrt (a * 10 ^ 10) ≤ _
    have hge := iter_ge a ha0 k
    have hpos : 0 < iter a k := by omega
    have hstep := newton_sub_sqrt_le_half (a := a * 10 ^ 10) hpos hge
    have hps : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ _ _
    have hdiv : (a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10)) / 2 ^ (k + 1)
        = ((a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10)) / 2 ^ k) / 2 := by
      rw [hps, Nat.div_div_eq_div_mul]
    have hmono : (iter a k - Nat.sqrt (a * 10 ^ 10)) / 2 + 1
        ≤ (2 + (a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10)) / 2 ^ k) / 2 + 1 :=
      Nat.add_le_add_right (ProofForgeFin.div_mono_left 2 ih) 1
    omega

theorem reach167 {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    iter a 167 - Nat.sqrt (a * 10 ^ 10) ≤ 2 := by
  have h := err_bound a ha 167
  have hd : (a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10)) / 2 ^ 167 = 0 := by
    apply Nat.div_eq_of_lt
    have hseed := seed_le_half hM
    have hs100 := s_big ha
    omega
  omega

/-- The loop pairs: `u 0 = a`, `u (n+1) = iter n`. -/
def u (a : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => iter a n

theorem u_zero (a : Nat) : u a 0 = a := rfl

theorem u_succ (a n : Nat) : u a (n + 1) = iter a n := rfl

theorem u_newton (a m : Nat) : u a (m + 2) = newton (a * 10 ^ 10) (u a (m + 1)) := by
  have e1 : u a (m + 2) = iter a (m + 1) := rfl
  have e2 : u a (m + 1) = iter a m := rfl
  rw [e1, e2, iter_succ_eq]

theorem seed_eq_a_cases {a : Nat} (h : a / 2 + 5 * 10 ^ 9 = a) :
    a = 9999999999 ∨ a = 10000000000 := by
  omega

theorem s_eq_low : Nat.sqrt (9999999999 * 10 ^ 10) = 9999999999 := by
  apply sqrt_eq_of_bounds
  · have : (9999999999 : Nat) ≤ 10 ^ 10 := by decide
    exact Nat.mul_le_mul_left 9999999999 this
  · decide

theorem s_eq_high : Nat.sqrt (10000000000 * 10 ^ 10) = 10000000000 := by
  apply sqrt_eq_of_bounds
  · exact Nat.le_refl _
  · decide

theorem stable_min (a : Nat) (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) (m : Nat) :
    ∀ (yn zn : Nat),
      ((yn = Nat.sqrt (a * 10 ^ 10) ∧ zn = Nat.sqrt (a * 10 ^ 10))
        ∨ (yn = Nat.sqrt (a * 10 ^ 10) ∧ zn = Nat.sqrt (a * 10 ^ 10) + 1)
        ∨ (yn = Nat.sqrt (a * 10 ^ 10) + 1 ∧ zn = Nat.sqrt (a * 10 ^ 10)))
      → (a * 10 ^ 10 / zn + zn ≤ 2 ^ 167 - 1) → (0 < zn)
      → ∃ p1 p2 : Int, loop (a : Int) m ((yn : Nat) : Int) ((zn : Nat) : Int)
          = some (p1, p2) ∧ (if p1 < p2 then p1 else p2)
          = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  induction m with
  | zero =>
    intro yn zn hmem hH hzpos
    refine ⟨((yn : Nat) : Int), ((zn : Nat) : Int), rfl, ?_⟩
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [if_neg (Int.lt_irrefl _)]
    · rw [if_pos (Int.ofNat_lt.mpr (Nat.lt_succ_self _))]
    · have hc : ¬ ((((Nat.sqrt (a * 10 ^ 10) + 1 : Nat)) : Int)
          < ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int)) := by omega
      rw [if_neg hc]
  | succ m ih =>
    intro yn zn hmem hH hzpos
    by_cases heq : zn = yn
    · subst heq
      refine ⟨_, _, loop_stop _ _ _, ?_⟩
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; rw [if_neg (Int.lt_irrefl _)]
      · omega
      · omega
    · have hstep := loop_step (a := a) (y := yn) (z := zn) m hzpos heq hH
      have hform : (a * 10 ^ 10 / zn + zn) / 2 = newton (a * 10 ^ 10) zn := by
        unfold newton; rw [Nat.add_comm]
      have hs100 := s_big ha
      have hspos : 0 < Nat.sqrt (a * 10 ^ 10) := by omega
      have hs2 := s_lt_pow hM
      rcases hmem with ⟨hyn, hzn⟩ | ⟨hyn, hzn⟩ | ⟨hyn, hzn⟩
      · omega
      · have hNs1 : newton (a * 10 ^ 10) (Nat.sqrt (a * 10 ^ 10) + 1)
            = Nat.sqrt (a * 10 ^ 10) := by
          have h := newton_of_mem (a := a * 10 ^ 10) (x := zn) hzpos ?_ ?_
          · rw [hzn] at h
            rcases h with h | ⟨hc, _, _⟩
            · exact h
            · omega
          · omega
          · omega
        have hformNs1 : (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10) := by
          rw [hform, hzn]; exact hNs1
        have next_H : a * 10 ^ 10 / ((a * 10 ^ 10 / zn + zn) / 2)
            + (a * 10 ^ 10 / zn + zn) / 2 ≤ 2 ^ 167 - 1 := by
          rw [hformNs1]
          have hNd := Ndiv_le_succ hspos (Nat.le_refl _)
          omega
        have next_pos : 0 < (a * 10 ^ 10 / zn + zn) / 2 := by
          rw [hformNs1]; omega
        have next_mem : (zn = Nat.sqrt (a * 10 ^ 10)
              ∧ (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10))
            ∨ (zn = Nat.sqrt (a * 10 ^ 10)
              ∧ (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10) + 1)
            ∨ (zn = Nat.sqrt (a * 10 ^ 10) + 1
              ∧ (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10)) :=
          Or.inr (Or.inr ⟨hzn, hformNs1⟩)
        obtain ⟨p1, p2, hp, hmin⟩ := ih zn ((a * 10 ^ 10 / zn + zn) / 2) next_mem next_H next_pos
        exact ⟨p1, p2, by rw [hstep]; exact hp, hmin⟩
      · have hNs : newton (a * 10 ^ 10) (Nat.sqrt (a * 10 ^ 10))
            = Nat.sqrt (a * 10 ^ 10)
            ∨ newton (a * 10 ^ 10) (Nat.sqrt (a * 10 ^ 10))
              = Nat.sqrt (a * 10 ^ 10) + 1 := by
          have h := newton_of_mem (a := a * 10 ^ 10)
            (x := Nat.sqrt (a * 10 ^ 10)) hspos (Nat.le_refl _) (Nat.le_succ _)
          rcases h with h | ⟨_, h, _⟩
          · exact Or.inl h
          · exact Or.inr h
        have hform2 : (a * 10 ^ 10 / zn + zn) / 2
            = newton (a * 10 ^ 10) (Nat.sqrt (a * 10 ^ 10)) := by
          rw [hform, hzn]
        have hformNs : (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10)
            ∨ (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10) + 1 := by
          rw [hform2]; exact hNs
        have hformge : Nat.sqrt (a * 10 ^ 10) ≤ (a * 10 ^ 10 / zn + zn) / 2 := by omega
        have hformle : (a * 10 ^ 10 / zn + zn) / 2 ≤ Nat.sqrt (a * 10 ^ 10) + 1 := by omega
        have next_H : a * 10 ^ 10 / ((a * 10 ^ 10 / zn + zn) / 2)
            + (a * 10 ^ 10 / zn + zn) / 2 ≤ 2 ^ 167 - 1 := by
          have hNd := Ndiv_le_succ hspos hformge
          omega
        have next_pos : 0 < (a * 10 ^ 10 / zn + zn) / 2 := by omega
        have next_mem : (zn = Nat.sqrt (a * 10 ^ 10)
              ∧ (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10))
            ∨ (zn = Nat.sqrt (a * 10 ^ 10)
              ∧ (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10) + 1)
            ∨ (zn = Nat.sqrt (a * 10 ^ 10) + 1
              ∧ (a * 10 ^ 10 / zn + zn) / 2 = Nat.sqrt (a * 10 ^ 10)) := by
          rcases hformNs with h | h
          · exact Or.inl ⟨hzn, h⟩
          · exact Or.inr (Or.inl ⟨hzn, h⟩)
        obtain ⟨p1, p2, hp, hmin⟩ := ih zn ((a * 10 ^ 10 / zn + zn) / 2) next_mem next_H next_pos
        exact ⟨p1, p2, by rw [hstep]; exact hp, hmin⟩

theorem unroll_or_stop (a : Nat) (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) (k : Nat)
    (hk : k ≤ 169) :
    loop (a : Int) 256 ((u a 0 : Nat) : Int) ((u a 1 : Nat) : Int)
        = loop (a : Int) (256 - k) ((u a k : Nat) : Int) ((u a (k + 1) : Nat) : Int)
      ∨ (∃ w : Int, loop (a : Int) 256 ((u a 0 : Nat) : Int) ((u a 1 : Nat) : Int)
          = some (w, w) ∧ w = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int)) := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    have hk' : k ≤ 169 := by omega
    have disj := ih hk'
    rcases disj with hleft | ⟨w, hw, hws⟩
    · by_cases heq : u a (k + 1) = u a k
      · right
        have hfuel : 256 - k = (256 - (k + 1)) + 1 := by omega
        have heqI : ((u a (k + 1) : Nat) : Int) = ((u a k : Nat) : Int) := by rw [heq]
        have hstop : loop (a : Int) (256 - k) ((u a k : Nat) : Int) ((u a (k + 1) : Nat) : Int)
            = some (((u a k : Nat) : Int), ((u a k : Nat) : Int)) := by
          rw [hfuel, heqI]
          exact loop_stop _ _ _
        refine ⟨((u a k : Nat) : Int), ?_, ?_⟩
        · rw [hleft, hstop]
        · by_cases hk0 : k = 0
          · subst hk0
            have hsimp : a / 2 + 5 * 10 ^ 9 = a := by
              have h := heq
              rw [u_succ, u_zero, iter_zero_eq] at h
              exact h
            have hc := seed_eq_a_cases hsimp
            have husimp : ((u a 0 : Nat) : Int) = ((a : Nat) : Int) := rfl
            rw [husimp]
            rcases hc with rfl | rfl
            · rw [s_eq_low]
            · rw [s_eq_high]
          · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk0
            have hnewt : u a (m + 1 + 1) = newton (a * 10 ^ 10) (u a (m + 1)) :=
              u_newton a m
            have hfix : newton (a * 10 ^ 10) (u a (m + 1)) = u a (m + 1) := by omega
            have hs100 := s_big ha
            have ha0 : 0 < a := by omega
            have hge : Nat.sqrt (a * 10 ^ 10) ≤ u a (m + 1) := by
              have e : u a (m + 1) = iter a m := rfl
              rw [e]; exact iter_ge a ha0 m
            have hpos : 0 < u a (m + 1) := by omega
            have hseq := eq_sqrt_of_newton_eq_self (a := a * 10 ^ 10) hpos hfix
            have euk : ((u a (m + 1) : Nat) : Int) = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
              rw [hseq]
            exact euk
      · left
        have hfuel : 256 - k = (256 - (k + 1)) + 1 := by omega
        have ha0 : 0 < a := by omega
        have e1 : u a (k + 1) = iter a k := rfl
        have hpos : 0 < u a (k + 1) := by
          rw [e1]
          have hs100 := s_big ha
          have hge := iter_ge a ha0 k
          omega
        have hH : a * 10 ^ 10 / u a (k + 1) + u a (k + 1) ≤ 2 ^ 167 - 1 := by
          rw [e1]; exact H_all ha hM k
        have hform : (a * 10 ^ 10 / u a (k + 1) + u a (k + 1)) / 2 = u a (k + 2) := by
          have e2 : u a (k + 2) = iter a (k + 1) := rfl
          rw [e1, e2, iter_loop_form]
        rw [hleft, hfuel, ← hform]
        exact loop_step _ hpos heq hH
    · right; exact ⟨w, hw, hws⟩

theorem reach168 {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    iter a 168 ≤ Nat.sqrt (a * 10 ^ 10) + 1 := by
  have h167 := reach167 ha hM
  have hs100 := s_big ha
  have ha0 : 0 < a := by omega
  have hge := iter_ge a ha0 167
  have hpos : 0 < iter a 167 := by omega
  have hd : (iter a 167 - Nat.sqrt (a * 10 ^ 10)) * (iter a 167 - Nat.sqrt (a * 10 ^ 10))
      ≤ 2 * Nat.sqrt (a * 10 ^ 10) := by
    have hm := Nat.mul_le_mul h167 h167
    omega
  have hle := newton_le_sqrt_add_one (a := a * 10 ^ 10) hpos hge hd
  have e168 : iter a 168 = iter a (167 + 1) := rfl
  rw [e168, iter_succ_eq]
  exact hle

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith _ x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨_, fun _ => rfl⟩

theorem loop256_eq (a : Nat) (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    ∃ p1 p2 : Int, loop (a : Int) 256 ((a : Nat) : Int)
        (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) = some (p1, p2)
      ∧ (if p1 < p2 then p1 else p2)
        = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  have eu0 : ((u a 0 : Nat) : Int) = ((a : Nat) : Int) := rfl
  have eu1 : ((u a 1 : Nat) : Int) = (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) := rfl
  have hdisj := unroll_or_stop a ha hM 169 (by omega)
  rw [eu0, eu1] at hdisj
  rcases hdisj with hleft | ⟨w, hw, hws⟩
  · have e169 : u a 169 = iter a 168 := u_succ a 168
    have e170 : u a 170 = newton (a * 10 ^ 10) (u a 169) := u_newton a 168
    have e170i : u a 170 = iter a 169 := u_succ a 169
    have ha0 : 0 < a := by omega
    have hs100 := s_big ha
    have hge169 : Nat.sqrt (a * 10 ^ 10) ≤ u a 169 := by
      rw [e169]; exact iter_ge a ha0 168
    have hle169 : u a 169 ≤ Nat.sqrt (a * 10 ^ 10) + 1 := by
      rw [e169]; exact reach168 ha hM
    have hpos169 : 0 < u a 169 := by omega
    have hH170 : a * 10 ^ 10 / u a 170 + u a 170 ≤ 2 ^ 167 - 1 := by
      rw [e170i]; exact H_all ha hM 169
    have h169mem : (u a 169 = Nat.sqrt (a * 10 ^ 10) ∧ u a 170 = Nat.sqrt (a * 10 ^ 10))
        ∨ (u a 169 = Nat.sqrt (a * 10 ^ 10) ∧ u a 170 = Nat.sqrt (a * 10 ^ 10) + 1)
        ∨ (u a 169 = Nat.sqrt (a * 10 ^ 10) + 1 ∧ u a 170 = Nat.sqrt (a * 10 ^ 10)) := by
      have hge : Nat.sqrt (a * 10 ^ 10) ≤ u a 169 := hge169
      have hle : u a 169 ≤ Nat.sqrt (a * 10 ^ 10) + 1 := hle169
      have hN := newton_of_mem (a := a * 10 ^ 10) (x := u a 169) hpos169 hge hle
      rcases hN with hN | ⟨hcu, hN, _⟩
      · have hu170 : u a 170 = Nat.sqrt (a * 10 ^ 10) := by rw [e170]; exact hN
        rcases (show u a 169 = Nat.sqrt (a * 10 ^ 10)
          ∨ u a 169 = Nat.sqrt (a * 10 ^ 10) + 1 from by omega) with h | h
        · exact Or.inl ⟨h, hu170⟩
        · exact Or.inr (Or.inr ⟨h, hu170⟩)
      · have hu170 : u a 170 = Nat.sqrt (a * 10 ^ 10) + 1 := by rw [e170]; exact hN
        exact Or.inr (Or.inl ⟨hcu, hu170⟩)
    have hpos170 : 0 < u a 170 := by omega
    have h87 : (256 : Nat) - 169 = 87 := rfl
    rw [h87] at hleft
    obtain ⟨p1, p2, hp, hmin⟩ :=
      stable_min a ha hM 87 (u a 169) (u a 170) h169mem hH170 hpos170
    exact ⟨p1, p2, by rw [hleft]; exact hp, hmin⟩
  · refine ⟨w, w, hw, ?_⟩
    rw [if_neg (Int.lt_irrefl _)]
    exact hws

theorem sqrt_zero : sqrt 0 = some 0 := by
  unfold sqrt vyperSqrtWith
  rw [if_neg (by decide), if_pos rfl]

theorem sqrt_eq_nat_sqrt {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    sqrt ((a : Nat) : Int) = some ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  have ha0 : 0 < a := by omega
  have hx0 : ¬ ((a : Nat) : Int) < 0 := by omega
  have hx1 : ¬ ((a : Nat) : Int) = 0 := by omega
  unfold sqrt
  rw [vyperSqrtWith_pos _ ha0 hM]
  obtain ⟨p1, p2, hp, hmin⟩ := loop256_eq a ha hM
  rw [hp, Option.map_some]
  show some (if p1 < p2 then p1 else p2) = some _
  exact congrArg _ hmin

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hsqrt
  by_cases hxneg : x < 0
  · rw [req_sqrt_neg_reverts x hxneg] at hsqrt
    exact absurd hsqrt.symm (Option.some_ne_none r)
  · have h0 : 0 ≤ x := by omega
    have hxa : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg h0
    have hM : x.toNat ≤ 2 ^ 167 - 1 := by
      have hle := hx.2
      rw [max_decimal_eq] at hle
      rw [← hxa] at hle
      exact Int.ofNat_le.mp hle
    rcases Nat.eq_zero_or_pos x.toNat with ha0 | hapos
    · have hx0 : x = 0 := by omega
      rw [hx0, sqrt_zero] at hsqrt
      have hr : r = 0 := (Option.some_inj.mp hsqrt).symm
      rw [hr, hx0]
      simp
    · have hsq := sqrt_eq_nat_sqrt (show 1 ≤ x.toNat by omega) hM
      rw [← hxa] at hsqrt
      rw [hsq] at hsqrt
      have hr : r = ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) :=
        (Option.some_inj.mp hsqrt).symm
      have hN := Nat.sqrt_le (x.toNat * 10 ^ 10)
      rw [← hxa, hr, divisor_eq]
      exact_mod_cast hN

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hsqrt
  by_cases hxneg : x < 0
  · rw [req_sqrt_neg_reverts x hxneg] at hsqrt
    exact absurd hsqrt.symm (Option.some_ne_none r)
  · have h0 : 0 ≤ x := by omega
    have hxa : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg h0
    have hM : x.toNat ≤ 2 ^ 167 - 1 := by
      have hle := hx.2
      rw [max_decimal_eq] at hle
      rw [← hxa] at hle
      exact Int.ofNat_le.mp hle
    rcases Nat.eq_zero_or_pos x.toNat with ha0 | hapos
    · have hx0 : x = 0 := by omega
      rw [hx0, sqrt_zero] at hsqrt
      have hr : r = 0 := (Option.some_inj.mp hsqrt).symm
      rw [hr, hx0]
      simp [divisor_eq]
    · have hsq := sqrt_eq_nat_sqrt (show 1 ≤ x.toNat by omega) hM
      rw [← hxa] at hsqrt
      rw [hsq] at hsqrt
      have hr : r = ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) :=
        (Option.some_inj.mp hsqrt).symm
      have hN := Nat.lt_succ_sqrt (x.toNat * 10 ^ 10)
      rw [← hxa, hr, divisor_eq]
      exact_mod_cast hN

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx h0
  have hxa : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg h0
  have hM : x.toNat ≤ 2 ^ 167 - 1 := by
    have hle := hx.2
    rw [max_decimal_eq] at hle
    rw [← hxa] at hle
    exact Int.ofNat_le.mp hle
  rcases Nat.eq_zero_or_pos x.toNat with ha0 | hapos
  · have hx0 : x = 0 := by omega
    rw [hx0, sqrt_zero]
    rfl
  · rw [← hxa, sqrt_eq_nat_sqrt (by omega) hM]
    rfl

end VyperSqrt

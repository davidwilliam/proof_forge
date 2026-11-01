import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

/-! Nat-level model of the loop: `Nof a = a * 10^10`, `seedOf`, Newton step `nstep`,
tail sequence `ZZ` from the seed, and full sequence `W` with `W 0 = a`. -/

def Nof (a : Nat) : Nat := a * 10 ^ 10

def seedOf (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

def nstep (N z : Nat) : Nat := (N / z + z) / 2

def ZZ (a : Nat) : Nat → Nat
  | 0 => seedOf a
  | Nat.succ k => nstep (Nof a) (ZZ a k)

def W (a : Nat) : Nat → Nat
  | 0 => a
  | Nat.succ k => ZZ a k

/-! Nonlinear toolkit (no `ring` in core). -/

theorem add_sq (x y : Nat) :
    (x + y) * (x + y) = x * x + (2 * (x * y) + y * y) := by
  simp only [Nat.add_mul, Nat.mul_add]
  rw [Nat.mul_comm y x]
  omega

theorem add_add_mul (p A E : Nat) :
    (p + A) * (p + E) = p * p + (p * E + (p * A + A * E)) := by
  simp only [Nat.add_mul, Nat.mul_add]
  rw [Nat.mul_comm A p]
  omega

theorem two_mul_le_add_sq (x y : Nat) : 2 * (x * y) ≤ x * x + y * y := by
  rcases Nat.le_total x y with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e1 : x * (x + d) = x * x + x * d := Nat.mul_add x x d
    have e2 := add_sq x d
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e1 : (y + d) * y = y * y + d * y := Nat.add_mul y d y
    have e2 := add_sq y d
    rw [Nat.mul_comm d y] at e1
    omega

theorem sq_le_sq_of_le {x y : Nat} (h : x ≤ y) : x * x ≤ y * y :=
  Nat.mul_le_mul h h

theorem sqrt_unique {s N : Nat} (h1 : s * s ≤ N) (h2 : N < (s + 1) * (s + 1)) :
    s = Nat.sqrt N := by
  have hr := Nat.sqrt_le N
  have hN : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  rcases Nat.lt_trichotomy s (Nat.sqrt N) with h | h | h
  · have hsr : s + 1 ≤ Nat.sqrt N := h
    have hcontra := sq_le_sq_of_le hsr
    omega
  · exact h
  · have hss := sq_le_sq_of_le (show Nat.sqrt N + 1 ≤ s by omega)
    omega

/-! Facts about `r = Nat.sqrt (Nof a)`. -/

theorem r_ge1 {a : Nat} (ha1 : 1 ≤ a) : 1 ≤ Nat.sqrt (Nof a) := by
  cases h : Nat.sqrt (Nof a) with
  | zero =>
    have hN := Nat.lt_succ_sqrt (Nof a)
    rw [h] at hN
    simp only [Nat.mul_one] at hN
    have hNge : 10 ^ 10 ≤ Nof a :=
      calc 10 ^ 10 = 1 * 10 ^ 10 := by omega
        _ ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha1
        _ = Nof a := rfl
    have d10 : (1 : Nat) < 10 ^ 10 := by decide
    omega
  | succ n => omega

theorem r_lt_pow {a : Nat} (haM : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (Nof a) < 2 ^ 101 := by
  have hleN := Nat.sqrt_le (Nof a)
  have hNM : Nof a ≤ (2 ^ 167 - 1) * 10 ^ 10 :=
    Nat.mul_le_mul_right _ haM
  have e1 : (2 ^ 101 : Nat) * 2 ^ 101 = 2 ^ 202 := by decide
  have e2 : ((2 ^ 167 - 1 : Nat)) * 10 ^ 10 < 2 ^ 201 := by decide
  have e3 : (2 ^ 201 : Nat) ≤ 2 ^ 202 := by decide
  rcases Nat.lt_trichotomy (Nat.sqrt (Nof a)) (2 ^ 101) with h | h | h
  · exact h
  · have hle : 2 ^ 101 ≤ Nat.sqrt (Nof a) := by omega
    have hsq := sq_le_sq_of_le hle
    omega
  · have hle : 2 ^ 101 ≤ Nat.sqrt (Nof a) := by omega
    have hsq := sq_le_sq_of_le hle
    omega

/-! Seed facts. -/

theorem seed_ge_r {a : Nat} (ha1 : 1 ≤ a) : Nat.sqrt (Nof a) ≤ seedOf a := by
  have hmod : a % 2 < 2 := Nat.mod_lt a (by decide)
  have hAM : 2 * (seedOf a * 10 ^ 10)
      ≤ seedOf a * seedOf a + 10 ^ 10 * 10 ^ 10 :=
    two_mul_le_add_sq _ _
  have h2sc : 2 * seedOf a + a % 2 = a + 10 ^ 10 := by
    have d : 2 * (5 * 10 ^ 9 : Nat) = 10 ^ 10 := by decide
    have hdm := Nat.div_add_mod a 2
    show 2 * (a / 2 + 5 * 10 ^ 9) + a % 2 = _
    rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (2 * (5 * 10 ^ 9)) (a % 2),
      ← Nat.add_assoc, hdm, d]
  have hcD : a % 2 * 10 ^ 10 ≤ 2 * seedOf a := by
    rcases Nat.lt_trichotomy (a % 2) 1 with h | h | h
    · have hz : a % 2 = 0 := by omega
      rw [hz]
      simp
    · rw [h]
      have hSge : 5000000000 ≤ seedOf a := by
        have d : (5 * 10 ^ 9 : Nat) = 5000000000 := by decide
        show 5000000000 ≤ a / 2 + 5 * 10 ^ 9
        omega
      have d : (10 : Nat) ^ 10 = 2 * 5000000000 := by decide
      omega
    · omega
  have key2 : 2 * (seedOf a * 10 ^ 10) + a % 2 * 10 ^ 10
      = Nof a + 10 ^ 10 * 10 ^ 10 := by
    have e1 : (2 * seedOf a + a % 2) * 10 ^ 10
        = 2 * (seedOf a * 10 ^ 10) + a % 2 * 10 ^ 10 := by
      rw [Nat.add_mul, Nat.mul_assoc]
    have e2 : (2 * seedOf a + a % 2) * 10 ^ 10 = (a + 10 ^ 10) * 10 ^ 10 := by
      rw [h2sc]
    have e3 : (a + 10 ^ 10) * 10 ^ 10 = a * 10 ^ 10 + 10 ^ 10 * 10 ^ 10 :=
      Nat.add_mul _ _ _
    have e4 : Nof a = a * 10 ^ 10 := rfl
    omega
  have hlt : Nof a < (seedOf a + 1) * (seedOf a + 1) := by
    have e := add_sq (seedOf a) 1
    simp only [Nat.mul_one] at e
    omega
  rcases Nat.lt_trichotomy (Nat.sqrt (Nof a)) (seedOf a) with h | h | h
  · omega
  · omega
  · have hle : seedOf a + 1 ≤ Nat.sqrt (Nof a) := Nat.succ_le_of_lt h
    have hcontra := sq_le_sq_of_le hle
    have hleN := Nat.sqrt_le (Nof a)
    omega

theorem seed_le {a : Nat} (haM : a ≤ 2 ^ 167 - 1) :
    seedOf a ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9 := by
  have hhalf : a / 2 ≤ 2 ^ 166 - 1 := by
    have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right haM
    have e : (2 ^ 167 - 1 : Nat) / 2 = 2 ^ 166 - 1 := by decide
    omega
  show a / 2 + 5 * 10 ^ 9 ≤ _
  omega

/-! Newton step bounds. -/

theorem step_q_le {N r z : Nat} (h2 : N < (r + 1) * (r + 1)) (hz : r ≤ z) :
    N / z ≤ r + 2 := by
  have e := add_sq r 1
  simp only [Nat.mul_one] at e
  have hNle : N ≤ r * r + 2 * r := by omega
  have g1 : r * r ≤ r * z := Nat.mul_le_mul_left r hz
  have g2 : 2 * r ≤ 2 * z := Nat.mul_le_mul_left 2 hz
  have e1 : z * (r + 2) = z * r + z * 2 := Nat.mul_add _ _ _
  have c2 : z * r = r * z := Nat.mul_comm _ _
  have c3 : z * 2 = 2 * z := Nat.mul_comm _ _
  have hNz : N ≤ z * (r + 2) := by omega
  exact Nat.div_le_of_le_mul hNz

theorem step_up1_eq {N r : Nat} (hr1 : 1 ≤ r) (h1 : r * r ≤ N)
    (h2 : N < (r + 1) * (r + 1)) : (N / (r + 1) + (r + 1)) / 2 = r := by
  cases hr : r with
  | zero => omega
  | succ t =>
    subst hr
    have hpos : 0 < t + 1 + 1 := by omega
    have hqlt : N / (t + 1 + 1) < t + 1 + 1 :=
      (Nat.div_lt_iff_lt_mul hpos).mpr h2
    have hqle : N / (t + 1 + 1) ≤ t + 1 := by omega
    have f1 : t * (t + 1 + 1) = t * t + (t + t) := by
      have g1 : t * (t + 1 + 1) = t * (t + 1) + t * 1 := Nat.mul_add _ _ _
      have g2 : t * (t + 1) = t * t + t * 1 := Nat.mul_add _ _ _
      have g3 : t * 1 = t := Nat.mul_one _
      omega
    have f2 : (t + 1) * (t + 1) = t * t + (t + (t + 1)) := by
      have g1 : (t + 1) * (t + 1) = (t + 1) * t + (t + 1) * 1 := Nat.mul_add _ _ _
      have g2 : (t + 1) * t = t * t + 1 * t := Nat.add_mul _ _ _
      have g3 : (t + 1) * 1 = t + 1 := Nat.mul_one _
      have g4 : (1 : Nat) * t = t := by omega
      omega
    have hqlb : t ≤ N / (t + 1 + 1) := by
      rw [Nat.le_div_iff_mul_le hpos]
      omega
    rcases Nat.lt_trichotomy (N / (t + 1 + 1)) (t + 1) with hq | hq | hq
    · have hqt : N / (t + 1 + 1) = t := by omega
      have eX : N / (t + 1 + 1) + (t + 1 + 1) = 2 * (t + 1) := by omega
      rw [eX, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    · have eX : N / (t + 1 + 1) + (t + 1 + 1) = 2 * (t + 1) + 1 := by omega
      rw [eX]
      omega
    · omega

theorem step_r_mem {N r : Nat} (hr1 : 1 ≤ r) (h1 : r * r ≤ N)
    (h2 : N < (r + 1) * (r + 1)) :
    (N / r + r) / 2 = r ∨ (N / r + r) / 2 = r + 1 := by
  have hpos : 0 < r := by omega
  have hqlb : r ≤ N / r := (Nat.le_div_iff_mul_le hpos).mpr h1
  have e := add_sq r 1
  simp only [Nat.mul_one] at e
  have hNle : N ≤ r * r + 2 * r := by omega
  have g1 : r * r ≤ r * (r + 2) := Nat.mul_le_mul_left r (by omega : r ≤ r + 2)
  have c1 : r * 2 = 2 * r := Nat.mul_comm _ _
  have e1 : r * (r + 2) = r * r + r * 2 := Nat.mul_add _ _ _
  have hqle : N / r ≤ r + 2 := by
    have hNz : N ≤ r * (r + 2) := by omega
    exact Nat.div_le_of_le_mul hNz
  rcases Nat.lt_trichotomy (N / r) (r + 1) with hq | hq | hq
  · have hqr : N / r = r := by omega
    have eX : N / r + r = 2 * r := by omega
    rw [eX, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    exact Or.inl rfl
  · have eX : N / r + r = 2 * r + 1 := by omega
    rw [eX]
    exact Or.inl (by omega)
  · have hqr : N / r = r + 2 := by omega
    have eX : N / r + r = 2 * (r + 1) := by omega
    rw [eX, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    exact Or.inr rfl

theorem step_lt {N r z : Nat} (h2 : N < (r + 1) * (r + 1)) (hz2 : r + 2 ≤ z) :
    (N / z + z) / 2 < z := by
  have hpos : 0 < z := by omega
  have hsq1 : (r + 1) * (r + 1) ≤ (r + 2) * (r + 2) := by
    have f : (r + 2) * (r + 2) = (r + 1) * (r + 1) + (2 * (r + 1) + 1) := by
      have g1 : (r + 2) * (r + 2) = (r + 1 + 1) * (r + 1 + 1) := by
        have er : r + 2 = r + 1 + 1 := by omega
        rw [er]
      rw [g1]
      have a1 := add_sq (r + 1) 1
      simp only [Nat.mul_one] at a1
      omega
    omega
  have hsq2 : (r + 2) * (r + 2) ≤ z * z := sq_le_sq_of_le hz2
  have hNz2 : N < z * z := by omega
  have hq : N / z < z := (Nat.div_lt_iff_lt_mul hpos).mpr hNz2
  have h2z : N / z + z < z * 2 := by omega
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr h2z

theorem halve {N r z s q : Nat} (h2 : N < (r + 1) * (r + 1))
    (hq : q = N / z) (hs : s = (q + z) / 2) (hsge : r + 1 ≤ s) (hz1 : r + 1 ≤ z) :
    (s - (r + 1)) * (2 * z) ≤ (z - (r + 1)) * (z - (r + 1)) := by
  have hqz : q * z ≤ N := by rw [hq]; exact Nat.div_mul_le_self _ _
  have h2s : 2 * s ≤ q + z := by
    rw [hs]
    have h := Nat.div_mul_le_self (q + z) 2
    have c : 2 * ((q + z) / 2) = ((q + z) / 2) * 2 := Nat.mul_comm _ _
    omega
  have hNle : N + 1 ≤ (r + 1) * (r + 1) := Nat.succ_le_of_lt h2
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le hsge
  obtain ⟨E, rfl⟩ := Nat.exists_eq_add_of_le hz1
  have sA : r + 1 + A - (r + 1) = A := by omega
  have sE : r + 1 + E - (r + 1) = E := by omega
  rw [sA, sE]
  have e1 := add_add_mul (r + 1) A E
  have e2 := add_add_mul (r + 1) E E
  have e3 : (q + (r + 1 + E)) * (r + 1 + E)
      = q * (r + 1 + E) + (r + 1 + E) * (r + 1 + E) := Nat.add_mul _ _ _
  have g1 : (2 * (r + 1 + A)) * (r + 1 + E) ≤ (q + (r + 1 + E)) * (r + 1 + E) :=
    Nat.mul_le_mul_right _ h2s
  have g2 : (2 * (r + 1 + A)) * (r + 1 + E) = 2 * ((r + 1 + A) * (r + 1 + E)) :=
    Nat.mul_assoc _ _ _
  have e6 : A * (2 * (r + 1 + E)) = 2 * (A * (r + 1 + E)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm A 2, Nat.mul_assoc]
  have e7 : A * (r + 1 + E) = (r + 1) * A + A * E := by
    rw [Nat.mul_add, Nat.mul_comm A (r + 1)]
  omega

theorem step_ge_r {N r z : Nat} (hr1 : 1 ≤ r) (h1 : r * r ≤ N)
    (h2 : N < (r + 1) * (r + 1)) (hz : r ≤ z) : r ≤ (N / z + z) / 2 := by
  rcases Nat.lt_trichotomy z r with h | h | h
  · omega
  · rw [h]
    have hq : r ≤ N / r := (Nat.le_div_iff_mul_le (show 0 < r by omega)).mpr h1
    have h2r : r + r ≤ N / r + r := Nat.add_le_add_right hq r
    have hdiv : (r + r) / 2 ≤ (N / r + r) / 2 := Nat.div_le_div_right h2r
    have e2r : (r + r) / 2 = r := by omega
    omega
  · rcases Nat.lt_trichotomy z (r + 1) with h2' | h2' | h2'
    · omega
    · subst h2'
      have e := step_up1_eq hr1 h1 h2
      omega
    · have hz2 : r + 2 ≤ z := by omega
      have hfin : 2 * r ≤ N / z + z := by
        rcases Nat.le_total z (2 * r) with h2rz | h2rz
        · have hq2 : 2 * r - z ≤ N / z := by
            rw [Nat.le_div_iff_mul_le (show 0 < z by omega)]
            have am := two_mul_le_add_sq r z
            have esub : (2 * r - z) + z = 2 * r := Nat.sub_add_cancel h2rz
            have emul : ((2 * r - z) + z) * z = (2 * r) * z := by rw [esub]
            have eadd : ((2 * r - z) + z) * z = (2 * r - z) * z + z * z :=
              Nat.add_mul _ _ _
            have eassoc : (2 * r) * z = 2 * (r * z) := Nat.mul_assoc _ _ _
            omega
          have hadd := Nat.add_le_add_right hq2 z
          have esub : (2 * r - z) + z = 2 * r := Nat.sub_add_cancel h2rz
          omega
        · have hle : z ≤ N / z + z := Nat.le_add_left _ _
          omega
      have hdiv : (2 * r) / 2 ≤ (N / z + z) / 2 := Nat.div_le_div_right hfin
      have e2r : (2 * r) / 2 = r := Nat.mul_div_cancel_left _ (by decide : 0 < 2)
      omega

theorem ZZ_zero (a : Nat) : ZZ a 0 = seedOf a := rfl

theorem ZZ_succ (a k : Nat) : ZZ a (k + 1) = nstep (Nof a) (ZZ a k) := rfl

theorem W_zero (a : Nat) : W a 0 = a := rfl

theorem W_succ (a k : Nat) : W a (k + 1) = ZZ a k := rfl

theorem nstep_eq (N z : Nat) : nstep N z = (N / z + z) / 2 := rfl

theorem ZZ_mem {a : Nat} (ha1 : 1 ≤ a) (k : Nat) :
    Nat.sqrt (Nof a) ≤ ZZ a k ∧ ZZ a k ≤ seedOf a + 1 := by
  induction k with
  | zero =>
    rw [ZZ_zero]
    exact ⟨seed_ge_r ha1, by omega⟩
  | succ k ih =>
    have hr1 := r_ge1 ha1
    have h1 := Nat.sqrt_le (Nof a)
    have h2 := Nat.lt_succ_sqrt (Nof a)
    have hlo : Nat.sqrt (Nof a) ≤ nstep (Nof a) (ZZ a k) :=
      step_ge_r hr1 h1 h2 ih.1
    have hhi : nstep (Nof a) (ZZ a k) ≤ seedOf a + 1 := by
      rcases Nat.lt_trichotomy (ZZ a k) (Nat.sqrt (Nof a) + 1) with hz | hz | hz
      · have hzr : ZZ a k = Nat.sqrt (Nof a) := by omega
        have hS := seed_ge_r ha1
        have hmem := step_r_mem hr1 h1 h2
        rw [nstep_eq, hzr]
        rcases hmem with e | e
        · rw [e]; omega
        · rw [e]; omega
      · have hS := seed_ge_r ha1
        have e := step_up1_eq hr1 h1 h2
        rw [nstep_eq, hz, e]
        omega
      · have hz2 : Nat.sqrt (Nof a) + 2 ≤ ZZ a k := by omega
        have hlt := step_lt (N := Nof a) h2 hz2
        have e : nstep (Nof a) (ZZ a k) = (Nof a / ZZ a k + ZZ a k) / 2 :=
          nstep_eq _ _
        omega
    show Nat.sqrt (Nof a) ≤ nstep (Nof a) (ZZ a k) ∧ _
    exact ⟨hlo, hhi⟩

theorem W_mem {a : Nat} (ha1 : 1 ≤ a) (j : Nat) (hj : 1 ≤ j) :
    Nat.sqrt (Nof a) ≤ W a j ∧ W a j ≤ seedOf a + 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  exact ZZ_mem ha1 t

theorem t_bound {a z : Nat} (haM : a ≤ 2 ^ 167 - 1)
    (hzr : Nat.sqrt (Nof a) ≤ z) (hzS : z ≤ seedOf a + 1) :
    Nof a / z + z ≤ 2 ^ 167 - 1 := by
  have h2 := Nat.lt_succ_sqrt (Nof a)
  have hq : Nof a / z ≤ Nat.sqrt (Nof a) + 2 := step_q_le h2 hzr
  have hr101 := r_lt_pow haM
  have hS := seed_le haM
  have dmax : ((2 : Nat) ^ 101 + 1) + (2 ^ 166 + 5 * 10 ^ 9) ≤ 2 ^ 167 - 1 := by
    decide
  omega

theorem reach {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2 ^ 167 - 1) :
    ∃ i, i ≤ 167 ∧ ZZ a i ≤ Nat.sqrt (Nof a) + 1 := by
  have hr1 := r_ge1 ha1
  have h1 := Nat.sqrt_le (Nof a)
  have h2 := Nat.lt_succ_sqrt (Nof a)
  have hS := seed_le haM
  have dE0 : seedOf a - (Nat.sqrt (Nof a) + 1) < 2 ^ 167 := by
    have dmax : seedOf a ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9 := hS
    have d167 : (2 ^ 166 - 1 : Nat) + 5 * 10 ^ 9 < 2 ^ 167 := by decide
    omega
  have P : ∀ j, (∃ i, i ≤ j ∧ ZZ a i ≤ Nat.sqrt (Nof a) + 1) ∨
      ((ZZ a j - (Nat.sqrt (Nof a) + 1)) * 2 ^ j
        ≤ seedOf a - (Nat.sqrt (Nof a) + 1)
        ∧ Nat.sqrt (Nof a) + 2 ≤ ZZ a j) := by
    intro j
    induction j with
    | zero =>
      rcases Nat.lt_trichotomy (ZZ a 0) (Nat.sqrt (Nof a) + 1) with h | h | h
      · exact Or.inl ⟨0, by omega, by omega⟩
      · exact Or.inl ⟨0, by omega, by omega⟩
      · refine Or.inr ⟨?_, by omega⟩
        have e0 : (2 : Nat) ^ 0 = 1 := by decide
        rw [e0, Nat.mul_one, ZZ_zero]
        omega
    | succ j ih =>
      rcases ih with ⟨i, hij, hZZ⟩ | ⟨hprod, hge⟩
      · exact Or.inl ⟨i, by omega, hZZ⟩
      · have hmem := ZZ_mem ha1 j
        have hsge : Nat.sqrt (Nof a) ≤ ZZ a (j + 1) :=
          step_ge_r hr1 h1 h2 hmem.1
        rcases Nat.lt_trichotomy (ZZ a (j + 1)) (Nat.sqrt (Nof a) + 1)
          with h | h | h
        · exact Or.inl ⟨j + 1, by omega, by omega⟩
        · exact Or.inl ⟨j + 1, by omega, by omega⟩
        · have hsge' : Nat.sqrt (Nof a) + 1 ≤ ZZ a (j + 1) := by omega
          have hz1 : Nat.sqrt (Nof a) + 1 ≤ ZZ a j := by omega
          have hs : ZZ a (j + 1) = (Nof a / ZZ a j + ZZ a j) / 2 := rfl
          have hq : Nof a / ZZ a j = Nof a / ZZ a j := rfl
          have hhalf := halve (N := Nof a) h2 hq hs hsge' hz1
          have hE : ZZ a j - (Nat.sqrt (Nof a) + 1) ≤ ZZ a j := by omega
          have hEz : (ZZ a j - (Nat.sqrt (Nof a) + 1))
                * (ZZ a j - (Nat.sqrt (Nof a) + 1))
              ≤ (ZZ a j - (Nat.sqrt (Nof a) + 1)) * ZZ a j :=
            Nat.mul_le_mul_left _ hE
          have hle1 : (ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * (2 * ZZ a j)
              ≤ (ZZ a j - (Nat.sqrt (Nof a) + 1)) * ZZ a j :=
            Nat.le_trans hhalf hEz
          have eassoc : ((ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * 2) * ZZ a j
              = (ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * (2 * ZZ a j) :=
            Nat.mul_assoc _ _ _
          have hle2 : ((ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * 2) * ZZ a j
              ≤ (ZZ a j - (Nat.sqrt (Nof a) + 1)) * ZZ a j := by omega
          have hA2 : (ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * 2
              ≤ ZZ a j - (Nat.sqrt (Nof a) + 1) :=
            Nat.le_of_mul_le_mul_right hle2 (show 0 < ZZ a j by omega)
          have epow : (2 : Nat) ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
          have emul1 : (ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * 2 ^ (j + 1)
              = ((ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * 2) * 2 ^ j := by
            rw [epow, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc]
          have emul2 : ((ZZ a (j + 1) - (Nat.sqrt (Nof a) + 1)) * 2) * 2 ^ j
              ≤ (ZZ a j - (Nat.sqrt (Nof a) + 1)) * 2 ^ j :=
            Nat.mul_le_mul_right _ hA2
          refine Or.inr ⟨?_, by omega⟩
          omega
  rcases P 167 with h | h
  · exact h
  · obtain ⟨hprod, hge⟩ := h
    have hE167 : 1 ≤ ZZ a 167 - (Nat.sqrt (Nof a) + 1) := by omega
    have hbig : (2 : Nat) ^ 167 ≤ (ZZ a 167 - (Nat.sqrt (Nof a) + 1)) * 2 ^ 167 := by
      have hle := Nat.mul_le_mul_right (2 ^ 167) hE167
      have o : (1 : Nat) * 2 ^ 167 = 2 ^ 167 := by omega
      omega
    omega

def Good (a t : Nat) : Prop :=
  (W a t = Nat.sqrt (Nof a) ∧ W a (t + 1) = Nat.sqrt (Nof a)) ∨
  (W a t = Nat.sqrt (Nof a) ∧ W a (t + 1) = Nat.sqrt (Nof a) + 1) ∨
  (W a t = Nat.sqrt (Nof a) + 1 ∧ W a (t + 1) = Nat.sqrt (Nof a))

theorem good_step {a t : Nat} (ha1 : 1 ≤ a) (h : Good a t) : Good a (t + 1) := by
  have hr1 := r_ge1 ha1
  have h1 := Nat.sqrt_le (Nof a)
  have h2 := Nat.lt_succ_sqrt (Nof a)
  have eW : W a (t + 1 + 1) = (Nof a / W a (t + 1) + W a (t + 1)) / 2 := rfl
  rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · have hmem := step_r_mem hr1 h1 h2
    rw [h2'] at eW
    rcases hmem with e | e
    · rw [e] at eW
      exact Or.inl ⟨h2', eW⟩
    · rw [e] at eW
      exact Or.inr (Or.inl ⟨h2', eW⟩)
  · have e := step_up1_eq hr1 h1 h2
    rw [h2'] at eW
    rw [e] at eW
    exact Or.inr (Or.inr ⟨h2', eW⟩)
  · have hmem := step_r_mem hr1 h1 h2
    rw [h2'] at eW
    rcases hmem with e | e
    · rw [e] at eW
      exact Or.inl ⟨h2', eW⟩
    · rw [e] at eW
      exact Or.inr (Or.inl ⟨h2', eW⟩)

theorem good_from {a i : Nat} (ha1 : 1 ≤ a)
    (hi_le : ZZ a i ≤ Nat.sqrt (Nof a) + 1) : ∀ d, Good a (i + 1 + d) := by
  intro d
  induction d with
  | zero =>
    show Good a (i + 1)
    have hr1 := r_ge1 ha1
    have h1 := Nat.sqrt_le (Nof a)
    have h2 := Nat.lt_succ_sqrt (Nof a)
    have eW : W a (i + 1) = ZZ a i := rfl
    have hmem := W_mem ha1 (i + 1) (by omega : 1 ≤ i + 1)
    have hle : W a (i + 1) ≤ Nat.sqrt (Nof a) + 1 := by omega
    have eW2 : W a (i + 1 + 1) = (Nof a / W a (i + 1) + W a (i + 1)) / 2 := rfl
    rcases Nat.lt_trichotomy (W a (i + 1)) (Nat.sqrt (Nof a) + 1) with h | h | h
    · have hw : W a (i + 1) = Nat.sqrt (Nof a) := by omega
      have hmem2 := step_r_mem hr1 h1 h2
      rw [hw] at eW2
      rcases hmem2 with e | e
      · rw [e] at eW2
        exact Or.inl ⟨hw, eW2⟩
      · rw [e] at eW2
        exact Or.inr (Or.inl ⟨hw, eW2⟩)
    · have e := step_up1_eq hr1 h1 h2
      rw [h] at eW2
      rw [e] at eW2
      exact Or.inr (Or.inr ⟨h, eW2⟩)
    · have hF : False := by omega
      exact False.elim hF
  | succ d ih =>
    exact good_step ha1 ih

theorem seed_eq_self {a : Nat} (h : a = seedOf a) :
    a = Nat.sqrt (Nof a) := by
  have hmod : a % 2 < 2 := Nat.mod_lt a (by decide)
  have ha : a = a / 2 + 5 * 10 ^ 9 := h
  have h5' : 5000000000 ≤ a := by
    have d : (5 * 10 ^ 9 : Nat) = 5000000000 := by decide
    omega
  have hhalf : a / 2 = a - 5000000000 := by
    have d : (5 * 10 ^ 9 : Nat) = 5000000000 := by decide
    omega
  have ha2 : 2 * (a - 5000000000) + a % 2 = a := by
    have hdm := Nat.div_add_mod a 2
    omega
  have hm : a - 5000000000 + a % 2 = 5000000000 := by omega
  have hlo : 10 ^ 10 - 1 ≤ a := by
    have d2 : (10 : Nat) ^ 10 - 1 = 5000000000 + 4999999999 := by decide
    omega
  have hhi : a ≤ 10 ^ 10 := by
    have d3 : (10 : Nat) ^ 10 = 5000000000 + 5000000000 := by decide
    omega
  rcases Nat.lt_trichotomy a (10 ^ 10) with hlt | heq | hgt
  · have ha9 : a = 10 ^ 10 - 1 := by omega
    subst ha9
    have g1 : (10 ^ 10 - 1) * (10 ^ 10 - 1) ≤ (10 ^ 10 - 1) * 10 ^ 10 := by
      decide
    have g2 : (10 ^ 10 - 1) * 10 ^ 10
        < ((10 ^ 10 - 1) + 1) * ((10 ^ 10 - 1) + 1) := by decide
    exact sqrt_unique g1 g2
  · subst heq
    have g1 : (10 ^ 10) * (10 ^ 10) ≤ (10 ^ 10) * 10 ^ 10 := by decide
    have g2 : (10 ^ 10) * 10 ^ 10 < ((10 ^ 10) + 1) * ((10 ^ 10) + 1) := by
      decide
    exact sqrt_unique g1 g2
  · have hF : False := by omega
    exact False.elim hF

theorem bridge {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2 ^ 167 - 1) (f k : Nat) :
    ∃ j, k ≤ j ∧ j ≤ k + f ∧ (j < k + f → W a j = W a (j + 1)) ∧
      loop (a : Int) f (W a k : Int) (W a (k + 1) : Int) =
        some ((W a j : Int), (W a (j + 1) : Int)) := by
  induction f generalizing k with
  | zero =>
    exact ⟨k, by omega, by omega, fun h => by omega, rfl⟩
  | succ f ih =>
    have stop_case : W a (k + 1) = W a k → ∃ j, k ≤ j ∧ j ≤ k + (f + 1) ∧
        (j < k + (f + 1) → W a j = W a (j + 1)) ∧
        loop (a : Int) (f + 1) (W a k : Int) (W a (k + 1) : Int) =
          some ((W a j : Int), (W a (j + 1) : Int)) := by
      intro heq
      refine ⟨k, by omega, by omega, fun _ => heq.symm, ?_⟩
      rw [heq]
      exact loop_stop _ _ _
    have step_case : W a (k + 1) ≠ W a k → ∃ j, k ≤ j ∧ j ≤ k + (f + 1) ∧
        (j < k + (f + 1) → W a j = W a (j + 1)) ∧
        loop (a : Int) (f + 1) (W a k : Int) (W a (k + 1) : Int) =
          some ((W a j : Int), (W a (j + 1) : Int)) := by
      intro hne
      have hz : 0 < W a (k + 1) := by
        have hmem := W_mem ha1 (k + 1) (by omega : 1 ≤ k + 1)
        have hr1 := r_ge1 ha1
        omega
      have hbound : Nof a / W a (k + 1) + W a (k + 1) ≤ 2 ^ 167 - 1 := by
        have hmem := W_mem ha1 (k + 1) (by omega : 1 ≤ k + 1)
        exact t_bound haM hmem.1 hmem.2
      have hstep := loop_step (a := a) (y := W a k) (z := W a (k + 1)) (n := f)
        hz hne hbound
      have hstep2 : loop (a : Int) (f + 1) (W a k : Int) (W a (k + 1) : Int) =
          loop (a : Int) f (W a (k + 1) : Int) (W a (k + 1 + 1) : Int) :=
        hstep
      obtain ⟨j, hkj, hjf, hstop, hloop⟩ := ih (k + 1)
      refine ⟨j, by omega, by omega, fun hlt => hstop (by omega), ?_⟩
      rw [hstep2]
      exact hloop
    rcases Nat.lt_trichotomy (W a (k + 1)) (W a k) with h | h | h
    · have hne : W a (k + 1) ≠ W a k := by omega
      exact step_case hne
    · exact stop_case h
    · have hne : W a (k + 1) ≠ W a k := by omega
      exact step_case hne

theorem fin_min_eq {m1 m2 r : Nat} (h1 : r ≤ m1) (h2 : r ≤ m2)
    (h : m1 = r ∨ m2 = r) :
    (if (m1 : Int) < (m2 : Int) then (m1 : Int) else (m2 : Int)) = (r : Int) := by
  have neg_of_not_lt : ∀ {u v : Nat}, ¬ u < v → ¬ (u : Int) < (v : Int) :=
    fun hlt hlt' => hlt (Int.ofNat_lt.mp hlt')
  rcases h with h | h
  · rcases Nat.lt_trichotomy m1 m2 with hlt | heq | hgt
    · have e : (m1 : Int) < (m2 : Int) := Int.ofNat_lt.mpr hlt
      rw [if_pos e, h]
    · have e : ¬ (m1 : Int) < (m2 : Int) := by
        have hne : ¬ m1 < m2 := by omega
        exact neg_of_not_lt hne
      have hmr : m2 = r := by omega
      rw [if_neg e, hmr]
    · have e : ¬ (m1 : Int) < (m2 : Int) := by
        have hne : ¬ m1 < m2 := by omega
        exact neg_of_not_lt hne
      have hmr : m2 = r := by omega
      rw [if_neg e, hmr]
  · rcases Nat.lt_trichotomy m1 m2 with hlt | heq | hgt
    · have e : (m1 : Int) < (m2 : Int) := Int.ofNat_lt.mpr hlt
      have hmr : m1 = r := by omega
      rw [if_pos e, hmr]
    · have e : ¬ (m1 : Int) < (m2 : Int) := by
        have hne : ¬ m1 < m2 := by omega
        exact neg_of_not_lt hne
      rw [if_neg e, h]
    · have e : ¬ (m1 : Int) < (m2 : Int) := by
        have hne : ¬ m1 < m2 := by omega
        exact neg_of_not_lt hne
      rw [if_neg e, h]

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem final_val {a j : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2 ^ 167 - 1)
    (hjf : j ≤ 256) (hstop : j < 256 → W a j = W a (j + 1)) :
    (W a j = Nat.sqrt (Nof a) ∨ W a (j + 1) = Nat.sqrt (Nof a))
    ∧ Nat.sqrt (Nof a) ≤ W a j ∧ Nat.sqrt (Nof a) ≤ W a (j + 1) := by
  have hr1 := r_ge1 ha1
  have h1 := Nat.sqrt_le (Nof a)
  have h2 := Nat.lt_succ_sqrt (Nof a)
  rcases Nat.lt_trichotomy j 256 with h256 | h256 | h256
  · have heq : W a j = W a (j + 1) := hstop h256
    rcases Nat.lt_trichotomy j 0 with hj | hj | hj
    · have hF : False := by omega
      exact False.elim hF
    · subst hj
      show (W a 0 = Nat.sqrt (Nof a) ∨ W a 1 = Nat.sqrt (Nof a))
        ∧ Nat.sqrt (Nof a) ≤ W a 0 ∧ Nat.sqrt (Nof a) ≤ W a 1
      have e0 : W a 0 = a := rfl
      have e1 : W a 1 = seedOf a := rfl
      have heq1 : W a 0 = W a 1 := heq
      have hSS : a = seedOf a := by omega
      have har : a = Nat.sqrt (Nof a) := seed_eq_self hSS
      have hw0 : W a 0 = Nat.sqrt (Nof a) := by omega
      have hw1 : W a 1 = Nat.sqrt (Nof a) := by omega
      exact ⟨Or.inl hw0, by omega, by omega⟩
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      have hmem := W_mem ha1 t.succ (by omega : 1 ≤ t.succ)
      have heW : W a (t.succ + 1) = (Nof a / W a t.succ + W a t.succ) / 2 := rfl
      rcases Nat.lt_trichotomy (W a t.succ) (Nat.sqrt (Nof a) + 1) with hw | hw | hw
      · have hwr : W a t.succ = Nat.sqrt (Nof a) := by omega
        have hw1r : W a (t.succ + 1) = Nat.sqrt (Nof a) := by omega
        exact ⟨Or.inl hwr, by omega, by omega⟩
      · have e := step_up1_eq hr1 h1 h2
        rw [hw] at heW
        rw [e] at heW
        exact ⟨Or.inr heW, by omega, by omega⟩
      · have hz2 : Nat.sqrt (Nof a) + 2 ≤ W a t.succ := by omega
        have elt := step_lt (N := Nof a) h2 hz2
        have hF : False := by omega
        exact False.elim hF
  · subst h256
    obtain ⟨i, hi167, hile⟩ := reach ha1 haM
    have h256e : i + 1 + (256 - (i + 1)) = 256 := by omega
    have hG := good_from ha1 hile (256 - (i + 1))
    rw [h256e] at hG
    rcases hG with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨Or.inl e1, by omega, by omega⟩
    · exact ⟨Or.inl e1, by omega, by omega⟩
    · exact ⟨Or.inr e2, by omega, by omega⟩
  · have hF : False := by omega
    exact False.elim hF

theorem sqrt_pos_eq {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2 ^ 167 - 1) :
    sqrt (a : Int) = some ((Nat.sqrt (Nof a) : Nat) : Int) := by
  have hfv_full : ∃ j, j ≤ 256 ∧ (j < 256 → W a j = W a (j + 1))
      ∧ loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
        = some (((W a j : Nat) : Int), ((W a (j + 1) : Nat) : Int)) := by
    obtain ⟨j, hkj, hjf, hstop, hloop⟩ := bridge ha1 haM 256 0
    have hloop2 : loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
        = some (((W a j : Nat) : Int), ((W a (j + 1) : Nat) : Int)) := hloop
    exact ⟨j, by omega, fun hlt => hstop (by omega), hloop2⟩
  show vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) = _
  rw [vyperSqrtWith_pos _ (show 0 < a by omega) haM]
  obtain ⟨j, hjf, hstop, hloop⟩ := hfv_full
  rw [hloop, Option.map_some, Option.some_inj]
  have hfv := final_val ha1 haM hjf hstop
  obtain ⟨hdisj, hrj, hrj1⟩ := hfv
  show (if (W a j : Int) < (W a (j + 1) : Int) then (W a j : Int)
    else (W a (j + 1) : Int)) = _
  exact fin_min_eq hrj hrj1 hdisj

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith _ x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop    : DeployedLoop sqrt :=
  ⟨_, fun x => rfl⟩

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := by
  intro x r hx hxr
  have hxp : MIN_DECIMAL ≤ x ∧ x ≤ MAX_DECIMAL := hx
  obtain ⟨hlo, hhi⟩ := hxp
  rcases Decidable.em (x < 0) with hneg | hnn
  · have hnone : sqrt x = none := req_sqrt_neg_reverts x hneg
    rw [hnone] at hxr
    cases hxr
  · have hx0 : 0 ≤ x := by omega
    have ha : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
    have haM : x.toNat ≤ 2 ^ 167 - 1 := by
      have hle : ((x.toNat : Nat) : Int) ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
        rw [max_decimal_eq] at hhi
        omega
      exact Int.ofNat_le.mp hle
    rcases Decidable.em (x.toNat = 0) with ha0 | ha0'
    · have hx00 : x = 0 := by rw [← ha, ha0]; rfl
      have hsqrt0 : sqrt (0 : Int) = some 0 := by
        show vyperSqrtWith _ (0 : Int) = _
        unfold vyperSqrtWith
        rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]
      rw [hx00, hsqrt0] at hxr
      have hr0 : r = 0 := Option.some_inj.mp hxr.symm
      rw [hr0, hx00]
      simp
    · have ha1 : 1 ≤ x.toNat := by omega
      have hsq := sqrt_pos_eq ha1 haM
      rw [← ha] at hxr
      rw [hsq, Option.some_inj] at hxr
      have hN : Nat.sqrt (Nof x.toNat) * Nat.sqrt (Nof x.toNat)
          ≤ x.toNat * 10 ^ 10 :=
        Nat.sqrt_le (Nof x.toNat)
      have eL : ((Nat.sqrt (Nof x.toNat) * Nat.sqrt (Nof x.toNat) : Nat) : Int)
          = ((Nat.sqrt (Nof x.toNat) : Nat) : Int)
            * ((Nat.sqrt (Nof x.toNat) : Nat) : Int) := by simp
      have eR : ((x.toNat * 10 ^ 10 : Nat) : Int)
          = ((x.toNat : Nat) : Int) * (((10 ^ 10 : Nat)) : Int) := by simp
      have hNz : ((Nat.sqrt (Nof x.toNat) * Nat.sqrt (Nof x.toNat) : Nat) : Int)
          ≤ ((x.toNat * 10 ^ 10 : Nat) : Int) :=
        Int.ofNat_le.mpr hN
      rw [eL, eR] at hNz
      rw [← hxr, ← ha, divisor_eq]
      exact hNz

theorem req_sqrt_not_below   : SqrtNotBelow sqrt := by
  intro x r hx hxr
  have hxp : MIN_DECIMAL ≤ x ∧ x ≤ MAX_DECIMAL := hx
  obtain ⟨hlo, hhi⟩ := hxp
  rcases Decidable.em (x < 0) with hneg | hnn
  · have hnone : sqrt x = none := req_sqrt_neg_reverts x hneg
    rw [hnone] at hxr
    cases hxr
  · have hx0 : 0 ≤ x := by omega
    have ha : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
    have haM : x.toNat ≤ 2 ^ 167 - 1 := by
      have hle : ((x.toNat : Nat) : Int) ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
        rw [max_decimal_eq] at hhi
        omega
      exact Int.ofNat_le.mp hle
    rcases Decidable.em (x.toNat = 0) with ha0 | ha0'
    · have hx00 : x = 0 := by rw [← ha, ha0]; rfl
      have hsqrt0 : sqrt (0 : Int) = some 0 := by
        show vyperSqrtWith _ (0 : Int) = _
        unfold vyperSqrtWith
        rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]
      rw [hx00, hsqrt0] at hxr
      have hr0 : r = 0 := Option.some_inj.mp hxr.symm
      rw [hr0, hx00]
      simp
    · have ha1 : 1 ≤ x.toNat := by omega
      have hsq := sqrt_pos_eq ha1 haM
      rw [← ha] at hxr
      rw [hsq, Option.some_inj] at hxr
      have hNb : x.toNat * 10 ^ 10
          < (Nat.sqrt (Nof x.toNat) + 1) * (Nat.sqrt (Nof x.toNat) + 1) :=
        Nat.lt_succ_sqrt (Nof x.toNat)
      have eL : ((x.toNat * 10 ^ 10 : Nat) : Int)
          = ((x.toNat : Nat) : Int) * (((10 ^ 10 : Nat)) : Int) := by simp
      have eR2 : ((((Nat.sqrt (Nof x.toNat)) + 1)
          * (((Nat.sqrt (Nof x.toNat))) + 1) : Nat) : Int)
          = ((((Nat.sqrt (Nof x.toNat) : Nat) : Int) + 1))
            * ((((Nat.sqrt (Nof x.toNat) : Nat) : Int) + 1)) := by simp
      have hNz : ((x.toNat * 10 ^ 10 : Nat) : Int)
          < ((((Nat.sqrt (Nof x.toNat)) + 1)
            * (((Nat.sqrt (Nof x.toNat))) + 1) : Nat) : Int) :=
        Int.ofNat_lt.mpr hNb
      rw [eL, eR2] at hNz
      rw [← hxr, ← ha, divisor_eq]
      exact hNz

theorem req_sqrt_total       : SqrtTotal sqrt := by
  intro x hx hx0
  have hxp : MIN_DECIMAL ≤ x ∧ x ≤ MAX_DECIMAL := hx
  obtain ⟨hlo, hhi⟩ := hxp
  have ha : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
  have haM : x.toNat ≤ 2 ^ 167 - 1 := by
    have hle : ((x.toNat : Nat) : Int) ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
      rw [max_decimal_eq] at hhi
      omega
    exact Int.ofNat_le.mp hle
  rcases Decidable.em (x.toNat = 0) with ha0 | ha0'
  · have hx00 : x = 0 := by rw [← ha, ha0]; rfl
    rw [hx00]
    show (vyperSqrtWith _ (0 : Int)).isSome = true
    unfold vyperSqrtWith
    rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]
    rfl
  · have ha1 : 1 ≤ x.toNat := by omega
    have hsq := sqrt_pos_eq ha1 haM
    show (sqrt x).isSome = true
    rw [← ha, hsq]
    rfl

end VyperSqrt

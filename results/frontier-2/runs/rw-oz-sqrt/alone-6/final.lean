import OzSqrt.Spec
import OzSqrt.Lemmas
namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem req_newton_budget : NewtonBudget sqrt :=
  ⟨7, Nat.le_refl 7, fun a => rfl⟩

/-! Pure-Nat Newton iteration mirroring the BitVec code. -/

def natStep (A X : Nat) : Nat := (X + A / X) / 2

def natIter (A : Nat) : Nat → Nat → Nat
  | 0, X => X
  | n + 1, X => natIter A n (natStep A X)

def natX0 (A : Nat) : Nat := 2 ^ (Nat.log2 A / 2)

/-- `x*x + s*s ≥ 2*(x*s)`. -/
theorem sq_add_sq_ge (x s : Nat) : 2 * (x * s) ≤ x * x + s * s := by
  rcases Nat.le_total x s with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (x + d) * (x + d) = x * x + (x * d + x * d) + d * d := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm d x]
      omega
    have hdd : 0 ≤ d * d := Nat.zero_le _
    -- goal: 2*(x*(x+d)) ≤ x*x + (x+d)*(x+d)
    have e2 : x * (x + d) = x * x + x * d := by rw [Nat.mul_add]
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (s + d) * (s + d) = s * s + (s * d + s * d) + d * d := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm d s]
      omega
    have e2 : (s + d) * s = s * s + s * d := by rw [Nat.add_mul, Nat.mul_comm d s]
    have e3 : 2 * ((s + d) * s) = 2 * (s * s) + 2 * (s * d) := by
      rw [e2]; omega
    omega

/-- Floor square root exists for every `A`. -/
theorem exists_floor (A : Nat) : ∃ s, s * s ≤ A ∧ A < (s + 1) * (s + 1) := by
  induction A with
  | zero => exact ⟨0, by omega, by omega⟩
  | succ n ih =>
    obtain ⟨s, h1, h2⟩ := ih
    by_cases h : n + 1 < (s + 1) * (s + 1)
    · exact ⟨s, by omega, h⟩
    · have h3 : n + 1 = (s + 1) * (s + 1) := by omega
      refine ⟨s + 1, by omega, ?_⟩
      have h4 : (s + 1) * (s + 1) < (s + 1 + 1) * (s + 1 + 1) := by
        have h5 : s + 1 < s + 1 + 1 := by omega
        have h6 := Nat.mul_le_mul h5 h5
        -- (s+1)*(s+1) ≤ (s+2)*(s+2); need strict
        have h7 : (s + 1) * (s + 1) < (s + 1 + 1) * (s + 1 + 1) := by
          have e1 : (s + 1) * (s + 1) = (s + 1) * (s + 1) := rfl
          -- (s+1)*(s+1) + (s+1) + (s+2) = (s+2)*(s+2)? expand manually
          have : (s + 1 + 1) * (s + 1 + 1) = (s + 1) * (s + 1) + (s + 1) + (s + 1 + 1) := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
            omega
          omega
        exact h7
      omega

/-- `(X + A / X) / 2 ≥ s` when `s * s ≤ A` and `0 < X`. -/
theorem natStep_lower (A s X : Nat) (hA : s * s ≤ A) (hX : 0 < X) :
    s ≤ natStep A X := by
  unfold natStep
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact Nat.zero_le _
  · suffices h : 2 * s ≤ X + A / X by
      have hle : (2 * s) / 2 ≤ (X + A / X) / 2 :=
        Nat.div_le_div_right h
      have heq : (2 * s) / 2 = s := by omega
      rw [heq] at hle
      exact hle
    -- X*X + A ≥ 2*(X*s)
    have hsq := sq_add_sq_ge X s
    have hXA : X * X + s * s ≤ X * X + A := by
      have : s * s ≤ A := hA
      omega
    have h2 : 2 * (X * s) ≤ X * X + A := by omega
    -- write A = (A/X)*X + A%X
    have hdm := Nat.div_add_mod A X
    have hmod : A % X < X := Nat.mod_lt _ hX
    have hqX : A / X * X ≤ A := Nat.div_mul_le_self A X
    rcases Classical.em (2 * s ≤ X + A / X) with hge' | hnge'
    · exact hge'
    · have hlt' : X + A / X + 1 ≤ 2 * s := by omega
      have hcomm : A / X * X = X * (A / X) := Nat.mul_comm _ _
      have hdm2 : X * (A / X) + A % X = A := hdm
      have hmod2 : A % X + 1 ≤ X := by omega
      have heq2 : (2 * s) * X = 2 * (X * s) := by
        rw [Nat.mul_assoc, Nat.mul_comm s X]
      -- (X + q) * X + X ≤ 2*(X*s)
      have hle : (X + A / X) * X + X ≤ 2 * (X * s) := by
        have h1 : (X + A / X + 1) * X ≤ (2 * s) * X :=
          Nat.mul_le_mul_right X hlt'
        have hex : (X + A / X + 1) * X = (X + A / X) * X + X := by
          rw [Nat.add_mul]
          omega
        rw [heq2] at h1
        omega
      have hexpand : (X + A / X) * X = X * X + X * (A / X) := by
        rw [Nat.add_mul, Nat.mul_comm (A / X) X]
      rw [hcomm] at hqX
      omega

/-- `t ≤ s` when `t*t ≤ A < (s+1)*(s+1)`. -/
theorem le_of_sq_le {A t s : Nat} (ht : t * t ≤ A) (hs : A < (s + 1) * (s + 1)) :
    t ≤ s := by
  rcases Classical.em (t ≤ s) with h | h
  · exact h
  · have hlt : s < t := Nat.lt_of_not_le h
    have hle : s + 1 ≤ t := hlt
    have hsq : (s + 1) * (s + 1) ≤ t * t := Nat.mul_le_mul hle hle
    omega

theorem natX0_pos (A : Nat) : 0 < natX0 A := by
  unfold natX0
  exact Nat.pow_pos (by decide)

/-- `natX0 A * natX0 A ≤ A` for `0 < A`. -/
theorem natX0_sq_le (A : Nat) (hA : 0 < A) : natX0 A * natX0 A ≤ A := by
  unfold natX0
  have hne : A ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hne).mp rfl
  obtain ⟨h1, _⟩ := hlog
  -- (log2 A / 2) * 2 ≤ log2 A
  have hdiv : Nat.log2 A / 2 * 2 ≤ Nat.log2 A := by
    have hdm := Nat.div_add_mod (Nat.log2 A) 2
    omega
  have hpow : 2 ^ (Nat.log2 A / 2 * 2) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide) hdiv
  have hsq : 2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2) = 2 ^ (Nat.log2 A / 2 * 2) := by
    have e1 : Nat.log2 A / 2 * 2 = Nat.log2 A / 2 + Nat.log2 A / 2 := by omega
    rw [e1, Nat.pow_add]
  omega

/-- Newton step stays positive when `A > 0`. -/
theorem natStep_pos (A X : Nat) (hA : 0 < A) (hX : 0 < X) :
    0 < natStep A X := by
  unfold natStep
  have h2 : 2 ≤ X + A / X := by
    by_cases hX1 : X = 1
    · rw [hX1, Nat.div_one]
      omega
    · have hX2 : 2 ≤ X := by omega
      have : 0 ≤ A / X := Nat.zero_le _
      omega
  have hle : (2 : Nat) / 2 ≤ (X + A / X) / 2 := Nat.div_le_div_right h2
  have heq : (2 : Nat) / 2 = 1 := by decide
  omega

/-- Iterates stay positive. -/
theorem natIter_pos (A X : Nat) (hA : 0 < A) (hX : 0 < X) (n : Nat) :
    0 < natIter A n X := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih =>
    have hstep : 0 < natStep A X := natStep_pos A X hA hX
    exact ih (natStep A X) hstep

/-- Iterates from step 1 on stay above `s`. -/
theorem natIter_lower (A s X : Nat) (hA : s * s ≤ A) (hX : 0 < X) (n : Nat) :
    s ≤ natIter A (n + 1) X := by
  rcases Nat.eq_zero_or_pos A with rfl | hApos
  · have hs0 : s = 0 := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · rfl
      · have h1 : 1 ≤ s := hs
        have h2 := Nat.mul_le_mul h1 h1
        have h3 : s * s ≤ 0 := hA
        omega
    rw [hs0]
    exact Nat.zero_le _
  · induction n generalizing X with
    | zero =>
      show s ≤ natIter A 1 X
      unfold natIter natStep
      exact natStep_lower A s X hA hX
    | succ n ih =>
      show s ≤ natIter A (n + 2) X
      unfold natIter
      have hstep : 0 < natStep A X := natStep_pos A X hApos hX
      exact ih (natStep A X) hstep

/-- `natX0 A ≤ s` when `s` is the floor root. -/
theorem natX0_le_floor (A s : Nat) (hApos : 0 < A)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1)) :
    natX0 A ≤ s :=
  le_of_sq_le (natX0_sq_le A hApos) h2

/-- `A < 2 ^ (2 * m + 2)` where `m = log2 A / 2`. -/
theorem Alat_bound (A : Nat) (hApos : 0 < A) :
    A < 2 ^ (2 * (Nat.log2 A / 2) + 2) := by
  have hne : A ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hne).mp rfl
  obtain ⟨_, h2⟩ := hlog
  -- log2 A ≤ 2*(log2 A/2)+1
  have hdiv : Nat.log2 A ≤ 2 * (Nat.log2 A / 2) + 1 := by
    have hdm := Nat.div_add_mod (Nat.log2 A) 2
    omega
  have hpow : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ (2 * (Nat.log2 A / 2) + 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- `s < 2 * 2^m` when `s` is the floor root and `m = log2 A / 2`. -/
theorem floor_lt_two_mul_pow (A s : Nat) (hApos : 0 < A)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1)) :
    s < 2 * 2 ^ (Nat.log2 A / 2) := by
  have hA2 : A < 2 ^ (2 * (Nat.log2 A / 2) + 2) := Alat_bound A hApos
  -- (2*2^m)^2 = 2^(2m+2)
  have heq : (2 * 2 ^ (Nat.log2 A / 2)) * (2 * 2 ^ (Nat.log2 A / 2)) =
      2 ^ (2 * (Nat.log2 A / 2) + 2) := by
    have e1 : (2 * 2 ^ (Nat.log2 A / 2)) = 2 ^ (Nat.log2 A / 2 + 1) := by
      rw [Nat.mul_comm, Nat.pow_succ]
    rw [e1, ← Nat.pow_add]
    congr 1
    omega
  rcases Classical.em (s < 2 * 2 ^ (Nat.log2 A / 2)) with h | h
  · exact h
  · have hge : 2 * 2 ^ (Nat.log2 A / 2) ≤ s := Nat.le_of_not_lt h
    have hsq : (2 * 2 ^ (Nat.log2 A / 2)) * (2 * 2 ^ (Nat.log2 A / 2)) ≤ s * s :=
      Nat.mul_le_mul hge hge
    rw [heq] at hsq
    omega

/-- `A ≤ s*(s+2)` when `A < (s+1)*(s+1)`. -/
theorem Alt_s_mul (A s : Nat) (h2 : A < (s + 1) * (s + 1)) :
    A ≤ s * (s + 2) := by
  have e : (s + 1) * (s + 1) = s * (s + 2) + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega
  omega

/-- First Newton iterate is at most `s + s/2 + 2`. -/
theorem natIter1_upper (A s : Nat) (hApos : 0 < A)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1)) :
    natIter A 1 (natX0 A) ≤ s + s / 2 + 2 := by
  have hX0pos : 0 < natX0 A := natX0_pos A
  have hX0le : natX0 A ≤ s := natX0_le_floor A s hApos h1 h2
  have hX0eq : natX0 A = 2 ^ (Nat.log2 A / 2) := rfl
  have hslt : s < 2 * 2 ^ (Nat.log2 A / 2) :=
    floor_lt_two_mul_pow A s hApos h1 h2
  -- A ≤ s*(s+2)
  have hAub : A ≤ s * (s + 2) := Alt_s_mul A s h2
  -- A / X0 ≤ 2*s+4
  have hdiv : A / natX0 A ≤ 2 * s + 4 := by
    have hX0pos2 : 0 < natX0 A := hX0pos
    rw [hX0eq] at hX0pos2 hX0le ⊢
    -- suffices A < (2*s+5) * 2^m
    have hlt : A < (2 * s + 5) * 2 ^ (Nat.log2 A / 2) := by
      have h1' : s * (s + 2) < (2 * s + 5) * 2 ^ (Nat.log2 A / 2) := by
        have hs2 : s < 2 * 2 ^ (Nat.log2 A / 2) := hslt
        have hmul : s * (s + 2) < 2 * 2 ^ (Nat.log2 A / 2) * (s + 2) :=
          Nat.mul_lt_mul_of_pos_right hs2 (by omega)
        have heq : 2 * 2 ^ (Nat.log2 A / 2) * (s + 2) =
            (2 * s + 4) * 2 ^ (Nat.log2 A / 2) := by
          have e1 : (2 * s + 4) = 2 * (s + 2) := by
            have h22 : (2 : Nat) * 2 = 4 := by decide
            rw [Nat.mul_add, h22]
          rw [e1]
          ac_rfl
        rw [heq] at hmul
        have hle : (2 * s + 4) * 2 ^ (Nat.log2 A / 2) ≤
            (2 * s + 5) * 2 ^ (Nat.log2 A / 2) :=
          Nat.mul_le_mul_right _ (by omega)
        exact Nat.lt_of_lt_of_le hmul hle
      have hle2 : A ≤ s * (s + 2) := hAub
      exact Nat.lt_of_le_of_lt hle2 h1'
    -- A / 2^m < 2*s+5 → ≤ 2*s+4
    have hlt2 : A / 2 ^ (Nat.log2 A / 2) < 2 * s + 5 := by
      have hpos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.pow_pos (by decide)
      have := (Nat.div_lt_iff_lt_mul hpos).mpr hlt
      -- (Nat.div_lt_iff_lt_mul hpos).mpr hlt : A / 2^m < 2*s+5 ?
      -- need y * k form: A < (2*s+5) * 2^m → A / 2^m < 2*s+5
      -- Nat.div_lt_iff_lt_mul : x/k < y ↔ x < y*k
      exact this
    omega
  -- (X0 + A/X0)/2 ≤ s + s/2+2
  show natIter A 1 (natX0 A) ≤ _
  unfold natIter natStep
  -- suffices X0 + A/X0 ≤ 2*(s+s/2+2)+1
  have hle : natX0 A + A / natX0 A ≤ 2 * (s + s / 2 + 2) + 1 := by omega
  have hmon : (natX0 A + A / natX0 A) / 2 ≤ (2 * (s + s / 2 + 2) + 1) / 2 :=
    Nat.div_le_div_right hle
  have heq : (2 * (s + s / 2 + 2) + 1) / 2 = s + s / 2 + 2 := by omega
  rw [heq] at hmon
  exact hmon

/-- `s < 2^128` when `s*s ≤ A < 2^256`. -/
theorem s_lt_pow128 {A s : Nat} (h1 : s * s ≤ A) (hA : A < 2 ^ 256) :
    s < 2 ^ 128 := by
  rcases Classical.em (s < 2 ^ 128) with h | h
  · exact h
  · have hge : 2 ^ 128 ≤ s := Nat.le_of_not_lt h
    have hsq : (2 ^ 128) * (2 ^ 128) ≤ s * s := Nat.mul_le_mul hge hge
    have heq : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by
      rw [← Nat.pow_add]
    rw [heq] at hsq
    omega

/-- `A / X ≤ s + 2` when `s ≤ X`, `A ≤ s*(s+2)`, `0 < s`. -/
theorem Adiv_le {A s X : Nat} (hs : 0 < s) (hX : s ≤ X) (hA : A ≤ s * (s + 2)) :
    A / X ≤ s + 2 := by
  have h1 : A / X ≤ (s * (s + 2)) / X := Nat.div_le_div_right hA
  have h2 : (s * (s + 2)) / X ≤ (s * (s + 2)) / s :=
    Nat.div_le_div_left hX hs
  have h3 : (s * (s + 2)) / s = s + 2 := by
    have heq : s * (s + 2) = (s + 2) * s := Nat.mul_comm _ _
    rw [heq, Nat.mul_div_cancel _ hs]
  omega

/-- Newton step preserves the `s + s/2 + 2` cap. -/
theorem natStep_le_U (A s X : Nat) (hs : 0 < s)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1))
    (hXlo : s ≤ X) (hXhi : X ≤ s + s / 2 + 2) :
    natStep A X ≤ s + s / 2 + 2 := by
  have hAub : A ≤ s * (s + 2) := Alt_s_mul A s h2
  have hdiv : A / X ≤ s + 2 := Adiv_le hs hXlo hAub
  unfold natStep
  have hle : X + A / X ≤ (s + s / 2 + 2) + (s + 2) := by omega
  have hmon : (X + A / X) / 2 ≤ ((s + s / 2 + 2) + (s + 2)) / 2 :=
    Nat.div_le_div_right hle
  have hub : ((s + s / 2 + 2) + (s + 2)) / 2 ≤ s + s / 2 + 2 := by omega
  exact Nat.le_trans hmon hub

/-- Composition of Newton iterates. -/
theorem natIter_add (A : Nat) (m n X : Nat) :
    natIter A (m + n) X = natIter A n (natIter A m X) := by
  induction m generalizing X with
  | zero => simp [natIter]
  | succ m ih =>
    show natIter A ((m + 1) + n) X = _
    have he : (m + 1) + n = (m + n) + 1 := by omega
    rw [he]
    have e1 : natIter A ((m + n) + 1) X = natIter A (m + n) (natStep A X) := rfl
    have e2 : natIter A (m + 1) X = natIter A m (natStep A X) := rfl
    rw [e1, e2, ih]

/-- Iterates from any `X` in `[s, U]` stay below `U`. -/
theorem natIter_le_U_aux (A s X : Nat) (hs : 0 < s)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1))
    (hXlo : s ≤ X) (hXhi : X ≤ s + s / 2 + 2) (n : Nat) :
    natIter A (n + 1) X ≤ s + s / 2 + 2 := by
  induction n generalizing X with
  | zero =>
    show natStep A X ≤ _
    exact natStep_le_U A s X hs h1 h2 hXlo hXhi
  | succ n ih =>
    show natIter A (n + 2) X ≤ _
    unfold natIter
    have hstep_lo : s ≤ natStep A X := by
      rcases Nat.eq_zero_or_pos A with rfl | hApos
      · have hs0 : s = 0 := by
          rcases Nat.eq_zero_or_pos s with rfl | hs'
          · rfl
          · have hle := Nat.mul_le_mul hs' hs'
            omega
        omega
      · exact natStep_lower A s X h1 (by omega)
    have hstep_hi : natStep A X ≤ s + s / 2 + 2 :=
      natStep_le_U A s X hs h1 h2 hXlo hXhi
    exact ih (natStep A X) hstep_lo hstep_hi

/-- All iterates from `X1` on stay below the cap. -/
theorem natIter_le_U (A s : Nat) (hs : 0 < s)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1))
    (hApos : 0 < A) (n : Nat) :
    natIter A (n + 1) (natX0 A) ≤ s + s / 2 + 2 := by
  rcases n with _ | n
  · exact natIter1_upper A s hApos h1 h2
  · show natIter A (n + 2) (natX0 A) ≤ _
    have h1up : natIter A 1 (natX0 A) ≤ s + s / 2 + 2 :=
      natIter1_upper A s hApos h1 h2
    have h1lo : s ≤ natIter A 1 (natX0 A) :=
      natIter_lower A s (natX0 A) h1 (natX0_pos A) 0
    have haux := natIter_le_U_aux A s (natIter A 1 (natX0 A)) hs h1 h2 h1lo h1up n
    have heq : natIter A (n + 2) (natX0 A) =
        natIter A (n + 1) (natIter A 1 (natX0 A)) := by
      have h2eq : n + 2 = 1 + (n + 1) := by omega
      rw [h2eq, natIter_add]
    rw [heq]
    exact haux

/-- `Nat.log2 A < 256` when `A < 2^256`. -/
theorem log2_lt_256 {A : Nat} (hA : A < 2 ^ 256) : Nat.log2 A < 256 := by
  rcases Nat.eq_zero_or_pos A with rfl | hpos
  · decide
  · rcases Classical.em (Nat.log2 A < 256) with h | h
    · exact h
    · have hge : 256 ≤ Nat.log2 A := Nat.le_of_not_lt h
      have hle : 2 ^ 256 ≤ A := by
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hge
        have hlog := (Nat.log2_eq_iff (by omega : A ≠ 0)).mp rfl
        omega
      omega

/-- The BitVec power-of-two estimate equals `natX0`. -/
theorem bvX0_toNat (a : U256) :
    (((1 : U256) <<< (log2 a >>> 1))).toNat = natX0 a.toNat := by
  unfold natX0
  have hlog : (log2 a).toNat = Nat.log2 a.toNat := toNat_log2 a
  have hshr : (log2 a >>> 1).toNat = Nat.log2 a.toNat / 2 := by
    have h1 : (log2 a >>> 1).toNat = (log2 a).toNat >>> 1 :=
      BitVec.toNat_ushiftRight _ _
    rw [h1, hlog, Nat.shiftRight_eq_div_pow]
  have hshift : ((1 : U256) <<< (log2 a >>> 1)).toNat =
      ((1 : U256).toNat <<< (log2 a >>> 1).toNat) % 2 ^ 256 := by
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  rw [hshift, hshr]
  have h1 : ((1 : U256).toNat) = 1 := rfl
  rw [h1, Nat.shiftLeft_eq, Nat.one_mul]
  have hA := a.isLt
  have hlog256 : Nat.log2 a.toNat < 256 := log2_lt_256 hA
  have hk : Nat.log2 a.toNat / 2 < 256 := by omega
  have hpow : 2 ^ (Nat.log2 a.toNat / 2) < 2 ^ 256 :=
    Nat.pow_lt_pow_right (by decide) hk
  rw [Nat.mod_eq_of_lt hpow]

/-- First-step sum does not wrap. -/
theorem first_step_nowrap (A : Nat) (hApos : 0 < A) (hA : A < 2 ^ 256) :
    natX0 A + A / natX0 A < 2 ^ 256 := by
  have hX0eq : natX0 A = 2 ^ (Nat.log2 A / 2) := rfl
  rw [hX0eq]
  have hm : Nat.log2 A / 2 ≤ 127 := by
    have hlog256 := log2_lt_256 hA
    omega
  have hpos : 0 < 2 ^ (Nat.log2 A / 2) := Nat.pow_pos (by decide)
  have hAlt : A < 2 ^ (2 * (Nat.log2 A / 2) + 2) := Alat_bound A hApos
  have hmul : 2 ^ (2 * (Nat.log2 A / 2) + 2) =
      2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2 + 2) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  -- A / 2^m < 2^(m+2)
  have hdiv : A / 2 ^ (Nat.log2 A / 2) < 2 ^ (Nat.log2 A / 2 + 2) := by
    have htarget : A < 2 ^ (Nat.log2 A / 2 + 2) * 2 ^ (Nat.log2 A / 2) := by
      have h2 := hAlt
      rw [hmul, Nat.mul_comm] at h2
      exact h2
    exact (Nat.div_lt_iff_lt_mul hpos).mpr htarget
  have h4eq : (2 : Nat) ^ (Nat.log2 A / 2 + 2) = 4 * 2 ^ (Nat.log2 A / 2) := by
    have : Nat.log2 A / 2 + 2 = 2 + Nat.log2 A / 2 := by omega
    rw [this, Nat.pow_add]
  rw [h4eq] at hdiv
  -- sum < 5 * 2^m ≤ 8 * 2^m = 2^(m+3) ≤ 2^130 < 2^256
  have hsum : 2 ^ (Nat.log2 A / 2) + A / 2 ^ (Nat.log2 A / 2) <
      5 * 2 ^ (Nat.log2 A / 2) := by omega
  have h5le : 5 * 2 ^ (Nat.log2 A / 2) ≤ 2 ^ (Nat.log2 A / 2 + 3) := by
    have h8eq : (2 : Nat) ^ (Nat.log2 A / 2 + 3) = 8 * 2 ^ (Nat.log2 A / 2) := by
      have : Nat.log2 A / 2 + 3 = 3 + Nat.log2 A / 2 := by omega
      rw [this, Nat.pow_add]
    omega
  have hle130 : 2 ^ (Nat.log2 A / 2 + 3) ≤ 2 ^ 130 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hlt256 : (2 : Nat) ^ 130 < 2 ^ 256 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

/-- Later-step sums do not wrap. -/
theorem later_step_nowrap (A s X : Nat) (hA : A < 2 ^ 256)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1))
    (hs : 0 < s) (hXlo : s ≤ X) (hXhi : X ≤ s + s / 2 + 2) :
    X + A / X < 2 ^ 256 := by
  have hAub : A ≤ s * (s + 2) := Alt_s_mul A s h2
  have hdiv : A / X ≤ s + 2 := Adiv_le hs hXlo hAub
  have hs128 : s < 2 ^ 128 := s_lt_pow128 h1 hA
  have hUle : X + A / X ≤ (s + s / 2 + 2) + (s + 2) := by omega
  -- (s+s/2+2)+(s+2) ≤ 3*s+4 < 2^256
  have h3le : (s + s / 2 + 2) + (s + 2) ≤ 3 * s + 4 := by omega
  have hpow128pos : 0 < 2 ^ 128 := Nat.pow_pos (by decide)
  have h4le : 4 ≤ 2 ^ 128 := by
    have h2eq : (2 : Nat) ^ 128 = 4 * 2 ^ 126 := by
      have hsplit : (128 : Nat) = 2 + 126 := by omega
      rw [hsplit, Nat.pow_add]
    omega
  have h256eq : (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 := by
    rw [← Nat.pow_add]
  have hbig : 3 * s + 4 < 2 ^ 256 := by
    rw [h256eq]
    have h1le : (1 : Nat) ≤ 2 ^ 128 := by omega
    -- 3*s+4 ≤ 4*2^128 ≤ 2^128*2^128
    have hle1 : 3 * s + 4 ≤ 4 * 2 ^ 128 := by omega
    have hle2 : 4 * 2 ^ 128 ≤ 2 ^ 128 * 2 ^ 128 :=
      Nat.mul_le_mul_right _ h4le
    omega
  omega

/-- Composition for BitVec `iterate`. -/
theorem bvIterate_add (f : U256 → U256) (m n : Nat) (x : U256) :
    iterate f (m + n) x = iterate f n (iterate f m x) := by
  induction m generalizing x with
  | zero => simp [iterate]
  | succ m ih =>
    have he : (m + 1) + n = (m + n) + 1 := by omega
    rw [he]
    have e1 : iterate f ((m + n) + 1) x = iterate f (m + n) (f x) := rfl
    have e2 : iterate f (m + 1) x = iterate f m (f x) := rfl
    rw [e1, e2, ih]

/-- BitVec Newton steps track Nat steps from any `X` in `[s, U]`. -/
theorem bvIter_eq_aux (a : U256) (s X : Nat) (r : U256)
    (hA : a.toNat < 2 ^ 256)
    (h1 : s * s ≤ a.toNat) (h2 : a.toNat < (s + 1) * (s + 1)) (hs : 0 < s)
    (hr : r.toNat = X) (hXlo : s ≤ X) (hXhi : X ≤ s + s / 2 + 2) (hXpos : 0 < X)
    (k : Nat) :
    (iterate (newtonStep a) k r).toNat = natIter a.toNat k X := by
  induction k generalizing r X with
  | zero => simp [iterate, natIter, hr]
  | succ k ih =>
    have e1 : iterate (newtonStep a) (k + 1) r =
        iterate (newtonStep a) k (newtonStep a r) := rfl
    have e2 : natIter a.toNat (k + 1) X = natIter a.toNat k (natStep a.toNat X) := rfl
    rw [e1, e2]
    have hwrap : r.toNat + a.toNat / r.toNat < 2 ^ 256 := by
      rw [hr]
      exact later_step_nowrap a.toNat s X hA h1 h2 hs hXlo hXhi
    have hstep : (newtonStep a r).toNat = natStep a.toNat X := by
      have h := toNat_newtonStep a r hwrap
      rw [hr] at h
      -- h : (newtonStep a r).toNat = (X + a.toNat / X)/2 ; natStep unfolds to same
      unfold natStep
      exact h
    have hXpos' : 0 < natStep a.toNat X := by
      rcases Nat.eq_zero_or_pos a.toNat with h0 | hApos
      · have hs0 : s = 0 := by
          rcases Nat.eq_zero_or_pos s with rfl | hs'
          · rfl
          · have hle := Nat.mul_le_mul hs' hs'
            omega
        omega
      · exact natStep_pos _ _ hApos hXpos
    have hlo' : s ≤ natStep a.toNat X := by
      rcases Nat.eq_zero_or_pos a.toNat with h0 | hApos
      · have hs0 : s = 0 := by
          rcases Nat.eq_zero_or_pos s with rfl | hs'
          · rfl
          · have hle := Nat.mul_le_mul hs' hs'
            omega
        omega
      · exact natStep_lower _ _ _ h1 hXpos
    have hhi' : natStep a.toNat X ≤ s + s / 2 + 2 :=
      natStep_le_U _ _ _ hs h1 h2 hXlo hXhi
    exact ih (natStep a.toNat X) (newtonStep a r) hstep hlo' hhi' hXpos'

/-- `min(X, A/X)^2 ≤ A` for `0 < X`. -/
theorem min_sq_le (A X : Nat) (hX : 0 < X) :
    Nat.min X (A / X) * Nat.min X (A / X) ≤ A := by
  have hQM : A / X * X ≤ A := Nat.div_mul_le_self A X
  have hQM' : X * (A / X) ≤ A := by
    rw [Nat.mul_comm]
    exact hQM
  rcases Classical.em (X ≤ A / X) with h | h
  · have hmin : Nat.min X (A / X) = X := Nat.min_eq_left h
    rw [hmin]
    have hle : X * X ≤ X * (A / X) := Nat.mul_le_mul_left X h
    omega
  · have hlt : A / X < X := Nat.lt_of_not_le h
    have hle : A / X ≤ X := Nat.le_of_lt hlt
    have hmin : Nat.min X (A / X) = A / X := Nat.min_eq_right hle
    rw [hmin]
    have hle2 : A / X * (A / X) ≤ A / X * X := Nat.mul_le_mul_left _ hle
    omega

/-- Full 7-step bridge from `X0`. -/
theorem bvIter_eq_full (a : U256) (s : Nat)
    (hApos : 0 < a.toNat) (hA : a.toNat < 2 ^ 256)
    (h1 : s * s ≤ a.toNat) (h2 : a.toNat < (s + 1) * (s + 1)) (hs : 0 < s)
    (k : Nat) :
    (iterate (newtonStep a) k (((1 : U256) <<< (log2 a >>> 1)))).toNat =
      natIter a.toNat k (natX0 a.toNat) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [iterate, natIter]
    exact bvX0_toNat a
  · have k_eq : k = (k - 1) + 1 := by omega
    -- first step
    have hr0 : (((1 : U256) <<< (log2 a >>> 1))).toNat = natX0 a.toNat :=
      bvX0_toNat a
    have hX0pos : 0 < natX0 a.toNat := natX0_pos _
    have hwrap0 : (((1 : U256) <<< (log2 a >>> 1))).toNat +
        a.toNat / (((1 : U256) <<< (log2 a >>> 1))).toNat < 2 ^ 256 := by
      rw [hr0]
      exact first_step_nowrap _ hApos hA
    have hfirst : (newtonStep a (((1 : U256) <<< (log2 a >>> 1)))).toNat =
        natStep a.toNat (natX0 a.toNat) := by
      have h := toNat_newtonStep a _ hwrap0
      rw [hr0] at h
      unfold natStep
      exact h
    have hX1 : natIter a.toNat 1 (natX0 a.toNat) = natStep a.toNat (natX0 a.toNat) := rfl
    have hX1pos : 0 < natIter a.toNat 1 (natX0 a.toNat) := by
      rw [hX1]
      exact natStep_pos _ _ hApos hX0pos
    have hX1lo : s ≤ natIter a.toNat 1 (natX0 a.toNat) :=
      natIter_lower _ _ _ h1 hX0pos 0
    have hX1hi : natIter a.toNat 1 (natX0 a.toNat) ≤ s + s / 2 + 2 :=
      natIter1_upper _ _ hApos h1 h2
    -- decompose k = 1 + (k-1)
    have hk1 : k = 1 + (k - 1) := by omega
    have hiter : iterate (newtonStep a) k (((1 : U256) <<< (log2 a >>> 1))) =
        iterate (newtonStep a) (k - 1)
          (iterate (newtonStep a) 1 (((1 : U256) <<< (log2 a >>> 1)))) := by
      have hk1' : 1 + (k - 1) = k := by omega
      have h := bvIterate_add (newtonStep a) 1 (k - 1)
        (((1 : U256) <<< (log2 a >>> 1)))
      rw [hk1'] at h
      exact h
    have hnat : natIter a.toNat k (natX0 a.toNat) =
        natIter a.toNat (k - 1) (natIter a.toNat 1 (natX0 a.toNat)) := by
      have hk1' : 1 + (k - 1) = k := by omega
      have h := natIter_add a.toNat 1 (k - 1) (natX0 a.toNat)
      rw [hk1'] at h
      exact h
    rw [hiter, hnat]
    have hr1 : (iterate (newtonStep a) 1 (((1 : U256) <<< (log2 a >>> 1)))).toNat =
        natIter a.toNat 1 (natX0 a.toNat) := by
      show (newtonStep a _).toNat = _
      rw [hX1]
      exact hfirst
    have hX1pos' : 0 < natIter a.toNat 1 (natX0 a.toNat) := hX1pos
    exact bvIter_eq_aux a s _ _ hA h1 h2 hs hr1 hX1lo hX1hi hX1pos' (k - 1)

/-- `newtonSqrt 7` on values is `min(X7, A/X7)`. -/
theorem sqrt_toNat_aux (a : U256) (s : Nat)
    (hApos : 0 < a.toNat) (hA : a.toNat < 2 ^ 256)
    (h1 : s * s ≤ a.toNat) (h2 : a.toNat < (s + 1) * (s + 1)) (hs : 0 < s) :
    (newtonSqrt 7 a).toNat =
      Nat.min (natIter a.toNat 7 (natX0 a.toNat))
        (a.toNat / natIter a.toNat 7 (natX0 a.toNat)) := by
  unfold newtonSqrt
  have ha0 : ¬ a = 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp at this
    omega
  rw [ite_eq_right ha0]
  simp only
  have hR : (iterate (newtonStep a) 7 (((1 : U256) <<< (log2 a >>> 1)))).toNat =
      natIter a.toNat 7 (natX0 a.toNat) :=
    bvIter_eq_full a s hApos hA h1 h2 hs 7
  have hmin := toNat_min
    (iterate (newtonStep a) 7 (((1 : U256) <<< (log2 a >>> 1))))
    (a / iterate (newtonStep a) 7 (((1 : U256) <<< (log2 a >>> 1))))
  rw [hmin, BitVec.toNat_udiv, hR]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  show (newtonSqrt 7 a).toNat * (newtonSqrt 7 a).toNat ≤ a.toNat
  rcases Nat.eq_zero_or_pos a.toNat with h0 | hApos
  · have ha0 : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
    have hsqrt : newtonSqrt 7 a = 0 := by
      unfold newtonSqrt
      rw [ite_eq_left ha0]
    rw [hsqrt]
    simp [h0]
  · obtain ⟨s, h1, h2⟩ := exists_floor a.toNat
    have hs : 0 < s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs'
      · simp at h1 h2
        omega
      · exact hs'
    have hA : a.toNat < 2 ^ 256 := a.isLt
    have hsqrt := sqrt_toNat_aux a s hApos hA h1 h2 hs
    rw [hsqrt]
    have hXpos : 0 < natIter a.toNat 7 (natX0 a.toNat) :=
      natIter_pos _ _ hApos (natX0_pos _) 7
    exact min_sq_le _ _ hXpos
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight : SqrtUpTight sqrt := sorry
theorem req_mint_backed : MintBacked sqrt := sorry
theorem req_mint_full : MintFull sqrt := sorry
theorem req_mint_live : MintLive sqrt := sorry

end OzSqrt

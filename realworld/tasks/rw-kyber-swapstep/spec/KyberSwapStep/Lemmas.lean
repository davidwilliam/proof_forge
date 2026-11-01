import KyberSwapStep.Spec
/-!
# Helper lemmas (protected, agent-visible)

Proved facts about the protected definitions. They say nothing about the definition hole; a
candidate may use them.

* The checked operations, `mulDivFloor`, `mulDivCeiling` and the casts, through `toNat`: each
  returns `some z` exactly when its exact result fits, and `z.toNat` is that result
  (`add_eq_some_iff`, `mulDivFloor_eq_some_iff`, ...), with the floor and ceiling bounds
  (`mulDivFloor_spec`, `mulDivCeiling_spec`).
* The values of the constants (`toNat_TWO_POW_96`, ...).
* `toNat_sqrt`, `sqrt_spec`: the port of `QuadMath.sqrt` (the Babylonian loop) is Lean core's
  `Nat.sqrt`, the square root rounded down, on every `uint256`; `sqrtUp_spec`: `sqrtUp` returns it
  rounded up.
-/

namespace KyberSwapStep

/-! ## Checked operations -/

theorem fit_eq_some_iff {n : Nat} {z : U256} : fit n = some z ↔ n < 2 ^ 256 ∧ z.toNat = n := by
  unfold fit
  by_cases h : n < 2 ^ 256
  · rw [ite_eq_left h]
    constructor
    · intro e; cases e; exact ⟨h, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]⟩
    · rintro ⟨-, e⟩; congr; apply BitVec.eq_of_toNat_eq; rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  · rw [ite_eq_right h]; simp [h]

theorem add_eq_some_iff {a b z : U256} :
    add a b = some z ↔ a.toNat + b.toNat < 2 ^ 256 ∧ z.toNat = a.toNat + b.toNat := fit_eq_some_iff

theorem mul_eq_some_iff {a b z : U256} :
    mul a b = some z ↔ a.toNat * b.toNat < 2 ^ 256 ∧ z.toNat = a.toNat * b.toNat := fit_eq_some_iff

theorem sub_eq_some_iff {a b z : U256} :
    sub a b = some z ↔ b.toNat ≤ a.toNat ∧ z.toNat = a.toNat - b.toNat := by
  unfold sub
  by_cases h : b.toNat ≤ a.toNat
  · rw [ite_eq_left h, fit_eq_some_iff]
    have := a.isLt
    constructor
    · rintro ⟨-, e⟩; exact ⟨h, e⟩
    · rintro ⟨-, e⟩; exact ⟨by omega, e⟩
  · rw [ite_eq_right h]; simp [h]

theorem toNat_pos_of_ne_zero {d : U256} (h : ¬ d = 0) : 0 < d.toNat := by
  rcases Nat.eq_zero_or_pos d.toNat with e | e
  · exact absurd (BitVec.eq_of_toNat_eq (by simpa using e)) h
  · exact e

theorem mulDivFloor_eq_some_iff {a b d z : U256} :
    mulDivFloor a b d = some z ↔
      0 < d.toNat ∧ a.toNat * b.toNat / d.toNat < 2 ^ 256 ∧ z.toNat = a.toNat * b.toNat / d.toNat := by
  unfold mulDivFloor
  by_cases h : d = 0
  · subst h; simp
  · rw [ite_eq_right h, fit_eq_some_iff]; simp [toNat_pos_of_ne_zero h]

theorem mulDivCeiling_eq_some_iff {a b d z : U256} :
    mulDivCeiling a b d = some z ↔
      0 < d.toNat ∧ (a.toNat * b.toNat + d.toNat - 1) / d.toNat < 2 ^ 256 ∧
        z.toNat = (a.toNat * b.toNat + d.toNat - 1) / d.toNat := by
  unfold mulDivCeiling
  by_cases h : d = 0
  · subst h; simp
  · rw [ite_eq_right h, fit_eq_some_iff]; simp [toNat_pos_of_ne_zero h]

theorem divFloor_eq_some_iff {a b z : U256} :
    divFloor a b = some z ↔ 0 < b.toNat ∧ z.toNat = a.toNat / b.toNat := by
  unfold divFloor
  by_cases h : b = 0
  · subst h; simp
  · have hb := toNat_pos_of_ne_zero h
    have : a.toNat / b.toNat < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
    rw [ite_eq_right h, fit_eq_some_iff]; simp [hb, this]

theorem divCeiling_eq_some_iff {a b z : U256} :
    divCeiling a b = some z ↔
      0 < b.toNat ∧ (a.toNat + b.toNat - 1) / b.toNat < 2 ^ 256 ∧
        z.toNat = (a.toNat + b.toNat - 1) / b.toNat := by
  unfold divCeiling
  by_cases h : b = 0
  · subst h; simp
  · rw [ite_eq_right h, fit_eq_some_iff]; simp [toNat_pos_of_ne_zero h]

/-- Floor bounds of a successful `mulDivFloor`: `z * d ≤ a * b < (z + 1) * d`. -/
theorem mulDivFloor_spec {a b d z : U256} (h : mulDivFloor a b d = some z) :
    0 < d.toNat ∧ z.toNat * d.toNat ≤ a.toNat * b.toNat ∧ a.toNat * b.toNat < (z.toNat + 1) * d.toNat := by
  obtain ⟨hd, -, hz⟩ := mulDivFloor_eq_some_iff.1 h
  rw [hz]
  refine ⟨hd, Nat.div_mul_le_self _ _, ?_⟩
  rw [Nat.add_mul, Nat.one_mul]
  have := Nat.lt_div_mul_add (a := a.toNat * b.toNat) hd
  omega

/-- Ceiling bounds of a successful `mulDivCeiling`: `a * b ≤ z * d < a * b + d`. -/
theorem mulDivCeiling_spec {a b d z : U256} (h : mulDivCeiling a b d = some z) :
    0 < d.toNat ∧ a.toNat * b.toNat ≤ z.toNat * d.toNat ∧ z.toNat * d.toNat < a.toNat * b.toNat + d.toNat := by
  obtain ⟨hd, -, hz⟩ := mulDivCeiling_eq_some_iff.1 h
  rw [hz]
  refine ⟨hd, ?_, ?_⟩
  · have := Nat.lt_div_mul_add (a := a.toNat * b.toNat + d.toNat - 1) hd
    omega
  · have := Nat.div_mul_le_self (a.toNat * b.toNat + d.toNat - 1) d.toNat
    omega

theorem mulDiv_false (a b d : U256) : mulDiv false a b d = mulDivFloor a b d := rfl

theorem mulDiv_true (a b d : U256) : mulDiv true a b d = mulDivCeiling a b d := rfl

theorem divRound_false (a b : U256) : divRound false a b = divFloor a b := rfl

theorem divRound_true (a b : U256) : divRound true a b = divCeiling a b := rfl

theorem toUint160_eq_some_iff {y z : U256} : toUint160 y = some z ↔ y.toNat < 2 ^ 160 ∧ z = y := by
  unfold toUint160
  by_cases h : y.toNat < 2 ^ 160
  · rw [ite_eq_left h]; constructor
    · intro e; cases e; exact ⟨h, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  · rw [ite_eq_right h]; simp [h]

theorem toInt256_eq_some_iff {y : U256} {z : Int} :
    toInt256 y = some z ↔ y.toNat < 2 ^ 255 ∧ z = y.toNat := by
  unfold toInt256
  by_cases h : y.toNat < 2 ^ 255
  · rw [ite_eq_left h]; constructor
    · intro e; cases e; exact ⟨h, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  · rw [ite_eq_right h]; simp [h]

theorem revToInt256_eq_some_iff {y : U256} {z : Int} :
    revToInt256 y = some z ↔ y.toNat < 2 ^ 255 ∧ z = -(y.toNat : Int) := by
  unfold revToInt256
  by_cases h : y.toNat < 2 ^ 255
  · rw [ite_eq_left h]; constructor
    · intro e; cases e; exact ⟨h, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  · rw [ite_eq_right h]; simp [h]

/-! ## Constants -/

theorem toNat_TWO_POW_96 : TWO_POW_96.toNat = 2 ^ 96 := by decide

theorem toNat_FEE_UNITS : FEE_UNITS.toNat = 100000 := by decide

theorem toNat_TWO_FEE_UNITS : TWO_FEE_UNITS.toNat = 200000 := by decide

/-! ## The square root of `QuadMath` -/

/-- One iteration from a positive `x` never goes below a number `r` with `r * r ≤ y`
(AM-GM with floors). -/
theorem le_babylonian_step {y r x : Nat} (hr : r * r ≤ y) (hx : 0 < x) : r ≤ (y / x + x) / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide)).2
  apply Nat.le_of_not_lt
  intro hlt
  have hq : y < (y / x + 1) * x := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hx
  have h1 : y / x + 1 + x ≤ 2 * r := by omega
  have h2 : (y / x + 1) * x ≤ r * r := by
    generalize y / x + 1 = q at h1
    have : q ≤ 2 * r - x := by omega
    have h3 : q * x ≤ (2 * r - x) * x := Nat.mul_le_mul_right x this
    have h4 : (2 * r - x) * x ≤ r * r := by
      rcases Nat.le_total x r with h | h
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        have e : 2 * (x + d) - x = x + 2 * d := by omega
        rw [e]; grind
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        have e : 2 * r - (r + d) = r - d := by omega
        rw [e]
        rcases Nat.le_total d r with h' | h'
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h'
          have e2 : d + k - d = k := by omega
          rw [e2]; grind
        · have e2 : r - d = 0 := by omega
          rw [e2]; simp
    omega
  omega

/-- Above a number `r` with `y < (r + 1) * (r + 1)`, one iteration at least halves the distance to
`r`. -/
theorem babylonian_step_le {y r x : Nat} (hr : y < (r + 1) * (r + 1)) (hx : r < x) :
    (y / x + x) / 2 ≤ (r + x) / 2 := by
  have hq : y / x ≤ r := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    exact Nat.lt_of_lt_of_le hr (Nat.mul_le_mul_left _ hx)
  exact Nat.div_le_div_right (by omega)

/-- The loop returns `r`, the root rounded down, from any `x` with `r ≤ x < z` and
`x - r < 2^n`, given at least `n + 1` iterations. -/
theorem babylonian_eq {y r : Nat} (h1 : r * r ≤ y) (h2 : y < (r + 1) * (r + 1)) :
    ∀ (n m z x : Nat), r ≤ x → x < z → x - r < 2 ^ n → babylonian y (n + 1 + m) z x = r := by
  intro n
  induction n with
  | zero =>
    intro m z x hrx hxz he
    have hx : x = r := by simp at he; omega
    subst hx
    rw [show 0 + 1 + m = m + 1 by omega]
    simp only [babylonian, ite_eq_left hxz]
    cases m with
    | zero => rfl
    | succ m =>
      simp only [babylonian]
      have hr0 : 0 < x ∨ x = 0 := by omega
      rcases hr0 with hpos | h0
      · rw [ite_eq_right (Nat.not_lt.2 (le_babylonian_step h1 hpos))]
      · subst h0; simp
  | succ n ih =>
    intro m z x hrx hxz he
    rw [show n + 1 + 1 + m = (n + 1 + m) + 1 by omega]
    simp only [babylonian, ite_eq_left hxz]
    rcases Nat.eq_or_lt_of_le hrx with e | hlt
    · subst e
      cases h : n + 1 + m with
      | zero => omega
      | succ k =>
        simp only [babylonian]
        rcases Nat.eq_zero_or_pos r with h0 | hpos
        · subst h0; simp
        · rw [ite_eq_right (Nat.not_lt.2 (le_babylonian_step h1 hpos))]
    · have hx : 0 < x := by omega
      apply ih m x ((y / x + x) / 2) (le_babylonian_step h1 hx)
      · have := babylonian_step_le h2 hlt; omega
      · have := babylonian_step_le h2 hlt
        rw [Nat.pow_succ] at he
        omega

/-- The port of `QuadMath.sqrt` is Lean core's `Nat.sqrt` on every `uint256`. -/
theorem toNat_sqrt (y : U256) : (sqrt y).toNat = Nat.sqrt y.toNat := by
  have hy := y.isLt
  have hr1 := Nat.sqrt_le y.toNat
  have hr2 := Nat.lt_succ_sqrt y.toNat
  simp only [Nat.succ_eq_add_one] at hr2
  unfold sqrt
  by_cases h3 : 3 < y.toNat
  · rw [ite_eq_left h3]
    have hrx : Nat.sqrt y.toNat ≤ y.toNat / 2 + 1 := by
      have := le_babylonian_step hr1 (x := y.toNat) (by omega)
      rw [Nat.div_self (by omega)] at this
      omega
    have h1 : 1 ≤ Nat.sqrt y.toNat := by
      apply Nat.le_of_lt_succ
      apply Nat.lt_of_not_le
      intro hle
      have : Nat.sqrt y.toNat = 0 := by omega
      rw [this] at hr2; omega
    have h256 : (2 : Nat) ^ 256 = 2 * 2 ^ 255 := by rw [Nat.pow_succ, Nat.mul_comm]
    have hb := babylonian_eq hr1 hr2 255 256 y.toNat (y.toNat / 2 + 1) hrx (by omega) (by omega)
    rw [show 255 + 1 + 256 = 512 by rfl] at hb
    have hle : Nat.sqrt y.toNat ≤ y.toNat :=
      Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega)) hr1
    rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hy)]
  · rw [ite_eq_right h3]
    have hs : Nat.sqrt y.toNat * Nat.sqrt y.toNat ≤ 3 := by omega
    by_cases h0 : y.toNat ≠ 0
    · rw [ite_eq_left h0]
      have : Nat.sqrt y.toNat < 2 := by
        apply Nat.lt_of_not_le; intro h2
        have := Nat.mul_le_mul h2 h2; omega
      have : Nat.sqrt y.toNat ≠ 0 := by
        intro e; rw [e] at hr2; omega
      show (1 : U256).toNat = _
      rw [show (1 : U256).toNat = 1 by rfl]; omega
    · rw [ite_eq_right h0]
      have e : y.toNat = 0 := by omega
      rw [e]; rfl

/-- `QuadMath.sqrt` returns the square root rounded down: `s * s ≤ y < (s + 1) * (s + 1)` for
`s = sqrt y`, on every `uint256`. -/
theorem sqrt_spec (y : U256) :
    (sqrt y).toNat * (sqrt y).toNat ≤ y.toNat ∧ y.toNat < ((sqrt y).toNat + 1) * ((sqrt y).toNat + 1) := by
  rw [toNat_sqrt]
  exact ⟨Nat.sqrt_le _, Nat.lt_succ_sqrt _⟩

/-- `sqrtUp` returns the square root rounded up: `y ≤ u * u`, and `(u - 1) * (u - 1) < y` when
`y > 0`, for `u = sqrtUp y`. -/
theorem sqrtUp_spec (y : U256) :
    y.toNat ≤ (sqrtUp y).toNat * (sqrtUp y).toNat ∧
      (0 < y.toNat → ((sqrtUp y).toNat - 1) * ((sqrtUp y).toNat - 1) < y.toNat) := by
  obtain ⟨h1, h2⟩ := sqrt_spec y
  have hy := y.isLt
  unfold sqrtUp
  generalize sqrt y = s at h1 h2
  by_cases h : s.toNat * s.toNat < y.toNat
  · rw [ite_eq_left h]
    have hs : s.toNat + 1 < 2 ^ 256 := by
      rcases Nat.eq_zero_or_pos s.toNat with e | e
      · rw [e]; decide
      · have : s.toNat < y.toNat := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ e) h
        omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
    refine ⟨Nat.le_of_lt h2, fun _ => ?_⟩
    simpa using h
  · rw [ite_eq_right h]
    have e : s.toNat * s.toNat = y.toNat := by omega
    refine ⟨by omega, fun hpos => ?_⟩
    have : 0 < s.toNat := by
      rcases Nat.eq_zero_or_pos s.toNat with z | z
      · rw [z] at e; omega
      · exact z
    have : s.toNat - 1 < s.toNat := by omega
    have := Nat.mul_self_lt_mul_self this
    omega

end KyberSwapStep

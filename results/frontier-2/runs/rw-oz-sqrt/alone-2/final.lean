import OzSqrt.Spec
import OzSqrt.Lemmas
/-!
The square-root routine under repair, `Math.sqrt(uint256 a)` in the style of OpenZeppelin
Contracts `Math.sol`, as this pool's first deposit calls it.
Fixed: seven Newton iterations (the deployed `Math.sqrt` has seven lines
`result = (result + a / result) >> 1;`), so the estimate converges on all 256-bit inputs.
-/
namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

/-- `min u (A / u)` squared never exceeds `A`. -/
theorem min_sq_le (u A : Nat) : (Nat.min u (A / u)) ^ 2 ≤ A := by
  by_cases hu : u = 0
  · subst hu; simp
  have hle : A / u * u ≤ A := Nat.div_mul_le_self A u
  have h1 : Nat.min u (A / u) ≤ u := Nat.min_le_left _ _
  have h2 : Nat.min u (A / u) ≤ A / u := Nat.min_le_right _ _
  have h3 : Nat.min u (A / u) * Nat.min u (A / u) ≤ u * (A / u) :=
    Nat.mul_le_mul h1 h2
  have h4 : u * (A / u) = A / u * u := Nat.mul_comm _ _
  rw [Nat.pow_two]
  omega

/-- `x * x ≤ A` implies `x ≤ Nat.sqrt A`. -/
theorem le_sqrt_of_sq_le {x A : Nat} (h : x * x ≤ A) : x ≤ Nat.sqrt A := by
  by_cases hle : x ≤ Nat.sqrt A
  · exact hle
  have h1 : Nat.sqrt A + 1 ≤ x := by omega
  have hmul : (Nat.sqrt A + 1) * (Nat.sqrt A + 1) ≤ x * x :=
    Nat.mul_le_mul h1 h1
  have hlt : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt A
  omega

/-- Nat-level initial estimate `2 ^ (log2 A / 2)`. -/
def R0nat (A : Nat) : Nat := 2 ^ (Nat.log2 A / 2)

/-- Nat-level Newton step `(R + A / R) / 2`. -/
def stepNat (A R : Nat) : Nat := (R + A / R) / 2

/-- Nat-level Newton iterates from `R0nat`. -/
def Rnat (A : Nat) : Nat → Nat
  | 0 => R0nat A
  | n + 1 => stepNat A (Rnat A n)

/-- `2 * S * R ≤ S * S + R * R` (AM-GM, via differences). -/
theorem two_mul_le_add_sq (S R : Nat) : 2 * S * R ≤ S * S + R * R := by
  by_cases h : R ≤ S
  · obtain ⟨d, hd⟩ : ∃ d, S = R + d := ⟨S - R, by omega⟩
    have e0 : 2 * S * R = S * R + S * R := by rw [Nat.mul_assoc, Nat.two_mul]
    have hmain : S * R + S * R + d * d = S * S + R * R := by
      rw [hd]
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
      ac_rfl
    rw [e0, ← hmain]; exact Nat.le_add_right _ _
  · obtain ⟨d, hd⟩ : ∃ d, R = S + d := ⟨R - S, by omega⟩
    have e0 : 2 * S * R = S * R + S * R := by rw [Nat.mul_assoc, Nat.two_mul]
    have hmain : S * R + S * R + d * d = S * S + R * R := by
      rw [hd]
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
      ac_rfl
    rw [e0, ← hmain]; exact Nat.le_add_right _ _

/-- The initial estimate is positive on positive inputs. -/
theorem R0nat_pos {A : Nat} (_ : 0 < A) : 0 < R0nat A := by
  unfold R0nat
  exact Nat.one_le_two_pow

/-- The initial estimate squared is below the input. -/
theorem R0nat_sq_le {A : Nat} (hA : A ≠ 0) : R0nat A * R0nat A ≤ A := by
  have hL : 2 ^ Nat.log2 A ≤ A := Nat.log2_self_le hA
  have h2 : Nat.log2 A / 2 + Nat.log2 A / 2 ≤ Nat.log2 A := by
    have := Nat.div_mul_le_self (Nat.log2 A) 2
    omega
  have e1 : R0nat A * R0nat A = 2 ^ (Nat.log2 A / 2 + Nat.log2 A / 2) := by
    unfold R0nat; rw [← Nat.pow_add]
  have h3 : 2 ^ (Nat.log2 A / 2 + Nat.log2 A / 2) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide) h2
  omega

/-- The initial estimate never exceeds the floor root. -/
theorem R0nat_le_sqrt {A : Nat} (hA : A ≠ 0) : R0nat A ≤ Nat.sqrt A :=
  le_sqrt_of_sq_le (R0nat_sq_le hA)

/-- The floor root is below twice the initial estimate. -/
theorem sqrt_succ_le_two_R0 {A : Nat} (hA : A ≠ 0) :
    Nat.sqrt A + 1 ≤ 2 * R0nat A := by
  by_cases h : Nat.sqrt A + 1 ≤ 2 * R0nat A
  · exact h
  have hle : 2 * R0nat A ≤ Nat.sqrt A := by omega
  have hSS : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
  have hsq : (2 * R0nat A) * (2 * R0nat A) ≤ A := by
    have := Nat.mul_le_mul hle hle
    omega
  have hA2 : A < 2 ^ (Nat.log2 A + 1) := Nat.lt_log2_self
  have hexp : Nat.log2 A + 1 ≤ 2 + (Nat.log2 A / 2 + Nat.log2 A / 2) := by omega
  have hpow : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ (2 + (Nat.log2 A / 2 + Nat.log2 A / 2)) :=
    Nat.pow_le_pow_right (by decide) hexp
  have e2 : (2 * R0nat A) * (2 * R0nat A) = 2 ^ (2 + (Nat.log2 A / 2 + Nat.log2 A / 2)) := by
    have e1 : R0nat A * R0nat A = 2 ^ (Nat.log2 A / 2 + Nat.log2 A / 2) := by
      unfold R0nat; rw [← Nat.pow_add]
    have c4 : (2 * R0nat A) * (2 * R0nat A) = (2 * 2) * (R0nat A * R0nat A) := by
      ac_rfl
    rw [c4, e1]
    have c42 : (2 * 2 : Nat) = 2 ^ 2 := by decide
    rw [c42, ← Nat.pow_add]
  omega

/-- One Newton step never goes below the floor root. -/
theorem step_ge_sqrt (A R : Nat) (hR : 0 < R) :
    Nat.sqrt A ≤ stepNat A R := by
  unfold stepNat
  have hSS : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
  have h2SR : 2 * (Nat.sqrt A * R) ≤ Nat.sqrt A * Nat.sqrt A + R * R := by
    have h := two_mul_le_add_sq (Nat.sqrt A) R
    have a1 : 2 * Nat.sqrt A * R = 2 * (Nat.sqrt A * R) := Nat.mul_assoc 2 _ _
    omega
  by_cases hbig : 2 * Nat.sqrt A ≤ R
  · have hle : 2 * Nat.sqrt A ≤ R + A / R :=
      Nat.le_trans hbig (Nat.le_add_right _ _)
    have harg : Nat.sqrt A * 2 ≤ R + A / R := by
      rw [Nat.mul_comm]; exact hle
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr harg
  · have hsmall : R < 2 * Nat.sqrt A := by omega
    have hRle : R ≤ 2 * Nat.sqrt A := Nat.le_of_lt hsmall
    have hRR : R * R ≤ 2 * (Nat.sqrt A * R) := by
      have h1 : R * R ≤ R * (2 * Nat.sqrt A) :=
        Nat.mul_le_mul (Nat.le_refl R) (Nat.le_of_lt hsmall)
      have a1 : R * (2 * Nat.sqrt A) = 2 * (Nat.sqrt A * R) := by ac_rfl
      rw [a1] at h1; exact h1
    have hsub : (2 * Nat.sqrt A - R) * R ≤ A := by
      have e : (2 * Nat.sqrt A - R) * R = 2 * Nat.sqrt A * R - R * R :=
        Nat.sub_mul _ _ _
      have a1 : 2 * Nat.sqrt A * R = 2 * (Nat.sqrt A * R) := Nat.mul_assoc 2 _ _
      have hstep : 2 * (Nat.sqrt A * R) - R * R ≤
          (Nat.sqrt A * Nat.sqrt A + R * R) - R * R :=
        Nat.sub_le_sub_right h2SR _
      have hcancel : Nat.sqrt A * Nat.sqrt A + R * R - R * R =
          Nat.sqrt A * Nat.sqrt A :=
        Nat.add_sub_cancel _ _
      have hle2 : 2 * (Nat.sqrt A * R) - R * R ≤ Nat.sqrt A * Nat.sqrt A := by
        rw [hcancel] at hstep; exact hstep
      have e' : (2 * Nat.sqrt A - R) * R = 2 * (Nat.sqrt A * R) - R * R := by
        rw [e, a1]
      rw [e']; exact Nat.le_trans hle2 hSS
    have hle : 2 * Nat.sqrt A - R ≤ A / R :=
      (Nat.le_div_iff_mul_le hR).mpr hsub
    have eadd : R + (2 * Nat.sqrt A - R) = 2 * Nat.sqrt A :=
      Nat.add_sub_cancel' hRle
    have hsum : 2 * Nat.sqrt A ≤ R + A / R := by
      have hcc : R + (2 * Nat.sqrt A - R) ≤ R + A / R :=
        Nat.add_le_add (Nat.le_refl R) hle
      rw [eadd] at hcc; exact hcc
    have harg : Nat.sqrt A * 2 ≤ R + A / R := by
      rw [Nat.mul_comm]; exact hsum
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr harg

/-- A Newton step strictly decreases while above the floor root. -/
theorem step_lt_of_above {A R : Nat} (hR : Nat.sqrt A + 1 ≤ R) :
    stepNat A R < R := by
  have hRpos : 0 < R := by omega
  have hSS1 : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt A
  have hRR : (Nat.sqrt A + 1) * (Nat.sqrt A + 1) ≤ R * R :=
    Nat.mul_le_mul hR hR
  have hAlt : A < R * R := by omega
  have hdiv : A / R < R := (Nat.div_lt_iff_lt_mul hRpos).mpr hAlt
  unfold stepNat
  omega

/-- Key Newton upper bound: `2 * R * next ≤ R * R + A`. -/
theorem newton_upper {A R : Nat} : 2 * R * stepNat A R ≤ R * R + A := by
  have hhalf : 2 * stepNat A R ≤ R + A / R := by
    unfold stepNat; omega
  have hmul : R * (2 * stepNat A R) ≤ R * (R + A / R) :=
    Nat.mul_le_mul (Nat.le_refl R) hhalf
  have hle : A / R * R ≤ A := Nat.div_mul_le_self A R
  have e : R * (R + A / R) = R * R + A / R * R := by
    rw [Nat.mul_add, Nat.mul_comm R (A / R)]
  have a1 : 2 * R * stepNat A R = R * (2 * stepNat A R) := by ac_rfl
  omega

theorem not_le_succ {a b : Nat} (h : ¬ a ≤ b) : b + 1 ≤ a := by omega

theorem add_one_le_of_lt_simple {a b : Nat} (h : a < b) : a + 1 ≤ b := by omega

theorem sq_succ_expand (S : Nat) : (S + 1) * (S + 1) = S * S + (S + S) + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  ac_rfl

theorem sqrt_sq_add_le {A : Nat} :
    A ≤ Nat.sqrt A * Nat.sqrt A + (Nat.sqrt A + Nat.sqrt A) := by
  have h := Nat.lt_succ_sqrt A
  have e := sq_succ_expand (Nat.sqrt A)
  have h2 : A < Nat.sqrt A * Nat.sqrt A + (Nat.sqrt A + Nat.sqrt A) + 1 := by
    rw [← e]; exact h
  exact Nat.le_of_lt_add_one h2

/-- Quadratic contraction: one Newton step from above lands within `E^2 / (2R) + 1`. -/
theorem quad_step {A R : Nat} (hA : 0 < A) (hR : 0 < R)
    (hRS : Nat.sqrt A ≤ R) :
    stepNat A R ≤ Nat.sqrt A + (R - Nat.sqrt A) * (R - Nat.sqrt A) / (2 * R) + 1 := by
  obtain ⟨E, hd⟩ : ∃ E, R = Nat.sqrt A + E := Nat.exists_eq_add_of_le hRS
  have h1A : 1 ≤ A := hA
  have h11 : 1 * 1 ≤ A := by rw [Nat.mul_one]; exact h1A
  have hS1 : 1 ≤ Nat.sqrt A := le_sqrt_of_sq_le h11
  have hRs : R - Nat.sqrt A = E := by
    rw [hd]; exact Nat.add_sub_cancel_left _ _
  rw [hRs]
  generalize hQ : E * E / (2 * R) = Q
  by_cases hN : stepNat A R ≤ Nat.sqrt A + Q + 1
  · exact hN
  · have hN2 : Nat.sqrt A + Q + 1 + 1 ≤ stepNat A R := not_le_succ hN
    have hA2 := sqrt_sq_add_le (A := A)
    have hnew := newton_upper (A := A) (R := R)
    have hmul : 2 * R * (Nat.sqrt A + Q + 1 + 1) ≤ 2 * R * stepNat A R :=
      Nat.mul_le_mul (Nat.le_refl _) hN2
    have hle1 : R * R + A
        ≤ R * R + (Nat.sqrt A * Nat.sqrt A + (Nat.sqrt A + Nat.sqrt A)) :=
      Nat.add_le_add_left hA2 _
    have hle2 : 2 * R * (Nat.sqrt A + Q + 1 + 1)
        ≤ R * R + (Nat.sqrt A * Nat.sqrt A + (Nat.sqrt A + Nat.sqrt A)) :=
      Nat.le_trans (Nat.le_trans hmul hnew) hle1
    have h2R : 0 < 2 * R := Nat.mul_pos (by decide) hR
    have hdm : (2 * R) * Q + E * E % (2 * R) = E * E := by
      rw [← hQ]; exact Nat.div_add_mod _ _
    have hmod : E * E % (2 * R) < 2 * R := Nat.mod_lt _ h2R
    have hgt : R * R + (Nat.sqrt A * Nat.sqrt A + (Nat.sqrt A + Nat.sqrt A))
        < 2 * R * (Nat.sqrt A + Q + 1 + 1) := by
      subst hd
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_one, Nat.one_mul] at hdm hmod ⊢
      clear hN hN2 hA2 hnew hmul hle1 hle2 hQ hRS hR hA hS1 hRs h11 h1A h2R
      have b1 : Nat.sqrt A * (Nat.sqrt A * 2) = 2 * (Nat.sqrt A * Nat.sqrt A) := by
        ac_rfl
      have b2 : Nat.sqrt A * (E * 2) = 2 * (Nat.sqrt A * E) := by ac_rfl
      have b3 : E * Nat.sqrt A = Nat.sqrt A * E := Nat.mul_comm _ _
      omega
    have hcontra : 2 * R * (Nat.sqrt A + Q + 1 + 1)
        < 2 * R * (Nat.sqrt A + Q + 1 + 1) :=
      Nat.lt_of_le_of_lt hle2 hgt
    exact absurd hcontra (Nat.lt_irrefl _)

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  unfold sqrt newtonSqrt
  by_cases ha : a = 0
  · subst ha; simp
  · rw [ite_eq_right ha]
    have hmin : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
      (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat =
      Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
        (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) := by
      rw [toNat_min, BitVec.toNat_udiv]
    rw [hmin, ← Nat.pow_two]
    exact min_sq_le _ _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := ⟨7, Nat.le_refl 7, fun a => rfl⟩

end OzSqrt

import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
/-!
Port of the code the Vyper compiler v0.4.0 (commit e9db8d9f7486eae38f5b86531629019ad28f514e)
inlines for the builtin `sqrt(d: decimal) -> decimal`, `vyper/builtins/functions.py`, class
`Sqrt` (lines 2117 to 2172):

```
assert x >= 0.0
z: decimal = 0.0

if x == 0.0:
    z = 0.0
else:
    z = x / 2.0 + 0.5
    y: decimal = x

    for i: uint256 in range(256):
        if z == y:
            break
        y = z
        z = (x / z + z) / 2.0
```

The result is `z`. The decimal operations and the loop are the protected `ddiv`, `dadd` and
`loop` of `VyperSqrt/Spec.lean`.
-/
namespace VyperSqrt

/-- The deployed loop followed by the choice of the smaller of the last two iterates
(the fix of Vyper pull request 4486). -/
def sqrt : SqrtFn := vyperSqrtWith fun y z => if y < z then y else z

open ProofForgeFin.Sqrt

/-- The scaled radicand fits below `2 ^ 202`. -/
theorem A_lt (a : Nat) (h : a ≤ 2 ^ 167 - 1) : a * 10 ^ 10 < 2 ^ 202 := by
  have e1 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 := Nat.mul_le_mul_right _ h
  have e2 : (2 ^ 167 - 1) * 10 ^ 10 < 2 ^ 202 := by decide
  exact Nat.lt_of_le_of_lt e1 e2

/-- The root is below `2 ^ 101`. -/
theorem s_lt (a : Nat) (h : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (a * 10 ^ 10) < 2 ^ 101 := by
  apply sqrt_lt_two_pow (k := 101)
  rw [show (2 : Nat) * 101 = 202 from rfl]
  exact A_lt a h

/-- The root of a positive input is positive. -/
theorem s_pos (a : Nat) (ha : 0 < a) : 0 < Nat.sqrt (a * 10 ^ 10) := by
  apply le_sqrt_of_mul_self_le (m := 1)
  exact Nat.mul_le_mul ha (by decide : (1 : Nat) ≤ 10 ^ 10)

/-- The root of a positive input is at least `10 ^ 5`. -/
theorem s_1e5 (a : Nat) (ha : 0 < a) : 10 ^ 5 ≤ Nat.sqrt (a * 10 ^ 10) := by
  apply le_sqrt_of_mul_self_le (m := 10 ^ 5)
  have h1 : (1 : Nat) ≤ a := ha
  have h2 : (10 ^ 5) * (10 ^ 5) ≤ 1 * 10 ^ 10 := by decide
  have h3 : (1 : Nat) * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ h1
  exact Nat.le_trans h2 h3

/-- The seed `a / 2 + 5 * 10 ^ 9` is at least the root. -/
theorem seed_ge_sqrt (a : Nat) (ha : 0 < a) :
    Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := by
  have hmod : a ≤ 2 * (a / 2) + 1 := by omega
  have e1 : a * 10 ^ 10 ≤ (2 * (a / 2) + 1) * 10 ^ 10 := Nat.mul_le_mul_right _ hmod
  have dC : 5 * 10 ^ 9 = 5000000000 := by decide
  have dD : (10 : Nat) ^ 10 = 10000000000 := by decide
  rw [dD] at e1 ⊢
  rw [dC] at ⊢
  have e1e : (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1)
      = (a / 2 + 5000000000) * (a / 2 + 5000000000)
        + 2 * (a / 2 + 5000000000) + 1 := by grind
  have e2e : (a / 2 + 5000000000) * (a / 2 + 5000000000)
      = (a / 2) * (a / 2) + 10000000000 * (a / 2) + 25000000000000000000 := by grind
  have hsq := four_mul_le_sq (a / 2) 5000000000
  rw [e2e] at hsq
  have hA : a * 10000000000 < (a / 2 + 5000000000 + 1) * (a / 2 + 5000000000 + 1) := by
    rw [e1e, e2e]
    omega
  have hlt : Nat.sqrt (a * 10000000000) < a / 2 + 5000000000 + 1 :=
    sqrt_lt_of_lt_mul_self hA
  have hback : a / 2 + 5000000000 = a / 2 + 5 * 10 ^ 9 := by rw [dC]
  omega

/-- Above the root, the floored quotient stays below the root. -/
theorem frac_le_s {A y : Nat} (hy : Nat.sqrt A + 1 ≤ y) (hypos : 0 < y) :
    A / y ≤ Nat.sqrt A := by
  rcases Nat.le_total (A / y) (Nat.sqrt A) with h | h
  · exact h
  · by_cases heq : Nat.sqrt A = A / y
    · omega
    · have hc' : Nat.sqrt A + 1 ≤ A / y := by omega
      have h1 : (Nat.sqrt A + 1) * y ≤ A := (Nat.le_div_iff_mul_le hypos).mp hc'
      have h2 : (Nat.sqrt A + 1) * (Nat.sqrt A + 1) ≤ (Nat.sqrt A + 1) * y :=
        Nat.mul_le_mul_left _ hy
      have h3 : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt _
      exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans h2 h1) h3) (Nat.lt_irrefl _)

/-- At the root, the floored quotient exceeds the root by at most two. -/
theorem frac_le_at {A : Nat} (hA1 : 1 ≤ A) :
    A / Nat.sqrt A ≤ Nat.sqrt A + 2 := by
  have hs : 0 < Nat.sqrt A := by
    apply le_sqrt_of_mul_self_le (m := 1)
    have : (1 : Nat) * 1 ≤ A := by omega
    exact this
  have h3 : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt _
  have hexp : (Nat.sqrt A + 1) * (Nat.sqrt A + 1)
      = Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A + 1 := by grind
  have hA : A ≤ Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A := by omega
  have hexp2 : (Nat.sqrt A + 3) * Nat.sqrt A
      = Nat.sqrt A * Nat.sqrt A + 3 * Nat.sqrt A := Nat.add_mul _ _ _
  rcases Nat.le_total (A / Nat.sqrt A) (Nat.sqrt A + 2) with h | h
  · exact h
  · by_cases heq : Nat.sqrt A + 2 = A / Nat.sqrt A
    · omega
    · have hc' : Nat.sqrt A + 3 ≤ A / Nat.sqrt A := by omega
      have h1 : (Nat.sqrt A + 3) * Nat.sqrt A ≤ A := (Nat.le_div_iff_mul_le hs).mp hc'
      have hle : (Nat.sqrt A + 3) * Nat.sqrt A
          ≤ Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A := Nat.le_trans h1 hA
      have hlt2 : Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A
          < (Nat.sqrt A + 3) * Nat.sqrt A := by omega
      have hfin : (Nat.sqrt A + 3) * Nat.sqrt A < (Nat.sqrt A + 3) * Nat.sqrt A :=
        Nat.lt_of_le_of_lt hle hlt2
      exact absurd hfin (Nat.lt_irrefl _)

/-- One loop iteration is one Newton step. -/
theorem step_newton (a y : Nat) :
    (a * 10 ^ 10 / y + y) / 2 = newton (a * 10 ^ 10) y := by
  unfold newton
  rw [Nat.add_comm (a * 10 ^ 10 / y) y]

/-- The Newton step stays above the root. -/
theorem newton_ge_s {a y : Nat} (hypos : 0 < y) :
    Nat.sqrt (a * 10 ^ 10) ≤ (a * 10 ^ 10 / y + y) / 2 := by
  rw [step_newton]
  exact sqrt_le_newton hypos

/-- Helper: trichotomy on naturals (moved up: used by the lemmas below). -/
theorem lt_or_ge_helper2 (m n : Nat) : m < n ∨ n ≤ m := by
  by_cases h : m < n
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- The Newton step stays below `seed + 1`. -/
theorem newton_le_seed1 {a y : Nat} (ha : 0 < a)
    (hylo : Nat.sqrt (a * 10 ^ 10) ≤ y) (hyhi : y ≤ a / 2 + 5 * 10 ^ 9 + 1) :
    (a * 10 ^ 10 / y + y) / 2 ≤ a / 2 + 5 * 10 ^ 9 + 1 := by
  have hseed : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := seed_ge_sqrt a ha
  have eN := step_newton a y
  rcases lt_or_ge_helper2 y (Nat.sqrt (a * 10 ^ 10) + 1) with hcase | hcase
  · have hy_eq : y = Nat.sqrt (a * 10 ^ 10) := by omega
    subst hy_eq
    have hm := newton_of_mem (a := a * 10 ^ 10) (x := Nat.sqrt (a * 10 ^ 10))
      (s_pos a ha) (Nat.le_refl _) (by omega : Nat.sqrt (a * 10 ^ 10) ≤ Nat.sqrt (a * 10 ^ 10) + 1)
    rcases hm with h | ⟨_, h, _⟩
    · omega
    · omega
  · have hlt : Nat.sqrt (a * 10 ^ 10) < y := by omega
    have hN := newton_lt_self (a := a * 10 ^ 10) (x := y) hlt
    omega

/-- Every iterate the loop can step from satisfies the range condition. -/
theorem step_bound {a y : Nat} (ha : 0 < a) (hM : a ≤ 2 ^ 167 - 1)
    (hylo : Nat.sqrt (a * 10 ^ 10) ≤ y) (hyhi : y ≤ a / 2 + 5 * 10 ^ 9 + 1)
    (hypos : 0 < y) :
    a * 10 ^ 10 / y + y ≤ 2 ^ 167 - 1 := by
  have hsB : Nat.sqrt (a * 10 ^ 10) < 2 ^ 101 := s_lt a hM
  have hA1 : 1 ≤ a * 10 ^ 10 :=
    Nat.le_trans (by decide : (1 : Nat) ≤ 1 * 10 ^ 10) (Nat.mul_le_mul_right _ ha)
  generalize (a * 10 ^ 10) = A at hylo hsB hA1 ⊢
  rcases lt_or_ge_helper2 y (Nat.sqrt A + 1) with hcase | hcase
  · have hy_eq : y = Nat.sqrt A := by omega
    subst hy_eq
    have hfr := frac_le_at (A := A) hA1
    have hclosed : 2 * 2 ^ 101 ≤ 2 ^ 167 - 1 := by decide
    omega
  · have hfr := frac_le_s hcase hypos
    have hclosed : ((2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 1) + 2 ^ 101 ≤ 2 ^ 167 - 1 := by
      decide
    omega

/-- From an iterate above the root within the error bound, the loop ends at the root. -/
theorem loop_pair_min_aux {a : Nat} (ha : 0 < a) (hM : a ≤ 2 ^ 167 - 1) (n : Nat) :
    ∀ y : Nat, Nat.sqrt (a * 10 ^ 10) ≤ y → y ≤ a / 2 + 5 * 10 ^ 9 + 1 → 0 < y →
      y - Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ n + 1 →
      ∃ Y Z : Nat, loop (a : Int) (n + 1) (y : Int)
        (((a * 10 ^ 10 / y + y) / 2 : Nat) : Int)
        = some (((Y : Nat) : Int), ((Z : Nat) : Int))
        ∧ min Y Z = Nat.sqrt (a * 10 ^ 10) := by
  induction n with
  | zero =>
    intro y hylo hyhi hypos herr
    have hN1 : Nat.sqrt (a * 10 ^ 10) ≤ (a * 10 ^ 10 / y + y) / 2 :=
      newton_ge_s hypos
    have hNhi : (a * 10 ^ 10 / y + y) / 2 ≤ a / 2 + 5 * 10 ^ 9 + 1 :=
      newton_le_seed1 ha hylo hyhi
    have hNpos : 0 < (a * 10 ^ 10 / y + y) / 2 := by
      have hsp := s_pos a ha
      omega
    have hsb := step_bound ha hM hN1 hNhi hNpos
    have eN := step_newton a y
    have herr2 : y - Nat.sqrt (a * 10 ^ 10) ≤ 2 := herr
    by_cases heq : (a * 10 ^ 10 / y + y) / 2 = y
    · have heqN : newton (a * 10 ^ 10) y = y := eN ▸ heq
      have hys : y = Nat.sqrt (a * 10 ^ 10) :=
        eq_sqrt_of_newton_eq_self hypos heqN
      subst hys
      have hcast : ((((a * 10 ^ 10 / Nat.sqrt (a * 10 ^ 10)
          + Nat.sqrt (a * 10 ^ 10)) / 2 : Nat)) : Int)
          = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := congrArg _ heq
      exact ⟨Nat.sqrt (a * 10 ^ 10), Nat.sqrt (a * 10 ^ 10),
        by rw [hcast, loop_stop], by omega⟩
    · rw [loop_step 0 hNpos heq hsb]
      have hy3 : y = Nat.sqrt (a * 10 ^ 10) ∨ y = Nat.sqrt (a * 10 ^ 10) + 1
          ∨ y = Nat.sqrt (a * 10 ^ 10) + 2 := by omega
      have hNmem : (a * 10 ^ 10 / y + y) / 2 = Nat.sqrt (a * 10 ^ 10)
          ∨ (a * 10 ^ 10 / y + y) / 2 = Nat.sqrt (a * 10 ^ 10) + 1 := by
        rcases hy3 with hyeq | hyeq | hyeq
        · subst hyeq
          have hm := newton_of_mem (a := a * 10 ^ 10) (x := Nat.sqrt (a * 10 ^ 10))
            (s_pos a ha) (Nat.le_refl _)
            (by omega : Nat.sqrt (a * 10 ^ 10) ≤ Nat.sqrt (a * 10 ^ 10) + 1)
          rcases hm with h | ⟨_, h, _⟩
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        · subst hyeq
          have hm := newton_of_mem (a := a * 10 ^ 10)
            (x := Nat.sqrt (a * 10 ^ 10) + 1)
            (by omega : 0 < Nat.sqrt (a * 10 ^ 10) + 1)
            (by omega : Nat.sqrt (a * 10 ^ 10) ≤ Nat.sqrt (a * 10 ^ 10) + 1)
            (Nat.le_refl _)
          rcases hm with h | ⟨hcon, _, _⟩
          · exact Or.inl (by omega)
          · omega
        · subst hyeq
          have h4 : (Nat.sqrt (a * 10 ^ 10) + 2 - Nat.sqrt (a * 10 ^ 10))
              * (Nat.sqrt (a * 10 ^ 10) + 2 - Nat.sqrt (a * 10 ^ 10))
              ≤ Nat.sqrt (a * 10 ^ 10) := by
            have hs5 := s_1e5 a ha
            have e2 : Nat.sqrt (a * 10 ^ 10) + 2 - Nat.sqrt (a * 10 ^ 10) = 2 := by
              omega
            rw [e2]
            omega
          have hm := newton_eq_or_succ (a := a * 10 ^ 10)
            (x := Nat.sqrt (a * 10 ^ 10) + 2) hypos hylo h4
          rcases hm with h | ⟨h, _⟩
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      have hfin : min ((a * 10 ^ 10 / y + y) / 2)
          ((a * 10 ^ 10 / ((a * 10 ^ 10 / y + y) / 2)
            + (a * 10 ^ 10 / y + y) / 2) / 2)
          = Nat.sqrt (a * 10 ^ 10) := by
        have eN' := step_newton a ((a * 10 ^ 10 / y + y) / 2)
        rw [eN']
        exact min_newton_eq_sqrt hNpos hN1 (by omega)
      exact ⟨(a * 10 ^ 10 / y + y) / 2,
        (a * 10 ^ 10 / ((a * 10 ^ 10 / y + y) / 2)
          + (a * 10 ^ 10 / y + y) / 2) / 2,
        rfl, hfin⟩
  | succ n ih =>
    intro y hylo hyhi hypos herr
    have hN1 : Nat.sqrt (a * 10 ^ 10) ≤ (a * 10 ^ 10 / y + y) / 2 :=
      newton_ge_s hypos
    have hNhi : (a * 10 ^ 10 / y + y) / 2 ≤ a / 2 + 5 * 10 ^ 9 + 1 :=
      newton_le_seed1 ha hylo hyhi
    have hNpos : 0 < (a * 10 ^ 10 / y + y) / 2 := by
      have hsp := s_pos a ha
      omega
    have hsb := step_bound ha hM hN1 hNhi hNpos
    have eN := step_newton a y
    have e2n : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    by_cases heq : (a * 10 ^ 10 / y + y) / 2 = y
    · have heqN : newton (a * 10 ^ 10) y = y := eN ▸ heq
      have hys : y = Nat.sqrt (a * 10 ^ 10) :=
        eq_sqrt_of_newton_eq_self hypos heqN
      subst hys
      have hcast : ((((a * 10 ^ 10 / Nat.sqrt (a * 10 ^ 10)
          + Nat.sqrt (a * 10 ^ 10)) / 2 : Nat)) : Int)
          = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := congrArg _ heq
      exact ⟨Nat.sqrt (a * 10 ^ 10), Nat.sqrt (a * 10 ^ 10),
        by rw [hcast, loop_stop], by omega⟩
    · rw [loop_step (n + 1) hNpos heq hsb]
      have hhalf := newton_sub_sqrt_le_half (a := a * 10 ^ 10) (x := y) hypos hylo
      have herr' : (a * 10 ^ 10 / y + y) / 2 - Nat.sqrt (a * 10 ^ 10)
          ≤ 2 ^ n + 1 := by omega
      obtain ⟨Y, Z, hloop, hmin⟩ :=
        ih ((a * 10 ^ 10 / y + y) / 2) hN1 hNhi hNpos herr'
      exact ⟨Y, Z, hloop, hmin⟩

/-- Helper: every natural is below its successor (kept separate so `omega` runs clean). -/
theorem le_succ_self (m : Nat) : m ≤ m + 1 := by omega

/-- The seed error fits the fuel bound (kept separate so `omega` runs clean). -/
theorem seed_err_le {a : Nat} (hM : a ≤ 2 ^ 167 - 1) :
    a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ 254 + 1 := by
  have hbig : (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 ≤ 2 ^ 254 := by decide
  omega

/-- The full 256-iteration loop ends at the root. -/
theorem sqrt_loop_min {a : Nat} (ha : 0 < a) (hM : a ≤ 2 ^ 167 - 1) :
    ∃ Y Z : Nat, loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)
      = some (((Y : Nat) : Int), ((Z : Nat) : Int))
      ∧ min Y Z = Nat.sqrt (a * 10 ^ 10) := by
  by_cases heq0 : a / 2 + 5 * 10 ^ 9 = a
  · have hcast : ((((a / 2 + 5 * 10 ^ 9 : Nat))) : Int) = ((a : Nat) : Int) :=
      congrArg _ heq0
    have ha10 : a = 10 * 10 ^ 9 ∨ a = 10 * 10 ^ 9 - 1 := by omega
    have e256 : (256 : Nat) = 255 + 1 := rfl
    rw [hcast, e256, loop_stop]
    refine ⟨a, a, rfl, ?_⟩
    rcases ha10 with h10 | h10
    · subst h10
      have hsa : Nat.sqrt ((10 * 10 ^ 9) * 10 ^ 10) = 10 * 10 ^ 9 :=
        sqrt_eq_of_bounds (by decide) (by decide)
      rw [hsa]
      omega
    · subst h10
      have hsa : Nat.sqrt ((10 * 10 ^ 9 - 1) * 10 ^ 10) = 10 * 10 ^ 9 - 1 :=
        sqrt_eq_of_bounds (by decide) (by decide)
      rw [hsa]
      omega
  · have hne : ((((a / 2 + 5 * 10 ^ 9 : Nat))) : Int) ≠ ((a : Nat) : Int) :=
      fun c => heq0 (Int.ofNat.inj c)
    have h5 : (0 : Nat) < 5 * 10 ^ 9 := by decide
    have hpos : 0 < a / 2 + 5 * 10 ^ 9 := by omega
    have hsb0 := step_bound (a := a) (y := a / 2 + 5 * 10 ^ 9) ha hM
      (seed_ge_sqrt a ha) (le_succ_self _) hpos
    have hloop1 : loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)
        = loop (a : Int) 255 (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int)
          (((a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9)
            + (a / 2 + 5 * 10 ^ 9)) / 2 : Nat) : Int) := by
      rw [show (256 : Nat) = 255 + 1 from rfl]
      exact loop_step 255 hpos heq0 hsb0
    rw [hloop1]
    have herr0 := seed_err_le (a := a) hM
    have e255 : (255 : Nat) = 254 + 1 := rfl
    rw [e255]
    exact loop_pair_min_aux ha hM 254 (a / 2 + 5 * 10 ^ 9)
      (seed_ge_sqrt a ha) (le_succ_self _) hpos herr0

/-- Non-negative decimals are casts of naturals bounded by `2 ^ 167 - 1`. -/
theorem toNat_isDecimal {x : Int} (hx : IsDecimal x) (hx0 : 0 ≤ x) :
    ∃ a : Nat, x = ((a : Nat) : Int) ∧ a ≤ 2 ^ 167 - 1 := by
  refine ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm, ?_⟩
  have h2 := hx.2
  rw [max_decimal_eq, ← Int.toNat_of_nonneg hx0] at h2
  exact Int.ofNat_le.mp h2

/-- On a positive decimal, `sqrt` returns the cast of the integer root. -/
theorem sqrt_pos_result {a : Nat} (ha : 0 < a) (hM : a ≤ 2 ^ 167 - 1) :
    sqrt ((a : Nat) : Int)
      = some (((Nat.sqrt (a * 10 ^ 10) : Nat)) : Int) := by
  have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha hM
  obtain ⟨Y, Z, hloop, hmin⟩ := sqrt_loop_min ha hM
  unfold sqrt
  rw [hpos, hloop, Option.map_some]
  show some (if ((Y : Nat) : Int) < ((Z : Nat) : Int) then ((Y : Nat) : Int)
    else ((Z : Nat) : Int))
    = some (((Nat.sqrt (a * 10 ^ 10) : Nat)) : Int)
  rcases lt_or_ge_helper2 Y Z with hlt | hge
  · have hYI : ((Y : Nat) : Int) = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
      omega
    rw [if_pos (Int.ofNat_lt.mpr hlt), hYI]
  · have hZI : ((Z : Nat) : Int) = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
      omega
    rw [if_neg (fun h => absurd (Int.ofNat_lt.mp h) (by omega)), hZI]

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := by
  intro x r hx hxr
  by_cases hneg : x < 0
  · have hnone : sqrt x = none := by unfold sqrt vyperSqrtWith; rw [if_pos hneg]
    rw [hnone] at hxr
    cases hxr
  · have hx0 : 0 ≤ x := by omega
    obtain ⟨a, rfl, hM⟩ := toNat_isDecimal hx hx0
    by_cases ha0 : a = 0
    · subst ha0
      have h0 : sqrt 0 = some 0 := by decide
      have hxr' : sqrt 0 = some r := hxr
      rw [h0] at hxr'
      have hr : r = 0 := (Option.some_inj.mp hxr').symm
      subst hr
      simp
    · have ha : 0 < a := Nat.pos_of_ne_zero ha0
      rw [sqrt_pos_result ha hM] at hxr
      have hr : r = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) :=
        (Option.some_inj.mp hxr).symm
      subst hr
      have hle : Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) ≤ a * 10 ^ 10 :=
        Nat.sqrt_le _
      have hleI : ((Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) : Nat) : Int)
          ≤ ((a * 10 ^ 10 : Nat) : Int) := Int.ofNat_le.mpr hle
      have e1 : ((Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) : Nat) : Int)
          = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int)
            * ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by simp
      have e2 : ((a * 10 ^ 10 : Nat) : Int)
          = ((a : Nat) : Int) * DIVISOR := by rw [divisor_eq]; simp
      rw [e1, e2] at hleI
      exact hleI

theorem req_sqrt_not_below   : SqrtNotBelow sqrt := by
  intro x r hx hxr
  by_cases hneg : x < 0
  · have hnone : sqrt x = none := by unfold sqrt vyperSqrtWith; rw [if_pos hneg]
    rw [hnone] at hxr
    cases hxr
  · have hx0 : 0 ≤ x := by omega
    obtain ⟨a, rfl, hM⟩ := toNat_isDecimal hx hx0
    by_cases ha0 : a = 0
    · subst ha0
      have h0 : sqrt 0 = some 0 := by decide
      have hxr' : sqrt 0 = some r := hxr
      rw [h0] at hxr'
      have hr : r = 0 := (Option.some_inj.mp hxr').symm
      subst hr
      simp
    · have ha : 0 < a := Nat.pos_of_ne_zero ha0
      rw [sqrt_pos_result ha hM] at hxr
      have hr : r = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) :=
        (Option.some_inj.mp hxr).symm
      subst hr
      have hlt : a * 10 ^ 10
          < (Nat.sqrt (a * 10 ^ 10) + 1) * (Nat.sqrt (a * 10 ^ 10) + 1) :=
        Nat.lt_succ_sqrt _
      have hltI : ((a * 10 ^ 10 : Nat) : Int)
          < (((Nat.sqrt (a * 10 ^ 10) + 1) * (Nat.sqrt (a * 10 ^ 10) + 1) : Nat) : Int) :=
        Int.ofNat_lt.mpr hlt
      have e2 : ((a * 10 ^ 10 : Nat) : Int)
          = ((a : Nat) : Int) * DIVISOR := by rw [divisor_eq]; simp
      have e3 : (((Nat.sqrt (a * 10 ^ 10) + 1) * (Nat.sqrt (a * 10 ^ 10) + 1) : Nat) : Int)
          = (((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) + 1)
            * (((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) + 1) := by simp
      rw [e2, e3] at hltI
      exact hltI

theorem req_sqrt_total       : SqrtTotal sqrt := by
  intro x hx hx0
  obtain ⟨a, rfl, hM⟩ := toNat_isDecimal hx hx0
  by_cases ha0 : a = 0
  · subst ha0
    show (sqrt 0).isSome
    unfold sqrt vyperSqrtWith
    rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]
    rfl
  · have ha : 0 < a := Nat.pos_of_ne_zero ha0
    rw [sqrt_pos_result ha hM]
    rfl

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop    : DeployedLoop sqrt :=
  ⟨fun y z => if y < z then y else z, fun x => rfl⟩

end VyperSqrt

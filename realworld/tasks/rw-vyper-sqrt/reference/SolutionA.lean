import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
/-!
# Reference solution A (build team; hidden from agents)

Port of the code Vyper v0.4.1 inlines for `sqrt(d: decimal)`: the v0.4.0 loop followed by the
lines pull request 4486 added (merge commit 2ffc8b3db8b7e32257a72560fa89e7dcf81b5384,
`vyper/builtins/functions.py`):

```
    if y < z:
        z = y
```

The proof works on natural numbers: with `N = x * 10^10` and `s = Nat.sqrt N`, one iteration of
the loop from a positive iterate is the Newton step `(z + N / z) / 2` (`loop_step`, `step_eq`).
From the seed, an error of at most `2^m + 2` above the root at most halves with every step
(`ProofForgeFin.Sqrt.newton_sub_sqrt_le_half`, `phase_far`); once the error is at most 3, one
step reaches the root or the root plus one (`newton_le_sqrt_add_one`, `phase_near`), and from
there the iterates stay at the root or alternate with the root plus one (`newton_of_mem`,
`phase_end`), so the smaller of the last two iterates is the root
(`min_newton_eq_sqrt`). The loop stops early only at a fixed point, which is the root
(`eq_sqrt_of_newton_eq_self`). The seed is below `2^166 + 2^40`, so 170 of the 256 iterations
suffice; no operation leaves the range of `decimal` (`body_fits`).
-/
namespace VyperSqrt

open ProofForgeFin.Sqrt (newton)

def sqrt : SqrtFn := fun x =>
  if x < 0 then none
  else if x = 0 then some 0
  else
    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
      (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2

theorem req_deployed_loop : DeployedLoop sqrt := ⟨fun y z => if y < z then y else z, fun _ => rfl⟩

/-! ## The loop on natural numbers -/

section
variable (a : Nat)

/-- The loop's result is the root: the smaller of the last two iterates is `Nat.sqrt (a * 10^10)`. -/
def Res (r : Option (Int × Int)) : Prop :=
  ∃ y z : Nat, r = some ((y : Int), (z : Int)) ∧ min y z = Nat.sqrt (a * 10 ^ 10)

/-- The loop body's step is the Newton step. -/
theorem step_eq (z : Nat) : (a * 10 ^ 10 / z + z) / 2 = newton (a * 10 ^ 10) z := by
  unfold newton; rw [Nat.add_comm]

/-- Facts about the root of `a * 10^10` for a positive decimal `a`. -/
theorem root_bounds (ha : 0 < a) (h : a ≤ 2 ^ 167 - 1) :
    10 ^ 5 ≤ Nat.sqrt (a * 10 ^ 10) ∧ Nat.sqrt (a * 10 ^ 10) < 2 ^ 101 := by
  constructor
  · apply ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le
    have : 1 * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha
    exact Nat.le_trans (by decide) this
  · apply ProofForgeFin.Sqrt.sqrt_lt_two_pow (k := 101)
    have h1 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 := Nat.mul_le_mul_right _ h
    exact Nat.lt_of_le_of_lt h1 (by decide)

/-- Above the root and below `2^166`, the body of the loop stays in range. -/
theorem body_fits (ha : 0 < a) (h : a ≤ 2 ^ 167 - 1) {z : Nat} (h1 : Nat.sqrt (a * 10 ^ 10) ≤ z)
    (h2 : z ≤ 2 ^ 166 + 2 ^ 40) : a * 10 ^ 10 / z + z ≤ 2 ^ 167 - 1 := by
  obtain ⟨hs5, hs⟩ := root_bounds a ha h
  have hlt := Nat.lt_succ_sqrt (a * 10 ^ 10)
  generalize Nat.sqrt (a * 10 ^ 10) = s at *
  generalize a * 10 ^ 10 = N at *
  have hspos : 0 < s := by omega
  have hdiv : N / z ≤ N / s := Nat.div_le_div_left h1 hspos
  have hdiv2 : N / s < s + 3 := by
    apply (Nat.div_lt_iff_lt_mul hspos).mpr
    simp only [Nat.succ_eq_add_one] at hlt
    grind
  have e : 2 ^ 101 + 3 + (2 ^ 166 + 2 ^ 40) ≤ 2 ^ 167 - 1 := by decide
  generalize (2 : Nat) ^ 101 = P at *
  generalize (2 : Nat) ^ 166 + 2 ^ 40 = Q at *
  generalize (2 : Nat) ^ 167 - 1 = M at *
  omega

/-- Phase 3: from an iterate at the root or the root plus one, the loop ends at the root. -/
theorem phase_end (ha : 0 < a) (h : a ≤ 2 ^ 167 - 1) :
    ∀ n y z, Nat.sqrt (a * 10 ^ 10) ≤ y → y ≤ Nat.sqrt (a * 10 ^ 10) + 1 →
      z = newton (a * 10 ^ 10) y → Res a (loop (a : Int) n (y : Int) (z : Int)) := by
  obtain ⟨hs5, hs⟩ := root_bounds a ha h
  intro n
  induction n with
  | zero =>
    intro y z h1 h2 hz
    refine ⟨y, z, rfl, ?_⟩
    rw [hz]; exact ProofForgeFin.Sqrt.min_newton_eq_sqrt (by omega) h1 h2
  | succ k ih =>
    intro y z h1 h2 hz
    by_cases hzy : z = y
    · subst hzy
      have hy := ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self (by omega) hz.symm
      refine ⟨z, z, loop_stop _ _ _, ?_⟩
      rw [Nat.min_self]; exact hy
    · have hm := ProofForgeFin.Sqrt.newton_of_mem (a := a * 10 ^ 10) (x := y) (by omega) h1 h2
      have hn := ProofForgeFin.Sqrt.sqrt_le_newton (a := a * 10 ^ 10) (x := y) (by omega)
      rw [← hz] at hm hn
      have hz1 : z ≤ Nat.sqrt (a * 10 ^ 10) + 1 := by omega
      rewrite [loop_step k (by omega) hzy (body_fits a ha h hn (by omega)), step_eq]
      exact ih z _ hn hz1 rfl

/-- Phase 2: one step from an iterate within `2 * s` of the root squared reaches phase 3. -/
theorem phase_near (ha : 0 < a) (h : a ≤ 2 ^ 167 - 1) :
    ∀ n y z, 0 < y → z = newton (a * 10 ^ 10) y → Nat.sqrt (a * 10 ^ 10) ≤ z →
      z ≤ Nat.sqrt (a * 10 ^ 10) + 1 → Res a (loop (a : Int) (n + 1) (y : Int) (z : Int)) := by
  obtain ⟨hs5, hs⟩ := root_bounds a ha h
  intro n y z hy hz h1 h2
  by_cases hzy : z = y
  · subst hzy
    have hy' := ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self hy hz.symm
    refine ⟨z, z, loop_stop _ _ _, ?_⟩
    rw [Nat.min_self]; exact hy'
  · rewrite [loop_step n (by omega) hzy (body_fits a ha h h1 (by omega)), step_eq]
    exact phase_end a ha h n z _ h1 h2 rfl

/-- Phase 1: an error of at most `2^m + 2` above the root halves with each step; after `m + 3`
iterations the loop has ended at the root. -/
theorem phase_far (ha : 0 < a) (h : a ≤ 2 ^ 167 - 1) :
    ∀ m n y z, m + 3 ≤ n → 0 < y → z = newton (a * 10 ^ 10) y → Nat.sqrt (a * 10 ^ 10) ≤ z →
      z ≤ 2 ^ 166 + 2 ^ 40 → z - Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ m + 2 →
      Res a (loop (a : Int) n (y : Int) (z : Int)) := by
  obtain ⟨hs5, hs⟩ := root_bounds a ha h
  have h166 : Nat.sqrt (a * 10 ^ 10) + 1 ≤ 2 ^ 166 + 2 ^ 40 :=
    Nat.le_trans hs (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) (Nat.le_add_right _ _))
  intro m
  induction m with
  | zero =>
    intro n y z hn hy hz h1 h2 hd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 + 1 := ⟨n - 3, by omega⟩
    by_cases hzy : z = y
    · subst hzy
      have hy' := ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self hy hz.symm
      refine ⟨z, z, loop_stop _ _ _, ?_⟩
      rw [Nat.min_self]; exact hy'
    · have hz0 : 0 < z := by omega
      have hsq : (z - Nat.sqrt (a * 10 ^ 10)) * (z - Nat.sqrt (a * 10 ^ 10)) ≤ 2 * Nat.sqrt (a * 10 ^ 10) := by
        have : (z - Nat.sqrt (a * 10 ^ 10)) * (z - Nat.sqrt (a * 10 ^ 10)) ≤ 3 * 3 :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      have e1 := ProofForgeFin.Sqrt.newton_le_sqrt_add_one hz0 h1 hsq
      have e2 := ProofForgeFin.Sqrt.sqrt_le_newton (a := a * 10 ^ 10) hz0
      rewrite [loop_step (k + 2) hz0 hzy (body_fits a ha h h1 h2), step_eq]
      exact phase_near a ha h (k + 1) z _ hz0 rfl e2 e1
  | succ m ih =>
    intro n y z hn hy hz h1 h2 hd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    by_cases hzy : z = y
    · subst hzy
      have hy' := ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self hy hz.symm
      refine ⟨z, z, loop_stop _ _ _, ?_⟩
      rw [Nat.min_self]; exact hy'
    · have hz0 : 0 < z := by omega
      have e1 := ProofForgeFin.Sqrt.newton_sub_sqrt_le_half (a := a * 10 ^ 10) hz0 h1
      have e2 := ProofForgeFin.Sqrt.sqrt_le_newton (a := a * 10 ^ 10) hz0
      have e3 : newton (a * 10 ^ 10) z ≤ 2 ^ 166 + 2 ^ 40 := by
        rcases Nat.lt_or_ge (Nat.sqrt (a * 10 ^ 10)) z with c | c
        · exact Nat.le_trans (Nat.le_of_lt (ProofForgeFin.Sqrt.newton_lt_self c)) h2
        · have := ProofForgeFin.Sqrt.newton_le_sqrt_add_one (a := a * 10 ^ 10) hz0 h1 (by
            have : z - Nat.sqrt (a * 10 ^ 10) = 0 := by omega
            rw [this]; exact Nat.zero_le _)
          omega
      have e4 : newton (a * 10 ^ 10) z - Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ m + 2 := by
        have : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [this] at hd
        omega
      rewrite [loop_step k hz0 hzy (body_fits a ha h h1 h2), step_eq]
      exact ih k z _ (by omega) hz0 rfl e2 e3 e4

end

/-- On a positive decimal the routine returns the root of `x * 10^10`. -/
theorem sqrt_pos_eq {a : Nat} (ha : 0 < a) (h : a ≤ 2 ^ 167 - 1) :
    sqrt (a : Int) = some ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  rw [show sqrt (a : Int) = vyperSqrtWith (fun y z => if y < z then y else z) (a : Int) from rfl,
    vyperSqrtWith_pos _ ha h]
  obtain ⟨hs5, hs⟩ := root_bounds a ha h
  have hfin : ∀ y z : Nat, (if (y : Int) < (z : Int) then (y : Int) else (z : Int)) = ((min y z : Nat) : Int) := by
    intro y z
    rw [Nat.min_def]
    by_cases c : y < z
    · rw [ite_eq_left (by exact_mod_cast c), ite_eq_left (by omega)]
    · rw [ite_eq_right (by exact_mod_cast c)]
      by_cases c' : y ≤ z
      · have : y = z := by omega
        subst this; rw [ite_eq_left c']
      · rw [ite_eq_right c']
  suffices hr : Res a (loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)) by
    obtain ⟨y, z, hyz, hm⟩ := hr
    rewrite [hyz]
    show some (if (y : Int) < (z : Int) then (y : Int) else (z : Int)) = _
    rw [hfin, hm]
  by_cases h0 : a / 2 + 5 * 10 ^ 9 = a
  · -- the seed equals the input: `a` is `10^10 - 1` or `10^10`, its own root
    rw [h0]
    refine ⟨a, a, loop_stop _ _ _, ?_⟩
    rw [Nat.min_self]
    have ha' : a = 10 ^ 10 - 1 ∨ a = 10 ^ 10 := by omega
    rcases ha' with rfl | rfl
    · exact (ProofForgeFin.Sqrt.sqrt_eq_of_bounds (by decide) (by decide)).symm
    · exact (ProofForgeFin.Sqrt.sqrt_eq_of_bounds (by decide) (by decide)).symm
  · -- one step from the seed, then phase 1 with `m = 166`
    have hz0 : 0 < a / 2 + 5 * 10 ^ 9 := by omega
    have hdiv : a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9) ≤ 2 * 10 ^ 10 := by
      apply Nat.div_le_of_le_mul
      have : a ≤ 2 * (a / 2 + 5 * 10 ^ 9) := by omega
      have := Nat.mul_le_mul_right (10 ^ 10) this
      rw [Nat.mul_comm (a / 2 + 5 * 10 ^ 9), Nat.mul_assoc]
      grind
    have hseed : a / 2 + 5 * 10 ^ 9 + 2 * 10 ^ 10 ≤ 2 ^ 166 + 2 ^ 40 := by
      have e : (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 2 * 10 ^ 10 ≤ 2 ^ 166 + 2 ^ 40 := by decide
      have := Nat.div_le_div_right (c := 2) h
      generalize (2 : Nat) ^ 167 - 1 = M at *
      generalize (2 : Nat) ^ 166 + 2 ^ 40 = Q at *
      omega
    have hfit : a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9) + (a / 2 + 5 * 10 ^ 9) ≤ 2 ^ 167 - 1 := by
      rw [Nat.add_comm]
      exact Nat.le_trans (Nat.add_le_add_left hdiv _) (Nat.le_trans hseed (by decide))
    have hne : a / 2 + 5 * 10 ^ 9 ≠ a := h0
    rewrite [loop_step 255 hz0 hne hfit, step_eq]
    have e2 := ProofForgeFin.Sqrt.sqrt_le_newton (a := a * 10 ^ 10) hz0
    have e3 : newton (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) ≤ 2 ^ 166 + 2 ^ 40 := by
      unfold newton
      exact Nat.le_trans (Nat.div_le_self _ _) (Nat.le_trans (Nat.add_le_add_left hdiv _) hseed)
    exact phase_far a ha h 167 255 _ _ (by decide) hz0 rfl e2 e3
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans e3 (by decide)))

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := fun x hx => by
  show (if x < 0 then none else _) = none
  rw [ite_eq_left hx]

/-- On a non-negative decimal the routine returns the root of `x * 10^10`. -/
theorem sqrt_nonneg_eq {x : Int} (hx : IsDecimal x) (h0 : 0 ≤ x) :
    sqrt x = some ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have ha : a ≤ 2 ^ 167 - 1 := by
    have := hx.2; rw [max_decimal_eq] at this; exact_mod_cast this
  rw [Int.toNat_natCast]
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · show (if ((0 : Nat) : Int) < 0 then none else if ((0 : Nat) : Int) = 0 then some 0 else _) = _
    rw [ite_eq_right (by decide), ite_eq_left (by simp)]
    exact congrArg some (by rw [Nat.zero_mul, show Nat.sqrt 0 = 0 from
      ProofForgeFin.Sqrt.sqrt_eq_of_bounds (by decide) (by decide)]; rfl)
  · exact sqrt_pos_eq hpos ha

theorem req_sqrt_total : SqrtTotal sqrt := fun x hx h0 => by
  rw [sqrt_nonneg_eq hx h0]; rfl

/-- The result of a non-negative decimal input, by cases on the sign. -/
theorem sqrt_some {x r : Int} (hx : IsDecimal x) (h : sqrt x = some r) :
    ∃ a : Nat, x = (a : Int) ∧ r = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  rcases Int.lt_or_le x 0 with hneg | h0
  · rw [req_sqrt_neg_reverts x hneg] at h; cases h
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [sqrt_nonneg_eq hx h0, Int.toNat_natCast] at h
    exact ⟨a, rfl, (Option.some.inj h).symm⟩

theorem req_sqrt_not_above : SqrtNotAbove sqrt := fun x r hx h => by
  obtain ⟨a, rfl, rfl⟩ := sqrt_some hx h
  rw [divisor_eq, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr (Nat.sqrt_le _)

theorem req_sqrt_not_below : SqrtNotBelow sqrt := fun x r hx h => by
  obtain ⟨a, rfl, rfl⟩ := sqrt_some hx h
  rw [divisor_eq, ← Int.natCast_mul, show ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) + 1 =
    ((Nat.sqrt (a * 10 ^ 10) + 1 : Nat) : Int) by push_cast; rfl, ← Int.natCast_mul]
  exact Int.ofNat_lt.mpr (Nat.lt_succ_sqrt _)

end VyperSqrt

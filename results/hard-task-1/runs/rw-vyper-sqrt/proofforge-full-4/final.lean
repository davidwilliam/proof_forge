import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt

namespace VyperSqrt

open ProofForgeFin.Sqrt

/-- Final choice: the smaller of the last two iterates (PR 4486 fix). -/
def finMin : Int → Int → Int := fun y z => if y < z then y else z

def sqrt : SqrtFn := vyperSqrtWith finMin

/-- Newton seed: `x / 2.0 + 0.5` on raw values. -/
def seedN (a : Nat) : Nat := a / 2 + 5 * 10^9

/-- Newton iterates for `A = a * 10^10` from the seed. -/
def ZN (a : Nat) : Nat → Nat
  | 0 => seedN a
  | n + 1 => newton (a * 10^10) (ZN a n)

/-- Nat mirror of `loop`: fuel, previous iterate, current iterate. -/
def nloopN (A : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, z => (y, z)
  | n + 1, y, z => if z = y then (y, z) else nloopN A n z (newton A z)

/-- The seed is positive. -/
theorem seedN_pos {a : Nat} : 0 < seedN a := by
  unfold seedN
  omega

/-- `A = a * 10^10` is positive for `a ≥ 1`. -/
theorem A_pos {a : Nat} (ha : 1 ≤ a) : 0 < a * 10^10 := by
  have h : 1 * 10^10 ≤ a * 10^10 := Nat.mul_le_mul_right _ ha
  omega

/-- The root is at least 2 for `a ≥ 1`. -/
theorem sqrt_ge_two {a : Nat} (ha : 1 ≤ a) : 2 ≤ Nat.sqrt (a * 10^10) := by
  apply le_sqrt_of_mul_self_le (m := 2)
  have h : 1 * 10^10 ≤ a * 10^10 := Nat.mul_le_mul_right _ ha
  omega

/-- Key square bound: `(seed + 1)^2 > A`, hence the seed is above the root. -/
theorem seed_sq (q : Nat) :
    2 * (q * 10^10) + 10^10 + 1 ≤ (q + 5 * 10^9 + 1) * (q + 5 * 10^9 + 1) := by
  have h10 : (10 : Nat)^10 = 10000000000 := by decide
  have h5 : (5 : Nat) * 10^9 = 5000000000 := by decide
  rcases Nat.le_total (5 * 10^9 - 1) q with hMq | hMq
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMq
    rw [h10, h5]
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hMq
    have hK : (5 * 10^9) = (q + d) + 1 := by omega
    have hD : (10 : Nat)^10 = 2 * (q + d) + 2 := by omega
    have two : ∀ n : Nat, 2 * n = n + n := fun n => by omega
    rw [hK, hD]
    simp only [two, Nat.add_mul, Nat.mul_add, Nat.mul_comm d q]
    omega

/-- The seed is above the root. -/
theorem seed_ge_sqrt {a : Nat} (ha : 1 ≤ a) : Nat.sqrt (a * 10^10) ≤ a / 2 + 5 * 10^9 := by
  suffices hlt : a * 10^10 < (a / 2 + 5 * 10^9 + 1) * (a / 2 + 5 * 10^9 + 1) by
    have h := sqrt_lt_of_lt_mul_self hlt
    omega
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h0
  · obtain ⟨q, rfl⟩ : ∃ q, a = 2 * q := ⟨a / 2, by omega⟩
    have e : (2 * q) / 2 = q := by omega
    rw [e]
    have hhelp := seed_sq q
    have e2 : (2 * q) * 10^10 = 2 * (q * 10^10) := by
      rw [← Nat.mul_assoc]
    omega
  · obtain ⟨q, rfl⟩ : ∃ q, a = 2 * q + 1 := ⟨a / 2, by omega⟩
    have e : (2 * q + 1) / 2 = q := by omega
    rw [e]
    have hhelp := seed_sq q
    have e2 : (2 * q + 1) * 10^10 = 2 * (q * 10^10) + 10^10 := by
      rw [Nat.add_mul, ← Nat.mul_assoc, Nat.one_mul]
    omega

/-- The seed (plus one) fits in `A`. -/
theorem seed_le_A {a : Nat} (ha : 1 ≤ a) : a / 2 + 5 * 10^9 + 1 ≤ a * 10^10 := by
  have h10sub : (10 : Nat)^10 = (10^10 - 1) + 1 :=
    (Nat.sub_add_cancel (by decide : 1 ≤ 10^10)).symm
  have hmul : 1 * (10^10 - 1) ≤ a * (10^10 - 1) := Nat.mul_le_mul_right _ ha
  have hle : 5 * 10^9 + 1 ≤ 1 * (10^10 - 1) := by decide
  have hle2 : 5 * 10^9 + 1 ≤ a * (10^10 - 1) := Nat.le_trans hle hmul
  have hdiv : a / 2 ≤ a := Nat.div_le_self a 2
  rw [h10sub, Nat.mul_add, Nat.mul_one]
  omega

/-- The root is below `2^101`. -/
theorem sqrt_lt_pow {a : Nat} (h : a ≤ 2^167 - 1) : Nat.sqrt (a * 10^10) < 2^101 := by
  have h10 : (10 : Nat)^10 < 2^34 := by decide
  have ha167 : a < 2^167 := by omega
  have hpos : (0 : Nat) < 10^10 := by decide
  have h1 : a * 10^10 < 2^167 * 10^10 := Nat.mul_lt_mul_of_pos_right ha167 hpos
  have h2 : 2^167 * 10^10 ≤ 2^167 * 2^34 := Nat.mul_le_mul_left _ (by omega)
  have h3 : a * 10^10 < 2^167 * 2^34 := Nat.lt_of_lt_of_le h1 h2
  have e201 : (2 : Nat)^167 * 2^34 = 2^201 := by
    rw [← Nat.pow_add]
  have g1 : (2 : Nat)^201 < 2^202 := Nat.pow_lt_pow_succ (by decide : 1 < 2)
  have g2 : (2 : Nat)^(2 * 101) = 2^202 := by decide
  have hfin : a * 10^10 < 2^(2 * 101) := by
    rw [g2]
    omega
  exact sqrt_lt_two_pow hfin

/-- The seed is small: at most `2^166 - 1 + 5 * 10^9`. -/
theorem seed_le {a : Nat} (h : a ≤ 2^167 - 1) : a / 2 + 5 * 10^9 ≤ 2^166 - 1 + 5 * 10^9 := by
  have h1 : a / 2 ≤ (2^167 - 1) / 2 := Nat.div_le_div_right h
  have e167 : (2 : Nat)^167 = 2 * 2^166 := by decide
  have h2 : (2^167 - 1) / 2 ≤ 2^166 - 1 := by omega
  omega

/-- The quotient `A / z` is at most `s + 2` for `z` above the root. -/
theorem quot_le {a z : Nat} (hs : 0 < Nat.sqrt (a * 10^10))
    (h : Nat.sqrt (a * 10^10) ≤ z) : a * 10^10 / z ≤ Nat.sqrt (a * 10^10) + 2 := by
  have hup := Nat.lt_succ_sqrt (a * 10^10)
  simp only [Nat.succ_eq_add_one] at hup
  have hexp : (Nat.sqrt (a * 10^10) + 1) * (Nat.sqrt (a * 10^10) + 1)
      = Nat.sqrt (a * 10^10) * (Nat.sqrt (a * 10^10) + 2) + 1 := by
    have e1 : (Nat.sqrt (a * 10^10) + 1) * (Nat.sqrt (a * 10^10) + 1)
        = (Nat.sqrt (a * 10^10) + 1) * Nat.sqrt (a * 10^10)
          + (Nat.sqrt (a * 10^10) + 1) * 1 := Nat.mul_add _ _ _
    have e2 : (Nat.sqrt (a * 10^10) + 1) * Nat.sqrt (a * 10^10)
        = Nat.sqrt (a * 10^10) * Nat.sqrt (a * 10^10)
          + 1 * Nat.sqrt (a * 10^10) := Nat.add_mul _ _ _
    have e3 : (1 : Nat) * Nat.sqrt (a * 10^10) = Nat.sqrt (a * 10^10) := Nat.one_mul _
    have e4 : (Nat.sqrt (a * 10^10) + 1) * 1 = Nat.sqrt (a * 10^10) + 1 := Nat.mul_one _
    have e5 : Nat.sqrt (a * 10^10) * (Nat.sqrt (a * 10^10) + 2)
        = Nat.sqrt (a * 10^10) * Nat.sqrt (a * 10^10)
          + Nat.sqrt (a * 10^10) * 2 := Nat.mul_add _ _ _
    have e6 : Nat.sqrt (a * 10^10) * 2
        = Nat.sqrt (a * 10^10) + Nat.sqrt (a * 10^10) := by omega
    omega
  have hle : a * 10^10 ≤ Nat.sqrt (a * 10^10) * (Nat.sqrt (a * 10^10) + 2) := by omega
  have hz : 0 < z := Nat.lt_of_lt_of_le hs h
  have d1 : (a * 10^10 / z) * Nat.sqrt (a * 10^10) ≤ a * 10^10 := by
    calc (a * 10^10 / z) * Nat.sqrt (a * 10^10)
        ≤ (a * 10^10 / z) * z := Nat.mul_le_mul_left _ h
      _ ≤ a * 10^10 := Nat.div_mul_le_self _ _
  have d2 : (a * 10^10 / z) * Nat.sqrt (a * 10^10)
      ≤ (Nat.sqrt (a * 10^10) + 2) * Nat.sqrt (a * 10^10) := by
    calc (a * 10^10 / z) * Nat.sqrt (a * 10^10) ≤ a * 10^10 := d1
      _ ≤ Nat.sqrt (a * 10^10) * (Nat.sqrt (a * 10^10) + 2) := hle
      _ = (Nat.sqrt (a * 10^10) + 2) * Nat.sqrt (a * 10^10) := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right d2 hs

/-- One Newton step stays in range: `A / z + z` fits in a decimal. -/
theorem sum_le {a z : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1)
    (hlo : Nat.sqrt (a * 10^10) ≤ z) (hhi : z ≤ a / 2 + 5 * 10^9 + 1) :
    a * 10^10 / z + z ≤ 2^167 - 1 := by
  have hs : 0 < Nat.sqrt (a * 10^10) := by
    have h2 := sqrt_ge_two ha1
    omega
  have hq := quot_le hs hlo
  have hseed := seed_le haM
  have hsq := sqrt_lt_pow haM
  have key : 5 * 10^9 + 2^101 + 3 ≤ 2^166 := by decide
  have e167 : (2 : Nat)^167 = 2 * 2^166 := by decide
  omega

/-- One Newton step preserves the `[s, seed + 1]` interval. -/
theorem newton_mem {a x : Nat} (ha1 : 1 ≤ a)
    (hlo : Nat.sqrt (a * 10^10) ≤ x) (hhi : x ≤ a / 2 + 5 * 10^9 + 1) (hx : 0 < x) :
    Nat.sqrt (a * 10^10) ≤ newton (a * 10^10) x
      ∧ newton (a * 10^10) x ≤ a / 2 + 5 * 10^9 + 1 := by
  refine ⟨sqrt_le_newton hx, ?_⟩
  have hss := seed_ge_sqrt ha1
  by_cases heq : x = Nat.sqrt (a * 10^10)
  · have h2 : x ≤ Nat.sqrt (a * 10^10) + 1 := by omega
    have hmem := newton_of_mem hx hlo h2
    rcases hmem with h1 | ⟨_, h1, _⟩ <;> omega
  · have hlt : Nat.sqrt (a * 10^10) < x := by omega
    have hlt2 := newton_lt_self hlt
    omega

/-- Newton iterates stay positive. -/
theorem newton_pos {a x : Nat} (hxA : x ≤ a * 10^10) (hx : 0 < x) :
    0 < newton (a * 10^10) x := by
  have hq : 1 ≤ (a * 10^10) / x := by
    rw [Nat.le_div_iff_mul_le hx]
    omega
  show 0 < (x + a * 10^10 / x) / 2
  omega

/-- Newton iterates never exceed `A`. -/
theorem newton_le_A {a x : Nat} (hxA : x ≤ a * 10^10) :
    newton (a * 10^10) x ≤ a * 10^10 := by
  have hq : (a * 10^10) / x ≤ a * 10^10 := Nat.div_le_self _ _
  have h1 : x + (a * 10^10) / x ≤ (a * 10^10) + (a * 10^10) := by omega
  have h2 : (x + (a * 10^10) / x) / 2 ≤ ((a * 10^10) + (a * 10^10)) / 2 :=
    Nat.div_le_div_right h1
  have h3 : ((a * 10^10) + (a * 10^10)) / 2 = a * 10^10 := by omega
  show (x + (a * 10^10) / x) / 2 ≤ a * 10^10
  omega

/-- All iterates stay positive, above the root, below `seed + 1`, and below `A`. -/
theorem ZN_inv {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    ∀ k, 0 < ZN a k ∧ Nat.sqrt (a * 10^10) ≤ ZN a k
      ∧ ZN a k ≤ a / 2 + 5 * 10^9 + 1 ∧ ZN a k ≤ a * 10^10 := by
  intro k
  induction k with
  | zero =>
    show 0 < a / 2 + 5 * 10^9 ∧ Nat.sqrt (a * 10^10) ≤ a / 2 + 5 * 10^9
      ∧ a / 2 + 5 * 10^9 ≤ a / 2 + 5 * 10^9 + 1 ∧ a / 2 + 5 * 10^9 ≤ a * 10^10
    refine ⟨by omega, seed_ge_sqrt ha1, by omega, ?_⟩
    have h := seed_le_A ha1
    omega
  | succ k ih =>
    obtain ⟨hpos, hge, hle, hleA⟩ := ih
    have hmem := newton_mem ha1 hge hle hpos
    show 0 < newton (a * 10^10) (ZN a k)
      ∧ Nat.sqrt (a * 10^10) ≤ newton (a * 10^10) (ZN a k)
      ∧ newton (a * 10^10) (ZN a k) ≤ a / 2 + 5 * 10^9 + 1
      ∧ newton (a * 10^10) (ZN a k) ≤ a * 10^10
    exact ⟨newton_pos hleA hpos, hmem.1, hmem.2, newton_le_A hleA⟩

/-- Quadratic-halving error bound for the iterates. -/
theorem ZN_err {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    ∀ k, ZN a k - Nat.sqrt (a * 10^10)
      ≤ (seedN a - Nat.sqrt (a * 10^10)) / 2^k + 2 := by
  have hinv := ZN_inv ha1 haM
  intro k
  induction k with
  | zero =>
    rw [Nat.pow_zero, Nat.div_one]
    show seedN a - Nat.sqrt (a * 10^10) ≤ _
    omega
  | succ k ih =>
    have hpos := (hinv k).1
    have hge := (hinv k).2.1
    have hstep := newton_sub_sqrt_le_half hpos hge
    have hmono : (ZN a k - Nat.sqrt (a * 10^10)) / 2
        ≤ ((seedN a - Nat.sqrt (a * 10^10)) / 2^k + 2) / 2 :=
      Nat.div_le_div_right ih
    have e1 : ((seedN a - Nat.sqrt (a * 10^10)) / 2^k + 2) / 2
        = (seedN a - Nat.sqrt (a * 10^10)) / 2^k / 2 + 1 := by omega
    have e2 : (seedN a - Nat.sqrt (a * 10^10)) / 2^k / 2
        = (seedN a - Nat.sqrt (a * 10^10)) / 2^(k + 1) := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
    show newton (a * 10^10) (ZN a k) - Nat.sqrt (a * 10^10) ≤ _
    omega

/-- After 168 steps the iterate is at most `s + 1`. -/
theorem ZN_168 {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    ZN a 168 ≤ Nat.sqrt (a * 10^10) + 1 := by
  have hinv := ZN_inv ha1 haM
  have herr := ZN_err ha1 haM 167
  have hE0 : seedN a - Nat.sqrt (a * 10^10) < 2^167 := by
    have hseed : seedN a ≤ 2^166 - 1 + 5 * 10^9 := seed_le haM
    have e167 : (2 : Nat)^167 = 2 * 2^166 := by decide
    omega
  have hdiv0 : (seedN a - Nat.sqrt (a * 10^10)) / 2^167 = 0 := Nat.div_eq_of_lt hE0
  have h167 : ZN a 167 - Nat.sqrt (a * 10^10) ≤ 2 := by omega
  have hpos167 := (hinv 167).1
  have hge167 := (hinv 167).2.1
  have hsq : (ZN a 167 - Nat.sqrt (a * 10^10)) * (ZN a 167 - Nat.sqrt (a * 10^10))
      ≤ 2 * Nat.sqrt (a * 10^10) := by
    have hs2 := sqrt_ge_two ha1
    have e1 : (ZN a 167 - Nat.sqrt (a * 10^10)) * (ZN a 167 - Nat.sqrt (a * 10^10))
        ≤ 2 * 2 := Nat.mul_le_mul h167 h167
    omega
  have hstep := newton_le_sqrt_add_one hpos167 hge167 hsq
  show newton (a * 10^10) (ZN a 167) ≤ _
  omega

/-- From step 168 on, every iterate is the root or the root plus one. -/
theorem ZN_mem {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    ∀ k, 168 ≤ k → ZN a k = Nat.sqrt (a * 10^10)
      ∨ ZN a k = Nat.sqrt (a * 10^10) + 1 := by
  have hinv := ZN_inv ha1 haM
  have h168 : ZN a 168 = Nat.sqrt (a * 10^10)
      ∨ ZN a 168 = Nat.sqrt (a * 10^10) + 1 := by
    have hge := (hinv 168).2.1
    have hle := ZN_168 ha1 haM
    omega
  have gen : ∀ d, ZN a (168 + d) = Nat.sqrt (a * 10^10)
      ∨ ZN a (168 + d) = Nat.sqrt (a * 10^10) + 1 := by
    intro d
    induction d with
    | zero => simpa using h168
    | succ d ih =>
      have hpos := (hinv (168 + d)).1
      have hge := (hinv (168 + d)).2.1
      have hle : ZN a (168 + d) ≤ Nat.sqrt (a * 10^10) + 1 := by omega
      have hmem := newton_of_mem hpos hge hle
      show newton (a * 10^10) (ZN a (168 + d)) = _
        ∨ newton (a * 10^10) (ZN a (168 + d)) = _ + 1
      rcases hmem with h1 | ⟨_, h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
  intro k hk
  have e : k = 168 + (k - 168) := by omega
  rw [e]
  exact gen _

/-- Unfold one iterate. -/
theorem ZN_succ {a : Nat} (k : Nat) :
    ZN a (k + 1) = newton (a * 10^10) (ZN a k) := rfl

/-- A fixed point of the iteration is the root. -/
theorem ZN_fix {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) {k : Nat}
    (h : ZN a (k + 1) = ZN a k) : ZN a k = Nat.sqrt (a * 10^10) := by
  have hpos := (ZN_inv ha1 haM k).1
  have e : newton (a * 10^10) (ZN a k) = ZN a k := h
  exact eq_sqrt_of_newton_eq_self hpos e

/-- If the seed equals the input, the input is the root. -/
theorem seed_eq_self {a : Nat} (ha1 : 1 ≤ a) (h : seedN a = a) :
    a = Nat.sqrt (a * 10^10) := by
  have h2 : a / 2 + 5 * 10^9 = a := h
  have hcase : a = 9999999999 ∨ a = 10^10 := by
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h0
    · have hd : a = 2 * (a / 2) := by omega
      have hev : a = 10^10 := by omega
      exact Or.inr hev
    · have hd : a = 2 * (a / 2) + 1 := by omega
      have hod : a = 9999999999 := by omega
      exact Or.inl hod
  rcases hcase with rfl | rfl
  · exact (sqrt_eq_of_bounds (by decide) (by decide)).symm
  · exact (sqrt_eq_of_bounds (by decide) (by decide)).symm
/-- The Int loop mirrors the Nat loop on reachable states. -/
theorem loop_bridge {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    ∀ (n y z : Nat),
      (y = a ∨ (Nat.sqrt (a * 10^10) ≤ y ∧ y ≤ a / 2 + 5 * 10^9 + 1))
      → Nat.sqrt (a * 10^10) ≤ z → z ≤ a / 2 + 5 * 10^9 + 1 → 0 < z
      → loop (a : Int) n (y : Int) (z : Int)
        = some ((((nloopN (a * 10^10) n y z).1 : Nat) : Int),
          (((nloopN (a * 10^10) n y z).2 : Nat) : Int)) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ _ _
    simp only [nloopN]
    rfl
  | succ n ih =>
    intro y z hy hs hz1 hz2
    by_cases hzy : z = y
    · subst hzy
      rw [loop_stop]
      simp only [nloopN]
      rfl
    · have hbnd : a * 10^10 / z + z ≤ 2^167 - 1 := sum_le ha1 haM hs hz1
      rw [loop_step n hz2 hzy hbnd]
      have eN : ((a * 10^10 / z + z) / 2) = newton (a * 10^10) z := by
        unfold newton
        omega
      rw [eN]
      have eR : nloopN (a * 10^10) (n + 1) y z
          = nloopN (a * 10^10) n z (newton (a * 10^10) z) := by
        simp only [nloopN]
        rw [if_neg hzy]
      rw [eR]
      apply ih
      · exact Or.inr ⟨hs, hz1⟩
      · exact sqrt_le_newton hz2
      · exact (newton_mem ha1 hs hz1 hz2).2
      · have hleA : z ≤ a * 10^10 := by
          have hA := seed_le_A ha1
          omega
        exact newton_pos hleA hz2

/-- The Nat loop from consecutive iterates ends at `(s, s)` or runs out of fuel. -/
theorem nloopN_run {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    ∀ (n k : Nat), nloopN (a * 10^10) n (ZN a k) (ZN a (k + 1))
      = (Nat.sqrt (a * 10^10), Nat.sqrt (a * 10^10))
      ∨ nloopN (a * 10^10) n (ZN a k) (ZN a (k + 1))
        = (ZN a (k + n), ZN a (k + n + 1)) := by
  intro n
  induction n with
  | zero => intro k; exact Or.inr rfl
  | succ n ih =>
    intro k
    by_cases heq : ZN a (k + 1) = ZN a k
    · have hN : nloopN (a * 10^10) (n + 1) (ZN a k) (ZN a (k + 1))
          = (ZN a k, ZN a (k + 1)) := by
        simp only [nloopN]
        rw [if_pos heq]
      rw [hN]
      left
      have hfix := ZN_fix ha1 haM heq
      rw [heq, hfix]
    · have eR : nloopN (a * 10^10) (n + 1) (ZN a k) (ZN a (k + 1))
          = nloopN (a * 10^10) n (ZN a (k + 1)) (ZN a (k + 1 + 1)) := by
        simp only [nloopN]
        rw [if_neg heq, ← ZN_succ (k + 1)]
      rw [eR]
      rcases ih (k + 1) with h1 | h1
      · exact Or.inl h1
      · right
        have e1 : (k + 1) + n = k + (n + 1) := by omega
        rw [e1] at h1
        exact h1

/-- The top-level loop ends at `(s, s)` or at `(ZN 255, ZN 256)`. -/
theorem loop_result {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10^9 : Nat)) : Int)
      = some ((((Nat.sqrt (a * 10^10) : Nat)) : Int),
        (((Nat.sqrt (a * 10^10) : Nat)) : Int))
    ∨ loop (a : Int) 256 (a : Int) (((a / 2 + 5 * 10^9 : Nat)) : Int)
      = some ((((ZN a 255 : Nat)) : Int), (((ZN a 256 : Nat)) : Int)) := by
  by_cases hseed : seedN a = a
  · have e0 : (((a / 2 + 5 * 10^9 : Nat)) : Int) = (a : Int) := by
      have h2 : a / 2 + 5 * 10^9 = a := hseed
      rw [h2]
    have e256 : (256 : Nat) = 255 + 1 := rfl
    rw [e0, e256, loop_stop]
    left
    have haS := seed_eq_self ha1 hseed
    rw [← haS]
  · have e256 : (256 : Nat) = 255 + 1 := rfl
    rw [e256]
    have hz : 0 < a / 2 + 5 * 10^9 := seedN_pos
    have hne2 : a / 2 + 5 * 10^9 ≠ a := hseed
    have hbnd : a * 10^10 / (a / 2 + 5 * 10^9) + (a / 2 + 5 * 10^9) ≤ 2^167 - 1 :=
      sum_le ha1 haM (seed_ge_sqrt ha1) (Nat.le_add_right _ _)
    rw [loop_step 255 hz hne2 hbnd]
    have eAc : (a * 10^10 / (a / 2 + 5 * 10^9) + (a / 2 + 5 * 10^9)) / 2
        = ((a / 2 + 5 * 10^9) + a * 10^10 / (a / 2 + 5 * 10^9)) / 2 := by
      rw [Nat.add_comm]
    rw [eAc]
    have hbr := loop_bridge ha1 haM 255 (ZN a 0) (ZN a 1)
      (Or.inr ⟨seed_ge_sqrt ha1, Nat.le_add_right _ _⟩)
      ((ZN_inv ha1 haM 1).2.1) ((ZN_inv ha1 haM 1).2.2.1) ((ZN_inv ha1 haM 1).1)
    have hN := nloopN_run ha1 haM 255 0
    have i2 : (0 : Nat) + 255 + 1 = 256 := by omega
    have i1 : (0 : Nat) + 255 = 255 := by omega
    rw [i2, i1] at hN
    rcases hN with hN | hN
    · left
      refine hbr.trans ?_
      rw [hN]
    · right
      refine hbr.trans ?_
      rw [hN]

/-- On a positive decimal input, `sqrt` returns the root `s`. -/
theorem sqrt_pos_nat {a : Nat} (ha1 : 1 ≤ a) (haM : a ≤ 2^167 - 1) :
    sqrt ((a : Nat) : Int) = some (((Nat.sqrt (a * 10^10) : Nat)) : Int) := by
  show vyperSqrtWith finMin (a : Int) = _
  rw [vyperSqrtWith_pos finMin (by omega : 0 < a) haM]
  have hloop := loop_result ha1 haM
  rcases hloop with h | h
  · rw [h]
    have hfin0 : finMin (((Nat.sqrt (a * 10^10) : Nat)) : Int)
        (((Nat.sqrt (a * 10^10) : Nat)) : Int)
        = (((Nat.sqrt (a * 10^10) : Nat)) : Int) := by
      unfold finMin
      rw [if_neg (by omega)]
    exact congrArg _ hfin0
  · rw [h]
    have hm255 := ZN_mem ha1 haM 255 (by decide : 168 ≤ 255)
    have hpos255 := (ZN_inv ha1 haM 255).1
    have hge255 := (ZN_inv ha1 haM 255).2.1
    have hle255 : ZN a 255 ≤ Nat.sqrt (a * 10^10) + 1 := by
      rcases hm255 with h | h <;> omega
    have hmin := min_newton_eq_sqrt hpos255 hge255 hle255
    have hss : ZN a (255 + 1) = newton (a * 10^10) (ZN a 255) := ZN_succ 255
    have e256 : (256 : Nat) = 255 + 1 := rfl
    have eN : ZN a 256 = newton (a * 10^10) (ZN a 255) := by
      rw [e256]
      exact hss
    have hfin : finMin ((((ZN a 255 : Nat))) : Int) ((((ZN a 256 : Nat))) : Int)
        = (((Nat.sqrt (a * 10^10) : Nat)) : Int) := by
      unfold finMin
      rw [eN]
      by_cases hlt : ZN a 255 < newton (a * 10^10) (ZN a 255)
      · rw [if_pos (by exact_mod_cast hlt)]
        have hmineq : Nat.min (ZN a 255) (newton (a * 10^10) (ZN a 255))
            = ZN a 255 := Nat.min_eq_left (by omega)
        omega
      · rw [if_neg (by exact_mod_cast hlt)]
        have hmineq : Nat.min (ZN a 255) (newton (a * 10^10) (ZN a 255))
            = newton (a * 10^10) (ZN a 255) := Nat.min_eq_right (by omega)
        omega
    exact congrArg _ hfin

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hdec hr
  have hr2 : vyperSqrtWith finMin x = some r := hr
  unfold vyperSqrtWith at hr2
  by_cases hx : x < 0
  · rw [if_pos hx] at hr2
    cases hr2
  · have hx0 : 0 ≤ x := by omega
    by_cases hx00 : x = 0
    · subst hx00
      rw [if_neg (by omega : ¬((0 : Int) < 0)), if_pos rfl] at hr2
      have hrr : (0 : Int) = r := Option.some_inj.mp hr2
      subst hrr
      simp
    · obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
        ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
      have ha1 : 1 ≤ a := by
        have hane : a ≠ 0 := by
          intro h
          subst h
          exact hx00 Int.ofNat_zero
        exact Nat.pos_of_ne_zero hane
      have haM : a ≤ 2^167 - 1 := by
        have h := hdec.2
        rw [max_decimal_eq] at h
        exact Int.ofNat_le.mp h
      have hsqrt := sqrt_pos_nat ha1 haM
      have hrr : r = (((Nat.sqrt (a * 10^10) : Nat)) : Int) :=
        Option.some_inj.mp (hr2.symm.trans hsqrt)
      rw [hrr, divisor_eq, ← Int.natCast_mul, ← Int.natCast_mul]
      exact Int.ofNat_le.mpr (Nat.sqrt_le _)

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hdec hr
  have hr2 : vyperSqrtWith finMin x = some r := hr
  unfold vyperSqrtWith at hr2
  by_cases hx : x < 0
  · rw [if_pos hx] at hr2
    cases hr2
  · have hx0 : 0 ≤ x := by omega
    by_cases hx00 : x = 0
    · subst hx00
      rw [if_neg (by omega : ¬((0 : Int) < 0)), if_pos rfl] at hr2
      have hrr : (0 : Int) = r := Option.some_inj.mp hr2
      subst hrr
      simp
    · obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
        ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
      have ha1 : 1 ≤ a := by
        have hane : a ≠ 0 := by
          intro h
          subst h
          exact hx00 Int.ofNat_zero
        exact Nat.pos_of_ne_zero hane
      have haM : a ≤ 2^167 - 1 := by
        have h := hdec.2
        rw [max_decimal_eq] at h
        exact Int.ofNat_le.mp h
      have hsqrt := sqrt_pos_nat ha1 haM
      have hrr : r = (((Nat.sqrt (a * 10^10) : Nat)) : Int) :=
        Option.some_inj.mp (hr2.symm.trans hsqrt)
      rw [hrr, divisor_eq, ← Int.ofNat_one, ← Int.natCast_add,
        ← Int.natCast_mul, ← Int.natCast_mul]
      have hlt := Nat.lt_succ_sqrt (a * 10^10)
      simp only [Nat.succ_eq_add_one] at hlt
      exact Int.ofNat_lt.mpr hlt

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hdec hx0
  by_cases hx : x < 0
  · exfalso
    omega
  · by_cases hx00 : x = 0
    · subst hx00
      have e : sqrt (0 : Int) = some 0 := by
        show vyperSqrtWith finMin 0 = _
        unfold vyperSqrtWith
        rw [if_neg (by omega : ¬((0 : Int) < 0)), if_pos rfl]
      rw [e]
      exact Option.isSome_some
    · obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
        ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
      have ha1 : 1 ≤ a := by
        have hane : a ≠ 0 := by
          intro h
          subst h
          exact hx00 Int.ofNat_zero
        exact Nat.pos_of_ne_zero hane
      have haM : a ≤ 2^167 - 1 := by
        have h := hdec.2
        rw [max_decimal_eq] at h
        exact Int.ofNat_le.mp h
      have hsqrt := sqrt_pos_nat ha1 haM
      rw [hsqrt]
      exact Option.isSome_some

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith finMin x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt := by
  exact ⟨finMin, fun x => rfl⟩

end VyperSqrt


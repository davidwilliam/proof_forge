import VyperSqrt.Spec
import VyperSqrt.Lemmas
/-!
Fixed port of the code the Vyper compiler inlines for `sqrt(d: decimal)`.

The deployed v0.4.0 loop returns the last iterate `z`, which can round the root
*up* (e.g. on `0.9999999998` it returns `0.9999999999`, whose square exceeds the
input). Pull request 4486 (released in v0.4.1) adds, after the loop,

```
if y < z:
    z = y
```

i.e. the routine returns the *minimum* of the last two iterates. The Babylonian
iteration on naturals converges to the exact floor (a fixed point is the floor;
a 2-cycle is `{floor, floor + 1}`), so the minimum of the final pair is the root
rounded down. This file proves that: `sqrt` satisfies all five locked
requirements.
-/
namespace VyperSqrt

/-- The PR 4486 fix: the deployed loop followed by the minimum of the last two
iterates. -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-! ## Natural-number model of the Newton iteration -/

/-- Scaled radicand on naturals: raw value of `x * DIVISOR`. -/
def newtN (a : Nat) : Nat := a * 10 ^ 10

/-- Loop seed on naturals: `x / 2 + 5 * 10^9`. -/
def newtS (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- One Newton step on naturals. -/
def newtF (a z : Nat) : Nat := (newtN a / z + z) / 2

/-- Newton orbit: `newtSeq a 0` is the seed, each next value is a Newton step. -/
def newtSeq (a : Nat) : Nat → Nat
  | 0 => newtS a
  | n + 1 => newtF a (newtSeq a n)

/-- Arithmetic-geometric mean inequality on naturals. -/
theorem two_mul_le_add_sq (u v : Nat) : 2 * (u * v) ≤ u * u + v * v := by
  rcases Nat.le_total u v with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have c : u * d = d * u := Nat.mul_comm _ _
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have c : d * v = v * d := Nat.mul_comm _ _
    simp only [Nat.add_mul, Nat.mul_add]
    omega

/-- Uniqueness of the natural square root from the two defining inequalities. -/
theorem nsqrt_eq_of_sq {N b : Nat} (h1 : b * b ≤ N) (h2 : N < (b + 1) * (b + 1)) :
    Nat.sqrt N = b := by
  by_cases heq : Nat.sqrt N = b
  · exact heq
  · have hlt := Nat.lt_succ_sqrt N
    rw [Nat.succ_eq_add_one] at hlt
    rcases Nat.lt_or_ge (Nat.sqrt N) b with h | h
    · have h3 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ b * b :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    · have h4 : b + 1 ≤ Nat.sqrt N := by omega
      have h5 : (b + 1) * (b + 1) ≤ Nat.sqrt N * Nat.sqrt N :=
        Nat.mul_le_mul h4 h4
      have h6 := Nat.sqrt_le N
      omega

/-- Successor square expansion. -/
theorem sq_succ_eq (m : Nat) : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-- Purely linear transitivity consequence used in E1 (kept free of `/` and
`%` terms, which `omega` abstracts incompletely). -/
theorem aux_E1 (A B C N : Nat) (h2 : A ≤ B) (h1 : B ≤ C) (hq : C ≤ N)
    (hm2 : N < A) : False := by
  omega

/-- E1: above the root, the quotient `N / z` is at most `m`. -/
theorem newt_div_le {a m z : Nat} (hm2 : newtN a < (m + 1) * (m + 1))
    (hz : m + 1 ≤ z) : newtN a / z ≤ m := by
  by_cases h : newtN a / z ≤ m
  · exact h
  · exfalso
    have h1 : (m + 1) * z ≤ newtN a / z * z :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (m + 1) * (m + 1) ≤ (m + 1) * z :=
      Nat.mul_le_mul_left _ hz
    have hq := Nat.div_mul_le_self (newtN a) z
    exact aux_E1 _ _ _ _ h2 h1 hq hm2

/-- E2: above the root, the Newton step strictly decreases. -/
theorem newt_lt {a m z : Nat} (hm2 : newtN a < (m + 1) * (m + 1))
    (hz : m + 1 ≤ z) (hle : newtN a / z ≤ m) : newtF a z < z := by
  unfold newtF
  omega

/-- Linear consequence for the far-above case of E3 (no `/`/`%` terms). -/
theorem aux_E3big (V z m : Nat) (hcon : V + z ≤ 2 * m - 1) (hbig : 2 * m ≤ z)
    (hm1' : 1 ≤ m) : False := by
  omega

/-- Linear consequence for the main case of E3 (no `/`/`%` terms). -/
theorem aux_E3main (m z A B Q R DS E F : Nat)
    (hF : 1 ≤ F)
    (e5 : A ≤ Q + R) (hqz : Q ≤ DS) (e3 : DS + B = E)
    (e4 : E + z = 2 * F) (ham : 2 * F ≤ A + B) (hr1 : R + 1 ≤ z) : False := by
  omega

/-- E3: the Newton step never goes below the floor (for a positive iterate). -/
theorem newt_ge {a m z : Nat} (hm1 : m * m ≤ newtN a)
    (ham : 2 * (m * z) ≤ m * m + z * z) (hz : 0 < z) : m ≤ newtF a z := by
  by_cases hm0 : m = 0
  · subst hm0; exact Nat.zero_le _
  · have hm1' : 1 ≤ m := by omega
    have hz1 : 1 ≤ z := by omega
    have hm11 : 2 * m - 1 + 1 = 2 * m := by omega
    have hF : 1 ≤ m * z := by
      have h := Nat.mul_le_mul hm1' hz1
      rwa [Nat.one_mul] at h
    have eF : newtF a z = (newtN a / z + z) / 2 := rfl
    by_cases hle : m ≤ (newtN a / z + z) / 2
    · rw [eF]; exact hle
    · exfalso
      have hcon : newtN a / z + z ≤ 2 * m - 1 := by omega
      by_cases hbig : 2 * m ≤ z
      · exact aux_E3big _ _ _ hcon hbig hm1'
      · have hzz : z ≤ 2 * m - 1 := by omega
        have hq : newtN a / z ≤ 2 * m - 1 - z := by omega
        have hmod := Nat.div_add_mod (newtN a) z
        have hr := Nat.mod_lt (newtN a) hz
        have hqz : newtN a / z * z ≤ (2 * m - 1 - z) * z :=
          Nat.mul_le_mul_right _ hq
        have e1 : (2 * m - 1 - z) * z = (2 * m - 1) * z - z * z :=
          Nat.sub_mul _ _ _
        have e2 : z * z ≤ (2 * m - 1) * z :=
          Nat.mul_le_mul_right _ hzz
        have e3 : (2 * m - 1 - z) * z + z * z = (2 * m - 1) * z := by
          rw [e1, Nat.sub_add_cancel e2]
        have h1 : (2 * m - 1 + 1) * z = 2 * (m * z) := by
          rw [hm11]; exact Nat.mul_assoc _ _ _
        have h2 : ((2 * m - 1) + 1) * z = (2 * m - 1) * z + 1 * z :=
          Nat.add_mul _ _ _
        rw [Nat.one_mul] at h2
        have e4 : (2 * m - 1) * z + z = 2 * (m * z) := by
          rw [← h2]; exact h1
        have hmod' : newtN a / z * z + newtN a % z = newtN a := by
          rw [Nat.mul_comm (newtN a / z) z]; exact hmod
        have e5 : m * m ≤ newtN a / z * z + newtN a % z := by
          rw [hmod']; exact hm1
        have hr1 : newtN a % z + 1 ≤ z := by omega
        exact aux_E3main m z _ _ _ _ _ _ _ hF e5 hqz e3 e4 ham hr1

/-- E5: one step from `m + 1` lands exactly on `m`. -/
theorem newt_succ {a m : Nat} (hm1 : m * m ≤ newtN a)
    (hm2 : newtN a < (m + 1) * (m + 1)) : newtF a (m + 1) = m := by
  have hE2 : newtF a (m + 1) < m + 1 :=
    newt_lt hm2 (Nat.le_refl _) (newt_div_le hm2 (Nat.le_refl _))
  have hE3 : m ≤ newtF a (m + 1) :=
    newt_ge hm1 (two_mul_le_add_sq m (m + 1)) (by omega)
  omega

/-- E1b: the quotient at `m` itself is at most `m + 2`. -/
theorem newt_div_at {a m : Nat} (hm1 : m * m ≤ newtN a)
    (hm2 : newtN a < (m + 1) * (m + 1)) (hmpos : 1 ≤ m) :
    newtN a / m ≤ m + 2 := by
  by_cases h : newtN a / m ≤ m + 2
  · exact h
  · exfalso
    have h' : m + 3 ≤ newtN a / m := by omega
    have hle : (m + 3) * m ≤ newtN a :=
      (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp h'
    have eX : (m + 3) * m = m * m + 3 * m := Nat.add_mul _ _ _
    have eY : (m + 1) * (m + 1) = m * m + 2 * m + 1 := sq_succ_eq m
    omega

/-- E6: one step from `m` stays in `{m, m + 1}`. -/
theorem newt_at {a m : Nat} (hm1 : m * m ≤ newtN a)
    (hm2 : newtN a < (m + 1) * (m + 1))
    (ham : ∀ z, 2 * (m * z) ≤ m * m + z * z) (hmpos : 1 ≤ m) :
    newtF a m = m ∨ newtF a m = m + 1 := by
  have hE3 : m ≤ newtF a m := newt_ge hm1 (ham m) hmpos
  have hle : newtF a m ≤ m + 1 := by
    have hN : newtN a / m ≤ m + 2 := newt_div_at hm1 hm2 hmpos
    unfold newtF
    omega
  omega

/-- The step at `0` is `0`. -/
theorem newtF_zero (a : Nat) : newtF a 0 = 0 := by
  unfold newtF newtN
  rw [Nat.div_zero, Nat.add_zero, Nat.zero_div]

/-- Fixed points of the step are the floor. -/
theorem newt_fixed_eq {a m v : Nat} (hm1 : m * m ≤ newtN a)
    (hm2 : newtN a < (m + 1) * (m + 1))
    (hamv : 2 * (m * v) ≤ m * m + v * v) (hv1 : 1 ≤ v)
    (hfix : newtF a v = v) : v = m := by
  have hE3 : m ≤ newtF a v := newt_ge hm1 hamv (by omega)
  have hmv : m ≤ v := by omega
  by_cases h : v ≤ m
  · omega
  · exfalso
    have h1 : m + 1 ≤ v := by omega
    have hE2 : newtF a v < v :=
      newt_lt hm2 h1 (newt_div_le hm2 h1)
    omega

/-- Positivity: every orbit value is at least `1`. -/
theorem newt_pos {a : Nat} (ha : 1 ≤ a) : ∀ i, 1 ≤ newtSeq a i := by
  have hN : 1 ≤ newtN a := by
    have h2 : 1 * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha
    unfold newtN
    omega
  intro i
  induction i with
  | zero => show 1 ≤ newtS a; unfold newtS; omega
  | succ n ih =>
    have e : newtSeq a (n + 1) = newtF a (newtSeq a n) := rfl
    rw [e]
    unfold newtF
    by_cases hz1 : newtSeq a n = 1
    · rw [hz1, Nat.div_one]
      omega
    · have hz2 : 2 ≤ newtSeq a n := by omega
      have h2 : 1 ≤ newtSeq a n / 2 := by omega
      have h3 : newtSeq a n / 2 ≤ (newtN a / newtSeq a n + newtSeq a n) / 2 :=
        Nat.div_le_div_right (Nat.le_add_left _ _)
      exact Nat.le_trans h2 h3

/-- E4 (halving): well above the floor, the excess at least halves each step. -/
theorem newt_half {a m z : Nat} (hm2 : newtN a < (m + 1) * (m + 1))
    (hz : m + 2 ≤ z) : newtF a z - m ≤ (z - m) / 2 := by
  have h1 : newtN a / z ≤ m := newt_div_le hm2 (by omega)
  have hmw : m ≤ (m + z) / 2 := by
    have hle : (m + m) / 2 ≤ (m + z) / 2 :=
      Nat.div_le_div_right (by omega : m + m ≤ m + z)
    have e : (m + m) / 2 = m := by omega
    omega
  have hle : newtF a z ≤ (m + z) / 2 := by
    unfold newtF
    exact Nat.div_le_div_right (by omega : newtN a / z + z ≤ m + z)
  have h2 : (m + z) / 2 * 2 ≤ m + z := Nat.div_mul_le_self _ _
  have h3 : ((m + z) / 2 - m) * 2 ≤ z - m := by
    have hwm' : m + ((m + z) / 2 - m) = (m + z) / 2 := by omega
    have e : 2 * ((m + z) / 2) ≤ m + z := by omega
    have h6 : 2 * (m + ((m + z) / 2 - m)) ≤ m + z := by omega
    omega
  have h4 : (m + z) / 2 - m ≤ (z - m) / 2 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr h3
  have hle' : newtF a z - m ≤ (m + z) / 2 - m :=
    Nat.sub_le_sub_right hle _
  omega

/-! ## The exact floor and its basic bounds -/

/-- The exact floor of the scaled radicand. -/
def flr (a : Nat) : Nat := Nat.sqrt (newtN a)

theorem flr_le (a : Nat) : flr a * flr a ≤ newtN a := Nat.sqrt_le _

theorem flr_lt (a : Nat) : newtN a < (flr a + 1) * (flr a + 1) := by
  have h := Nat.lt_succ_sqrt (newtN a)
  rw [Nat.succ_eq_add_one] at h
  exact h

/-- A natural below the radicand is below the square root. -/
theorem sqrt_le_of_sq_le {N b : Nat} (h : b * b ≤ N) : b ≤ Nat.sqrt N := by
  rcases Nat.lt_or_ge b (Nat.sqrt N) with hle | hge
  · exact Nat.le_of_lt hle
  · by_cases h2 : Nat.sqrt N + 1 ≤ b
    · exfalso
      have h3 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ b * b := Nat.mul_le_mul h2 h2
      have h4 := Nat.lt_succ_sqrt N
      rw [Nat.succ_eq_add_one] at h4
      omega
    · omega

/-- For a positive input, the floor is positive. -/
theorem flr_pos {a : Nat} (ha : 1 ≤ a) : 1 ≤ flr a := by
  apply sqrt_le_of_sq_le
  have h1 : (1 : Nat) * 1 ≤ 1 * 10 ^ 10 := by decide
  have h10 : (1 : Nat) * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha
  have hN : newtN a = a * 10 ^ 10 := rfl
  omega

/-- The seed is above the floor. -/
theorem seed_ge_flr (a : Nat) : flr a ≤ newtS a := by
  by_cases h : flr a ≤ newtS a
  · exact h
  · exfalso
    have hs : newtS a + 1 ≤ flr a := by omega
    have hsq : (newtS a + 1) * (newtS a + 1) ≤ flr a * flr a :=
      Nat.mul_le_mul hs hs
    have hle : (newtS a + 1) * (newtS a + 1) ≤ newtN a :=
      Nat.le_trans hsq (flr_le a)
    have eS : newtS a = a / 2 + 5 * 10 ^ 9 := rfl
    have hN : newtN a = a * 10 ^ 10 := rfl
    have hmod := Nat.div_add_mod a 2
    have hr : a % 2 < 2 := Nat.mod_lt _ (by decide)
    have ham := two_mul_le_add_sq (a / 2) (5 * 10 ^ 9)
    have e1 : (a / 2 + 5 * 10 ^ 9) * (a / 2 + 5 * 10 ^ 9) =
        (a / 2) * (a / 2 + 5 * 10 ^ 9) + (5 * 10 ^ 9) * (a / 2 + 5 * 10 ^ 9) :=
      Nat.add_mul _ _ _
    have e2 : (a / 2) * (a / 2 + 5 * 10 ^ 9) =
        (a / 2) * (a / 2) + (a / 2) * (5 * 10 ^ 9) :=
      Nat.mul_add _ _ _
    have e3 : (5 * 10 ^ 9) * (a / 2 + 5 * 10 ^ 9) =
        (5 * 10 ^ 9) * (a / 2) + (5 * 10 ^ 9) * (5 * 10 ^ 9) :=
      Nat.mul_add _ _ _
    have ec : (5 * 10 ^ 9) * (a / 2) = (a / 2) * (5 * 10 ^ 9) := Nat.mul_comm _ _
    have eSS : newtS a * newtS a = (a / 2 + 5 * 10 ^ 9) * (a / 2 + 5 * 10 ^ 9) := rfl
    have eSq := sq_succ_eq (newtS a)
    omega

/-- The floor fits in a decimal. -/
theorem flr_le_MAX {a : Nat} (h : a ≤ 2 ^ 167 - 1) : flr a ≤ 2 ^ 167 - 1 := by
  by_cases hle : flr a ≤ 2 ^ 167 - 1
  · exact hle
  · exfalso
    have h1 : 2 ^ 167 - 1 + 1 ≤ flr a := by omega
    have h2 : (2 ^ 167 - 1 + 1) * (2 ^ 167 - 1 + 1) ≤ flr a * flr a :=
      Nat.mul_le_mul h1 h1
    have h4 : newtN a = a * 10 ^ 10 := rfl
    have h5 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 := Nat.mul_le_mul_right _ h
    have key : (2 ^ 167 - 1) * 10 ^ 10 < (2 ^ 167 - 1 + 1) * (2 ^ 167 - 1 + 1) := by
      decide
    have h3 := flr_le a
    omega

/-- The floor is far below `2^101`. -/
theorem flr_lt_B {a : Nat} (h : a ≤ 2 ^ 167 - 1) : flr a < 2 ^ 101 := by
  by_cases hle : flr a < 2 ^ 101
  · exact hle
  · exfalso
    have h1 : 2 ^ 101 ≤ flr a := by omega
    have h2 : (2 ^ 101) * (2 ^ 101) ≤ flr a * flr a := Nat.mul_le_mul h1 h1
    have h4 : newtN a = a * 10 ^ 10 := rfl
    have h5 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 := Nat.mul_le_mul_right _ h
    have key : (2 ^ 167 - 1) * 10 ^ 10 < (2 ^ 101) * (2 ^ 101) := by decide
    have h3 := flr_le a
    omega

/-! ## Orbit bounds: the orbit stays above the floor and near the seed -/

/-- Every orbit value is at least the floor. -/
theorem newt_ge_all {a : Nat} (ha : 1 ≤ a) : ∀ i, flr a ≤ newtSeq a i := by
  intro i
  induction i with
  | zero => show flr a ≤ newtS a; exact seed_ge_flr a
  | succ n ih =>
    have e : newtSeq a (n + 1) = newtF a (newtSeq a n) := rfl
    rw [e]
    have hpos : 0 < newtSeq a n := by have := newt_pos ha n; omega
    exact newt_ge (flr_le a) (two_mul_le_add_sq _ _) hpos

/-- Every orbit value is at most one above the seed. -/
theorem newt_le_seed1 {a : Nat} (ha : 1 ≤ a) : ∀ i, newtSeq a i ≤ newtS a + 1 := by
  have hflr : 1 ≤ flr a := flr_pos ha
  have hge := newt_ge_all ha
  have hseed := seed_ge_flr a
  have hm1 := flr_le a
  have hm2 := flr_lt a
  intro i
  induction i with
  | zero => show newtS a ≤ newtS a + 1; omega
  | succ n ih =>
    have e : newtSeq a (n + 1) = newtF a (newtSeq a n) := rfl
    rw [e]
    have hgn := hge n
    by_cases heq : newtSeq a n = flr a
    · rw [heq]
      rcases newt_at hm1 hm2 (fun z => two_mul_le_add_sq _ _) hflr with h1 | h1
      · omega
      · omega
    · have hle : newtF a (newtSeq a n) < newtSeq a n :=
        newt_lt hm2 (by omega) (newt_div_le hm2 (by omega))
      omega

/-- The Newton-step inputs always fit in a decimal. -/
theorem qz_bound {a : Nat} (hM : a ≤ 2 ^ 167 - 1) (ha : 1 ≤ a)
    {z : Nat} (hlo : flr a ≤ z) (hhi : z ≤ newtS a + 1) :
    newtN a / z + z ≤ 2 ^ 167 - 1 := by
  have hm1 := flr_le a
  have hm2 := flr_lt a
  have hflr : 1 ≤ flr a := flr_pos ha
  have hB : flr a < 2 ^ 101 := flr_lt_B hM
  have hdiv := Nat.div_le_div_right (c := 2) hM
  have eS : newtS a = a / 2 + 5 * 10 ^ 9 := rfl
  by_cases heq : z = flr a
  · subst heq
    have hN := newt_div_at hm1 hm2 hflr
    have e2 : 2 * 2 ^ 101 + 2 ≤ 2 ^ 167 - 1 := by decide
    omega
  · have hgt : flr a + 1 ≤ z := by omega
    have hq := newt_div_le hm2 hgt
    have e : (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 1 + 2 ^ 101 ≤ 2 ^ 167 - 1 := by decide
    omega

/-! ## Decay: the orbit reaches `{floor, floor + 1}` within 255 steps -/

/-- Either the orbit has hit `floor + 1` by step `k`, or the excess over the
floor at step `k` is the initial excess halved `k` times. -/
theorem decay_dich {a : Nat} (ha : 1 ≤ a) (k : Nat) :
    (∃ i, i ≤ k ∧ newtSeq a i ≤ flr a + 1) ∨
      newtSeq a k - flr a ≤ (newtSeq a 0 - flr a) / 2 ^ k := by
  have hm2 := flr_lt a
  induction k with
  | zero =>
    refine Or.inr ?_
    rw [Nat.pow_zero, Nat.div_one]
    exact Nat.le_refl _
  | succ k ih =>
    rcases ih with ⟨i, hi, hsmall⟩ | hbig
    · exact Or.inl ⟨i, by omega, hsmall⟩
    · by_cases hle : newtSeq a k ≤ flr a + 1
      · exact Or.inl ⟨k, by omega, hle⟩
      · have h2 : flr a + 2 ≤ newtSeq a k := by omega
        have hstep := newt_half hm2 h2
        have e : newtSeq a (k + 1) = newtF a (newtSeq a k) := rfl
        have hmono : (newtSeq a k - flr a) / 2 ≤ ((newtSeq a 0 - flr a) / 2 ^ k) / 2 :=
          Nat.div_le_div_right hbig
        have ediv : ((newtSeq a 0 - flr a) / 2 ^ k) / 2 =
            (newtSeq a 0 - flr a) / 2 ^ (k + 1) := by
          rw [Nat.div_div_eq_div_mul]
          have e2 : 2 ^ (k + 1) = 2 ^ k * 2 := by
            rw [← Nat.succ_eq_add_one]
            exact Nat.pow_succ _ _
          rw [e2]
        refine Or.inr ?_
        rw [e]
        omega

/-- The initial excess is below `2^255`. -/
theorem E0_small {a : Nat} (hM : a ≤ 2 ^ 167 - 1) :
    newtSeq a 0 - flr a < 2 ^ 255 := by
  have e : (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 < 2 ^ 255 := by decide
  have hdiv := Nat.div_le_div_right (c := 2) hM
  have eS : newtS a = a / 2 + 5 * 10 ^ 9 := rfl
  have e0 : newtSeq a 0 = newtS a := rfl
  omega

/-- The orbit hits `floor + 1` within 255 steps. -/
theorem hit_small {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    ∃ i, i ≤ 255 ∧ newtSeq a i ≤ flr a + 1 := by
  have hd := decay_dich ha 255
  have hE := E0_small hM
  have h0 : (newtSeq a 0 - flr a) / 2 ^ 255 = 0 :=
    Nat.div_eq_of_lt hE
  rcases hd with ⟨i, hi, hs⟩ | hbig
  · exact ⟨i, hi, hs⟩
  · refine ⟨255, Nat.le_refl _, ?_⟩
    have hge := newt_ge_all ha 255
    rw [h0] at hbig
    omega

/-- Once in `{floor, floor + 1}`, the orbit stays there. -/
theorem stay_small {a : Nat} (ha : 1 ≤ a) {i t : Nat}
    (h : newtSeq a i = flr a ∨ newtSeq a i = flr a + 1) :
    newtSeq a (i + t) = flr a ∨ newtSeq a (i + t) = flr a + 1 := by
  have hm1 := flr_le a
  have hm2 := flr_lt a
  have hflr : 1 ≤ flr a := flr_pos ha
  induction t with
  | zero =>
    have e : i + 0 = i := by omega
    rw [e]
    exact h
  | succ t ih =>
    have e : i + (t + 1) = (i + t) + 1 := by omega
    rw [e]
    have es : newtSeq a ((i + t) + 1) = newtF a (newtSeq a (i + t)) := rfl
    rw [es]
    rcases ih with h1 | h1
    · rw [h1]
      exact newt_at hm1 hm2 (fun z => two_mul_le_add_sq _ _) hflr
    · rw [h1]
      have hs := newt_succ hm1 hm2
      rw [hs]
      exact Or.inl rfl

/-! ## Loop correspondence: the decimal loop follows the Newton orbit -/

/-- The decimal loop from two consecutive orbit values either stops at a fixed
point of the Newton step or runs `n` steps along the orbit. -/
theorem loop_orbit {a : Nat} (hM : a ≤ 2 ^ 167 - 1) (ha : 1 ≤ a) :
    ∀ (n j : Nat),
    (∃ k, loop (a : Int) n ((newtSeq a j : Nat) : Int) ((newtSeq a (j + 1) : Nat) : Int) =
      some ((((newtSeq a k : Nat)) : Int), (((newtSeq a k : Nat)) : Int)) ∧
      newtF a (newtSeq a k) = newtSeq a k) ∨
    loop (a : Int) n ((newtSeq a j : Nat) : Int) ((newtSeq a (j + 1) : Nat) : Int) =
      some ((((newtSeq a (j + n) : Nat)) : Int), (((newtSeq a (j + n + 1) : Nat)) : Int)) := by
  have hge := newt_ge_all ha
  have hle := newt_le_seed1 ha
  have hm2 := flr_lt a
  intro n
  induction n with
  | zero =>
    intro j
    exact Or.inr rfl
  | succ n ih =>
    intro j
    by_cases heq : newtSeq a (j + 1) = newtSeq a j
    · refine Or.inl ⟨j, ?_, ?_⟩
      · have hc : (((newtSeq a (j + 1) : Nat)) : Int) = (((newtSeq a j : Nat)) : Int) := by
          rw [heq]
        rw [hc]
        exact loop_stop _ _ _
      · have e : newtSeq a (j + 1) = newtF a (newtSeq a j) := rfl
        omega
    · have hpos : 0 < newtSeq a (j + 1) := by have := newt_pos ha (j + 1); omega
      have hne : newtSeq a (j + 1) ≠ newtSeq a j := heq
      have hb : a * 10 ^ 10 / newtSeq a (j + 1) + newtSeq a (j + 1) ≤ 2 ^ 167 - 1 :=
        qz_bound hM ha (hge (j + 1)) (hle (j + 1))
      have hstep := loop_step (a := a) (y := newtSeq a j) (z := newtSeq a (j + 1)) n hpos hne hb
      have hstep2 : loop (a : Int) (n + 1) ((newtSeq a j : Nat) : Int)
          ((newtSeq a (j + 1) : Nat) : Int) =
          loop (a : Int) n ((newtSeq a (j + 1) : Nat) : Int)
            ((newtSeq a (j + 1 + 1) : Nat) : Int) := hstep
      rw [hstep2]
      rcases ih (j + 1) with ⟨k, hk1, hk2⟩ | hrun
      · refine Or.inl ⟨k, ?_, hk2⟩
        exact hk1
      · refine Or.inr ?_
        have e1 : j + 1 + n = j + (n + 1) := by omega
        rw [e1] at hrun
        exact hrun

/-- The full 256-iteration loop from the seed ends with minimum exactly the floor. -/
theorem loop_final_min {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    ∃ u v : Nat, loop (a : Int) 256 ((a : Nat) : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) =
      some ((((u : Nat)) : Int), (((v : Nat)) : Int)) ∧ Nat.min u v = flr a := by
  have hge := newt_ge_all ha
  have hpos1 : 1 ≤ flr a := flr_pos ha
  have hm1 := flr_le a
  have hm2 := flr_lt a
  have eS : newtS a = a / 2 + 5 * 10 ^ 9 := rfl
  by_cases heq : a / 2 + 5 * 10 ^ 9 = a
  · -- The seed equals the input: the loop stops immediately at `(a, a)`, and `a` is the floor.
    have hc : (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) = (((a : Nat)) : Int) := by rw [heq]
    have hseed : flr a ≤ a := by
      have h := seed_ge_flr a
      omega
    have ha10 : a ≤ 10 ^ 10 := by omega
    have hN : newtN a = a * 10 ^ 10 := rfl
    have haa : a = flr a := by
      by_cases hle : a ≤ flr a
      · omega
      · exfalso
        have h1 : flr a + 1 ≤ a := by omega
        have h2 : (flr a + 1) * (flr a + 1) ≤ a * a := Nat.mul_le_mul h1 h1
        have h3 : a * a ≤ a * 10 ^ 10 := Nat.mul_le_mul_left _ ha10
        omega
    refine ⟨a, a, ?_, ?_⟩
    · rw [hc]
      exact loop_stop _ _ _
    · rw [← haa]
      exact Nat.min_eq_left (Nat.le_refl _)
  · -- Otherwise the first step enters the orbit, and the rest follows it.
    have hposS : 0 < a / 2 + 5 * 10 ^ 9 := by omega
    have hlo : flr a ≤ a / 2 + 5 * 10 ^ 9 := seed_ge_flr a
    have hhi : a / 2 + 5 * 10 ^ 9 ≤ newtS a + 1 := by omega
    have hb : a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9) + (a / 2 + 5 * 10 ^ 9) ≤ 2 ^ 167 - 1 :=
      qz_bound hM ha hlo hhi
    have hstep := loop_step (a := a) (y := a) (z := a / 2 + 5 * 10 ^ 9) 255 hposS heq hb
    have hstep2 : loop (a : Int) 256 ((a : Nat) : Int) (((a / 2 + 5 * 10 ^ 9 : Nat)) : Int) =
        loop (a : Int) 255 ((newtSeq a 0 : Nat) : Int) ((newtSeq a 1 : Nat) : Int) := hstep
    rw [hstep2]
    rcases loop_orbit hM ha 255 0 with ⟨k, hk1, hk2⟩ | hrun
    · -- Stopped at a fixed point, which is the floor.
      have hfix : newtSeq a k = flr a := by
        have hposk : 1 ≤ newtSeq a k := newt_pos ha k
        exact newt_fixed_eq hm1 hm2 (two_mul_le_add_sq _ _) hposk hk2
      refine ⟨newtSeq a k, newtSeq a k, hk1, ?_⟩
      rw [hfix]
      exact Nat.min_eq_left (Nat.le_refl _)
    · -- Ran to the end inside `{floor, floor + 1}`.
      obtain ⟨i, hi255, hsmall⟩ := hit_small ha hM
      have hgei : flr a ≤ newtSeq a i := hge i
      have hmem : newtSeq a i = flr a ∨ newtSeq a i = flr a + 1 := by omega
      have eA : i + (255 - i) = 0 + 255 := by omega
      have eB : i + (256 - i) = 0 + 255 + 1 := by omega
      have stay1 := stay_small ha (t := 255 - i) hmem
      have stay2 := stay_small ha (t := 256 - i) hmem
      rw [eA] at stay1
      rw [eB] at stay2
      have hcon : newtSeq a (0 + 255 + 1) = newtF a (newtSeq a (0 + 255)) := rfl
      refine ⟨newtSeq a (0 + 255), newtSeq a (0 + 255 + 1), hrun, ?_⟩
      rcases stay1 with h1 | h1
      · rw [h1]
        exact Nat.min_eq_left (hge _)
      · have h2 : newtSeq a (0 + 255 + 1) = flr a := by
          rw [h1] at hcon
          have hs := newt_succ hm1 hm2
          rw [hs] at hcon
          exact hcon
        rw [h1, h2]
        exact Nat.min_eq_right (by omega : flr a ≤ flr a + 1)

/-! ## The result is the floor, and the five required theorems -/

/-- The choice function applied to casts is the cast of the natural minimum. -/
theorem fin_min_cast {u v : Nat} :
    (if ((u : Nat) : Int) < ((v : Nat) : Int) then ((u : Nat) : Int) else ((v : Nat) : Int)) =
    (((Nat.min u v : Nat)) : Int) := by
  by_cases h : u < v
  · have hc : ((u : Nat) : Int) < ((v : Nat) : Int) := Int.ofNat_lt.mpr h
    rw [if_pos hc]
    congr 1
    exact (Nat.min_eq_left (Nat.le_of_lt h)).symm
  · have hc : ¬ ((u : Nat) : Int) < ((v : Nat) : Int) := by
      intro hc'
      exact h (Int.ofNat_lt.mp hc')
    rw [if_neg hc]
    congr 1
    exact (Nat.min_eq_right (by omega : v ≤ u)).symm

/-- On a positive decimal input, `sqrt` returns the floor of the scaled root. -/
theorem sqrt_eq_floor {a : Nat} (ha : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    sqrt ((a : Nat) : Int) = some ((((flr a : Nat))) : Int) := by
  have hpos : 0 < a := by omega
  have hloop := vyperSqrtWith_pos (fun y z => if y < z then y else z) hpos hM
  obtain ⟨u, v, hpair, hmin⟩ := loop_final_min ha hM
  have hsqrt : sqrt ((a : Nat) : Int) =
      vyperSqrtWith (fun y z => if y < z then y else z) ((a : Nat) : Int) := rfl
  rw [hsqrt, hloop, hpair]
  show Option.map (fun p : Int × Int => (if p.1 < p.2 then p.1 else p.2))
    (some ((((u : Nat)) : Int), (((v : Nat)) : Int))) = _
  show some ((if ((u : Nat) : Int) < ((v : Nat) : Int) then ((u : Nat) : Int)
    else ((v : Nat) : Int))) = _
  rw [fin_min_cast, hmin]

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith _ x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨fun y z => if y < z then y else z, fun x => rfl⟩

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx h
  unfold IsDecimal at hx
  obtain ⟨hmin, hmax⟩ := hx
  by_cases hneg : x < 0
  · have hn := req_sqrt_neg_reverts x hneg
    rw [hn] at h
    cases h
  · have hnn : 0 ≤ x := by omega
    by_cases hz : x = 0
    · subst hz
      have h0 : sqrt (0 : Int) = some 0 := rfl
      rw [h0] at h
      have hr : (0 : Int) = r := Option.some_inj.mp h
      rw [← hr]
      show (0 : Int) * 0 ≤ 0 * DIVISOR
      unfold DIVISOR
      decide
    · have hpos : 0 < x := by omega
      obtain ⟨a, ha | ha⟩ := Int.eq_nat_or_neg x
      · subst ha
        have hane : ((a : Nat) : Int) ≠ 0 := hz
        have hane0 : a ≠ 0 := by
          intro z
          rw [z] at hane
          simp at hane
        have ha1 : 1 ≤ a := Nat.pos_of_ne_zero hane0
        have hM : a ≤ 2 ^ 167 - 1 := by
          rw [max_decimal_eq] at hmax
          exact Int.ofNat_le.mp hmax
        have hval := sqrt_eq_floor ha1 hM
        rw [hval] at h
        have hr : (((flr a : Nat)) : Int) = r := Option.some_inj.mp h
        have key := flr_le a
        have hcast : ((flr a * flr a : Nat) : Int) ≤ ((newtN a : Nat) : Int) := by
          exact_mod_cast key
        have hN : newtN a = a * 10 ^ 10 := rfl
        rw [Int.natCast_mul] at hcast
        rw [hN, Int.natCast_mul, ← divisor_eq] at hcast
        rw [← hr]
        exact hcast
      · have hle : ((a : Nat) : Int) ≤ 0 := by omega
        have hx0 : x = 0 := by omega
        exact absurd hx0 hz

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx h
  unfold IsDecimal at hx
  obtain ⟨hmin, hmax⟩ := hx
  by_cases hneg : x < 0
  · have hn := req_sqrt_neg_reverts x hneg
    rw [hn] at h
    cases h
  · have hnn : 0 ≤ x := by omega
    by_cases hz : x = 0
    · subst hz
      have h0 : sqrt (0 : Int) = some 0 := rfl
      rw [h0] at h
      have hr : (0 : Int) = r := Option.some_inj.mp h
      rw [← hr]
      show (0 : Int) * DIVISOR < (0 + 1) * (0 + 1)
      unfold DIVISOR
      decide
    · have hpos : 0 < x := by omega
      obtain ⟨a, ha | ha⟩ := Int.eq_nat_or_neg x
      · subst ha
        have hane : ((a : Nat) : Int) ≠ 0 := hz
        have hane0 : a ≠ 0 := by
          intro z
          rw [z] at hane
          simp at hane
        have ha1 : 1 ≤ a := Nat.pos_of_ne_zero hane0
        have hM : a ≤ 2 ^ 167 - 1 := by
          rw [max_decimal_eq] at hmax
          exact Int.ofNat_le.mp hmax
        have hval := sqrt_eq_floor ha1 hM
        rw [hval] at h
        have hr : (((flr a : Nat)) : Int) = r := Option.some_inj.mp h
        have key := flr_lt a
        have hcast : ((newtN a : Nat) : Int) < (((flr a + 1) * (flr a + 1) : Nat) : Int) := by
          exact_mod_cast key
        have hN : newtN a = a * 10 ^ 10 := rfl
        have e1 : ((1 : Nat) : Int) = 1 := rfl
        rw [hN, Int.natCast_mul, Int.natCast_mul, Int.natCast_add, e1, ← divisor_eq] at hcast
        rw [← hr]
        exact hcast
      · have hle : ((a : Nat) : Int) ≤ 0 := by omega
        have hx0 : x = 0 := by omega
        exact absurd hx0 hz

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hnn
  unfold IsDecimal at hx
  obtain ⟨hmin, hmax⟩ := hx
  by_cases hz : x = 0
  · subst hz
    have h0 : sqrt (0 : Int) = some 0 := rfl
    rw [h0]
    rfl
  · have hpos : 0 < x := by omega
    obtain ⟨a, ha | ha⟩ := Int.eq_nat_or_neg x
    · subst ha
      have hM : a ≤ 2 ^ 167 - 1 := by
        rw [max_decimal_eq] at hmax
        exact Int.ofNat_le.mp hmax
      have hane0 : a ≠ 0 := by
        intro z
        rw [z] at hz
        simp at hz
      have ha1 : 1 ≤ a := Nat.pos_of_ne_zero hane0
      have hval := sqrt_eq_floor ha1 hM
      rw [hval]
      rfl
    · omega

end VyperSqrt

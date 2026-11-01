import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
/-!
Port of the code the Vyper compiler v0.4.0 (commit e9db8d9f7486eae38f5b86531629019ad28f514e)
inlines for the builtin `sqrt(d: decimal) -> decimal`, `vyper/builtins/functions.py`, class
`Sqrt` (lines 2117 to 2172), with the fix of pull request 4486 (released in v0.4.1): after
the loop, `if y < z: z = y`, i.e. the result is the smaller of the last two iterates.
-/
namespace VyperSqrt

open ProofForgeFin.Sqrt

/-- The deployed routine with the v0.4.1 fix: the smaller of the last two iterates. -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith _ x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt := by
  exact ⟨fun y z => if y < z then y else z, fun x => rfl⟩

/-! ## Pure-Nat Newton analysis

On non-negative decimals every decimal operation is the operation on natural numbers
(`ddiv_nat`, `dadd_nat`), the loop is the Newton step
`newton (x * 10^10) z = (z + x * 10^10 / z) / 2` from the seed `x / 2 + 5 * 10^9`.
We analyze that iteration on `Nat` first. -/

/-- The raw value whose root is wanted: `x * 10^10`. -/
def aval (x : Nat) : Nat := x * 10 ^ 10

/-- The seed `x / 2.0 + 0.5` on raw values. -/
def seedN (x : Nat) : Nat := x / 2 + 5 * 10 ^ 9

/-- Newton iteration done `n` times starting from `x`. -/
def iterNewton (a x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => iterNewton a (newton a x) n

/-- Unfolding once. -/
theorem iterNewton_succ (a x n : Nat) :
    iterNewton a x (n + 1) = iterNewton a (newton a x) n := rfl

/-- One more step at the end is one Newton step. -/
theorem newton_iter (a x n : Nat) :
    newton a (iterNewton a x n) = iterNewton a x (n + 1) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have e1 : iterNewton a x (n + 1) = iterNewton a (newton a x) n := rfl
    have e2 : iterNewton a x (n + 1 + 1) = iterNewton a (newton a x) (n + 1) := rfl
    rw [e1, ih]
    exact e2.symm

/-- `(s+1)^2` expanded. -/
theorem sq_succ_eq (s : Nat) : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-- The seed is near the root: `x * 10^10 < (seed + 1)^2`. -/
theorem aval_lt_seed_succ_sq (x : Nat) :
    aval x < (seedN x + 1) * (seedN x + 1) := by
  have hfour : 4 * (x / 2) * (5 * 10 ^ 9) ≤ seedN x * seedN x :=
    four_mul_le_sq _ _
  have hxm : x ≤ 2 * (x / 2) + 1 := by
    have hdm := Nat.div_add_mod x 2
    have hmod : x % 2 < 2 := Nat.mod_lt x (by decide)
    omega
  have hmul : x * 10 ^ 10 ≤ (2 * (x / 2) + 1) * 10 ^ 10 :=
    Nat.mul_le_mul hxm (Nat.le_refl _)
  have hexpand : (2 * (x / 2) + 1) * 10 ^ 10 = 4 * (x / 2) * (5 * 10 ^ 9) + 10 ^ 10 := by
    grind
  have h10 : (10 : Nat) ^ 10 ≤ 2 * seedN x := by
    have hle : 5 * 10 ^ 9 ≤ seedN x := Nat.le_add_left _ _
    omega
  have hsq := sq_succ_eq (seedN x)
  have hax : aval x = x * 10 ^ 10 := rfl
  omega

/-- The seed is above the root. -/
theorem seed_ge (x : Nat) : Nat.sqrt (aval x) ≤ seedN x := by
  have h := aval_lt_seed_succ_sq x
  have h2 : Nat.sqrt (aval x) < seedN x + 1 := sqrt_lt_of_lt_mul_self h
  omega

/-- The quotient `a / t` for `t` above the root is at most `s + 2`. -/
theorem qbound (a : Nat) {t : Nat} (hs1 : 1 ≤ Nat.sqrt a) (ht0 : 0 < t)
    (hts : Nat.sqrt a ≤ t) : a / t ≤ Nat.sqrt a + 2 := by
  have h1 : a < (Nat.sqrt a + 1) * (Nat.sqrt a + 1) := Nat.lt_succ_sqrt a
  have e1 := sq_succ_eq (Nat.sqrt a)
  have e2 : (Nat.sqrt a + 3) * Nat.sqrt a
      = Nat.sqrt a * Nat.sqrt a + 3 * Nat.sqrt a := by
    simp only [Nat.add_mul]
  have h3 : (Nat.sqrt a + 3) * Nat.sqrt a ≤ (Nat.sqrt a + 3) * t :=
    Nat.mul_le_mul (Nat.le_refl _) hts
  have h4 : a < (Nat.sqrt a + 3) * t := by omega
  have h5 : a / t < Nat.sqrt a + 3 := (Nat.div_lt_iff_lt_mul ht0).mpr h4
  omega

/-- Iterates stay positive and above the root. -/
theorem lo_pos (a : Nat) (hs1 : 1 ≤ Nat.sqrt a) (n x : Nat) (hx0 : 0 < x)
    (hxs : Nat.sqrt a ≤ x) :
    0 < iterNewton a x n ∧ Nat.sqrt a ≤ iterNewton a x n := by
  induction n generalizing x with
  | zero => exact ⟨hx0, hxs⟩
  | succ n ih =>
    have hy : Nat.sqrt a ≤ newton a x := sqrt_le_newton hx0
    have hy0 : 0 < newton a x := by omega
    have e : iterNewton a x (n + 1) = iterNewton a (newton a x) n := rfl
    rw [e]
    exact ih _ hy0 hy

/-- Iterates stay at or below `seed + 1`. -/
theorem traj_up (a seed : Nat) (hs1 : 1 ≤ Nat.sqrt a)
    (hs : Nat.sqrt a ≤ seed)
    (hq : ∀ t : Nat, 0 < t → Nat.sqrt a ≤ t → t ≤ seed + 1 → a / t ≤ Nat.sqrt a + 2)
    (n x : Nat) (hx0 : 0 < x) (hxs : Nat.sqrt a ≤ x) (hxu : x ≤ seed + 1) :
    iterNewton a x n ≤ seed + 1 := by
  induction n generalizing x with
  | zero => exact hxu
  | succ n ih =>
    have hy : Nat.sqrt a ≤ newton a x := sqrt_le_newton hx0
    have hq' : a / x ≤ Nat.sqrt a + 2 := hq x hx0 hxs hxu
    have hy0 : 0 < newton a x := by omega
    have hle : newton a x ≤ seed + 1 := by
      show (x + a / x) / 2 ≤ seed + 1
      omega
    have e : iterNewton a x (n + 1) = iterNewton a (newton a x) n := rfl
    rw [e]
    exact ih _ hy0 hy hle

/-- The seed is small. -/
theorem seed_bound (x : Nat) (hxb : x ≤ 2 ^ 167 - 1) :
    seedN x ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9 := by
  have h : x / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hxb
  have heq : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
  have h2 : seedN x = x / 2 + 5 * 10 ^ 9 := rfl
  omega

/-- The root is small: below `2^101`. -/
theorem sqrt_small {x : Nat} (hxb : x ≤ 2 ^ 167 - 1) :
    Nat.sqrt (aval x) < 2 ^ 101 := by
  apply sqrt_lt_two_pow
  show aval x < 2 ^ 202
  have hle : (10 : Nat) ^ 10 ≤ 2 ^ 34 := by decide
  have hx1 : x + 1 ≤ 2 ^ 167 := by omega
  have hax : aval x = x * 10 ^ 10 := rfl
  have e1 : x * 10 ^ 10 ≤ x * 2 ^ 34 := Nat.mul_le_mul (Nat.le_refl _) hle
  have hpos : 0 < (2 : Nat) ^ 34 := by decide
  have e2 : x * 2 ^ 34 < (x + 1) * 2 ^ 34 := by
    have e : (x + 1) * 2 ^ 34 = x * 2 ^ 34 + 2 ^ 34 := by grind
    omega
  have e3 : (x + 1) * 2 ^ 34 ≤ 2 ^ 167 * 2 ^ 34 := Nat.mul_le_mul hx1 (Nat.le_refl _)
  have e4 : (2 : Nat) ^ 167 * 2 ^ 34 = 2 ^ 201 := by decide
  have e5 : (2 : Nat) ^ 202 = 2 ^ 201 * 2 := by decide
  have hpos2 : 0 < (2 : Nat) ^ 201 := by decide
  omega

/-- The root is large: at least `10^5` for positive input. -/
theorem sqrt_big {x : Nat} (hx1 : 1 ≤ x) : 10 ^ 5 ≤ Nat.sqrt (aval x) := by
  apply le_sqrt_of_mul_self_le
  have h : (10 : Nat) ^ 5 * 10 ^ 5 = 10 ^ 10 := by decide
  have hax : aval x = x * 10 ^ 10 := rfl
  have h2 : (10 : Nat) ^ 10 ≤ aval x := by
    have hm : 1 * 10 ^ 10 ≤ x * 10 ^ 10 := Nat.mul_le_mul hx1 (Nat.le_refl _)
    rwa [Nat.one_mul] at hm
  omega

/-- Halving: after `k` steps the error above the root is at most `3`,
provided it starts below `2^k + 2`. -/
theorem halve (a : Nat) (hs1 : 1 ≤ Nat.sqrt a) (k : Nat) : ∀ x : Nat, 0 < x →
    Nat.sqrt a ≤ x → x - Nat.sqrt a ≤ 2 ^ k + 2 →
    iterNewton a x k - Nat.sqrt a ≤ 3 := by
  induction k with
  | zero =>
    intro x hx0 hxs herr
    have e : (2 : Nat) ^ 0 + 2 = 3 := by decide
    have ee : iterNewton a x 0 = x := rfl
    omega
  | succ k ih =>
    intro x hx0 hxs herr
    have hy : Nat.sqrt a ≤ newton a x := sqrt_le_newton hx0
    have hy0 : 0 < newton a x := by omega
    have hpow : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hhalf := newton_sub_sqrt_le_half hx0 hxs
    have herr_y : newton a x - Nat.sqrt a ≤ 2 ^ k + 2 := by
      rw [hpow] at herr
      omega
    have e : iterNewton a x (k + 1) = iterNewton a (newton a x) k := rfl
    rw [e]
    exact ih _ hy0 hy herr_y

/-- After 169 steps the iterate is at the root or the root plus one. -/
theorem reach169 {xraw : Nat} (hx1 : 1 ≤ xraw) (hxb : xraw ≤ 2 ^ 167 - 1) :
    Nat.sqrt (aval xraw) ≤ iterNewton (aval xraw) (seedN xraw) 169 ∧
    iterNewton (aval xraw) (seedN xraw) 169 ≤ Nat.sqrt (aval xraw) + 1 := by
  have hs5 : 10 ^ 5 ≤ Nat.sqrt (aval xraw) := sqrt_big hx1
  have hs1 : 1 ≤ Nat.sqrt (aval xraw) := by omega
  have hseed : Nat.sqrt (aval xraw) ≤ seedN xraw := seed_ge xraw
  have hseed0 : 0 < seedN xraw := by
    have hle : 5 * 10 ^ 9 ≤ seedN xraw := Nat.le_add_left _ _
    omega
  have hb := seed_bound xraw hxb
  have h5 : (5 : Nat) * 10 ^ 9 ≤ 2 ^ 166 := by decide
  have herr0 : seedN xraw - Nat.sqrt (aval xraw) ≤ 2 ^ 167 + 2 := by
    omega
  have h167 := halve (aval xraw) hs1 167 (seedN xraw) hseed0 hseed herr0
  have hlo167 := lo_pos (aval xraw) hs1 167 (seedN xraw) hseed0 hseed
  have ht168_eq : iterNewton (aval xraw) (seedN xraw) 168
      = newton (aval xraw) (iterNewton (aval xraw) (seedN xraw) 167) :=
    (newton_iter _ _ _).symm
  have ht168_0 : 0 < iterNewton (aval xraw) (seedN xraw) 168 := by
    rw [ht168_eq]
    have hle := sqrt_le_newton (a := aval xraw) hlo167.1
    omega
  have ht168_s : Nat.sqrt (aval xraw) ≤
      iterNewton (aval xraw) (seedN xraw) 168 := by
    rw [ht168_eq]
    exact sqrt_le_newton hlo167.1
  have herr168 : iterNewton (aval xraw) (seedN xraw) 168 -
      Nat.sqrt (aval xraw) ≤ 2 := by
    have hhalf := newton_sub_sqrt_le_half hlo167.1 hlo167.2
    rw [ht168_eq]
    omega
  have hsq : (iterNewton (aval xraw) (seedN xraw) 168 - Nat.sqrt (aval xraw)) *
      (iterNewton (aval xraw) (seedN xraw) 168 - Nat.sqrt (aval xraw)) ≤
      2 * Nat.sqrt (aval xraw) := by
    have h2 := Nat.mul_le_mul herr168 herr168
    have h3 : 2 * 2 ≤ 2 * Nat.sqrt (aval xraw) := by omega
    omega
  have ht169 := newton_le_sqrt_add_one ht168_0 ht168_s hsq
  have ht169_eq : iterNewton (aval xraw) (seedN xraw) 169
      = newton (aval xraw) (iterNewton (aval xraw) (seedN xraw) 168) :=
    (newton_iter _ _ _).symm
  have hlo169 := lo_pos (aval xraw) hs1 169 (seedN xraw) hseed0 hseed
  have hup169 : iterNewton (aval xraw) (seedN xraw) 169 ≤
      Nat.sqrt (aval xraw) + 1 := by
    rw [ht169_eq]
    exact ht169
  exact ⟨hlo169.2, hup169⟩

/-- From step 169 on, every iterate is at the root or the root plus one. -/
theorem mem_after {xraw : Nat} (hx1 : 1 ≤ xraw) (hxb : xraw ≤ 2 ^ 167 - 1)
    (j : Nat) : 169 ≤ j →
    Nat.sqrt (aval xraw) ≤ iterNewton (aval xraw) (seedN xraw) j ∧
    iterNewton (aval xraw) (seedN xraw) j ≤ Nat.sqrt (aval xraw) + 1 := by
  induction j with
  | zero =>
    intro hj
    exact absurd hj (by decide)
  | succ j ih =>
    intro hj
    by_cases hjj : 169 ≤ j
    · obtain ⟨h1, h2⟩ := ih hjj
      have hs1 : 1 ≤ Nat.sqrt (aval xraw) := by
        have h5 := sqrt_big hx1
        omega
      have hpos : 0 < iterNewton (aval xraw) (seedN xraw) j := by omega
      have hm := newton_of_mem hpos h1 h2
      have e : iterNewton (aval xraw) (seedN xraw) (j + 1)
          = newton (aval xraw) (iterNewton (aval xraw) (seedN xraw) j) :=
        (newton_iter _ _ _).symm
      rw [e]
      rcases hm with h | ⟨hyz, hnew, hmem⟩
      · omega
      · omega
    · have e : j + 1 = 169 := by omega
      rw [e]
      exact reach169 hx1 hxb

/-- The sum `a / t + t` that the loop adds stays in range. -/
theorem range_sum {xraw t : Nat} (hx1 : 1 ≤ xraw) (hxb : xraw ≤ 2 ^ 167 - 1)
    (ht0 : 0 < t) (hts : Nat.sqrt (aval xraw) ≤ t) (htu : t ≤ seedN xraw + 1) :
    aval xraw / t + t ≤ 2 ^ 167 - 1 := by
  have hs1 : 1 ≤ Nat.sqrt (aval xraw) := by
    have h5 := sqrt_big hx1
    omega
  have hq : aval xraw / t ≤ Nat.sqrt (aval xraw) + 2 := qbound _ hs1 ht0 hts
  have hsmall : Nat.sqrt (aval xraw) < 2 ^ 101 := sqrt_small hxb
  have hb : seedN xraw ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9 := seed_bound xraw hxb
  have h5 : (5 : Nat) * 10 ^ 9 + 2 ^ 101 + 3 ≤ 2 ^ 166 := by decide
  have hax : aval xraw = xraw * 10 ^ 10 := rfl
  omega

/-- The choice `if y < z then y else z` is the cast of `min`. -/
theorem fin_eq (Y Z : Nat) :
    (if (Y : Int) < (Z : Int) then (Y : Int) else (Z : Int)) =
      ((min Y Z : Nat) : Int) := by
  by_cases h : Y < Z
  · have h' : (Y : Int) < (Z : Int) := by exact_mod_cast h
    have hm : min Y Z = Y := Nat.min_eq_left (by omega)
    rw [if_pos h', hm]
  · have h' : ¬ (Y : Int) < (Z : Int) := by
      intro hc
      exact h (by exact_mod_cast hc)
    have hle : Z ≤ Y := by omega
    have hm : min Y Z = Z := Nat.min_eq_right hle
    rw [if_neg h', hm]

/-- The zero case. -/
theorem sqrt_zero : sqrt 0 = some 0 := by
  show vyperSqrtWith _ 0 = some 0
  unfold vyperSqrtWith
  rw [if_neg (by decide : ¬ (0 : Int) < 0), if_pos rfl]

/-- If the seed equals the input, both are the root. -/
theorem x_eq_seed {xraw : Nat} (hx1 : 1 ≤ xraw)
    (heq : xraw = xraw / 2 + 5 * 10 ^ 9) : xraw = Nat.sqrt (aval xraw) := by
  have hs1 : 1 ≤ Nat.sqrt (aval xraw) := by
    have h5 := sqrt_big hx1
    omega
  have hseed_eq : seedN xraw = xraw / 2 + 5 * 10 ^ 9 := rfl
  have hse : seedN xraw = xraw := by omega
  have hge : Nat.sqrt (aval xraw) ≤ xraw := by
    have h := seed_ge xraw
    omega
  have hle : xraw ≤ Nat.sqrt (aval xraw) := by
    apply le_sqrt_of_mul_self_le
    have hax : aval xraw = xraw * 10 ^ 10 := rfl
    rw [hax]
    have h10 : xraw ≤ 10 ^ 10 := by
      have h2 : 2 * (xraw / 2) ≤ xraw := by
        have h := Nat.div_mul_le_self xraw 2
        omega
      omega
    exact Nat.mul_le_mul (Nat.le_refl _) h10
  omega

/-- The loop follows the Newton iterates and its last two iterates
have minimum `Nat.sqrt (aval xraw)`. -/
theorem sim_aux {xraw : Nat} (hx1 : 1 ≤ xraw) (hxb : xraw ≤ 2 ^ 167 - 1) :
    ∀ (k j : Nat), j + k = 256 →
    ∃ Y Z : Nat, loop (xraw : Int) (256 - j)
        (if j = 0 then (xraw : Int)
          else ((iterNewton (aval xraw) (seedN xraw) (j - 1) : Nat) : Int))
        ((iterNewton (aval xraw) (seedN xraw) j : Nat) : Int) =
        some ((Y : Int), (Z : Int)) ∧ min Y Z = Nat.sqrt (aval xraw) := by
  intro k
  induction k with
  | zero =>
    intro j hjk
    have hj : j = 256 := by omega
    subst hj
    have hf : 256 - 256 = 0 := by decide
    have h255 := mem_after hx1 hxb 255 (by decide)
    have h256 := mem_after hx1 hxb 256 (by decide)
    have hcon : iterNewton (aval xraw) (seedN xraw) 256
        = newton (aval xraw) (iterNewton (aval xraw) (seedN xraw) 255) :=
      (newton_iter _ _ _).symm
    have hpos : 0 < iterNewton (aval xraw) (seedN xraw) 255 := by
      have h5 := sqrt_big hx1
      omega
    have hmin : min (iterNewton (aval xraw) (seedN xraw) 255)
        (iterNewton (aval xraw) (seedN xraw) 256) = Nat.sqrt (aval xraw) := by
      rw [hcon]
      exact min_newton_eq_sqrt hpos h255.1 h255.2
    refine ⟨iterNewton (aval xraw) (seedN xraw) 255,
      iterNewton (aval xraw) (seedN xraw) 256, ?_, hmin⟩
    rw [hf, if_neg (by decide : ¬ (256 : Nat) = 0),
      show (256 : Nat) - 1 = 255 from by decide]
    rfl
  | succ k ih =>
    intro j hjk
    have hs1 : 1 ≤ Nat.sqrt (aval xraw) := by
      have h5 := sqrt_big hx1
      omega
    have hseed : Nat.sqrt (aval xraw) ≤ seedN xraw := seed_ge xraw
    have hseed0 : 0 < seedN xraw := by
      have hle : 5 * 10 ^ 9 ≤ seedN xraw := Nat.le_add_left _ _
      omega
    have hq : ∀ t : Nat, 0 < t → Nat.sqrt (aval xraw) ≤ t → t ≤ seedN xraw + 1 →
        aval xraw / t ≤ Nat.sqrt (aval xraw) + 2 :=
      fun t ht0 hts htu => qbound _ hs1 ht0 hts
    by_cases hj0 : j = 0
    · subst hj0
      have hprev : (if (0 : Nat) = 0 then (xraw : Int)
          else ((iterNewton (aval xraw) (seedN xraw) (0 - 1) : Nat) : Int)) =
          (xraw : Int) := if_pos rfl
      have h0 : iterNewton (aval xraw) (seedN xraw) 0 = seedN xraw := rfl
      have hf0 : 256 - 0 = (256 - (0 + 1)) + 1 := by omega
      rw [hprev, h0, hf0]
      by_cases heq : ((seedN xraw : Nat) : Int) = (xraw : Int)
      · have hse : seedN xraw = xraw := Int.ofNat.inj heq
        have hse' : xraw = xraw / 2 + 5 * 10 ^ 9 := hse.symm
        have hxx : xraw = Nat.sqrt (aval xraw) := x_eq_seed hx1 hse'
        rw [heq, loop_stop]
        have hm0 : min xraw xraw = xraw := Nat.min_eq_left (Nat.le_refl _)
        refine ⟨xraw, xraw, rfl, ?_⟩
        rw [hm0]
        exact hxx
      · have hne : seedN xraw ≠ xraw := fun c => heq (by rw [c])
        have ht0 : 0 < seedN xraw := hseed0
        have h' : xraw * 10 ^ 10 / seedN xraw + seedN xraw ≤ 2 ^ 167 - 1 :=
          range_sum hx1 hxb ht0 hseed (Nat.le_succ _)
        have hstep := loop_step (a := xraw) (y := xraw) (z := seedN xraw)
          (256 - (0 + 1)) ht0 hne h'
        rw [hstep]
        have hcon : (xraw * 10 ^ 10 / seedN xraw + seedN xraw) / 2
            = iterNewton (aval xraw) (seedN xraw) (0 + 1) := by
          have e1 : iterNewton (aval xraw) (seedN xraw) (0 + 1)
              = newton (aval xraw) (seedN xraw) := rfl
          rw [e1]
          show (aval xraw / seedN xraw + seedN xraw) / 2 =
            (seedN xraw + aval xraw / seedN xraw) / 2
          rw [Nat.add_comm]
        rw [hcon]
        obtain ⟨Y, Z, hloop, hmin⟩ := ih (0 + 1) (by omega)
        rw [if_neg (by decide : ¬ (0 : Nat) + 1 = 0),
          show (0 : Nat) + 1 - 1 = 0 from by decide, h0] at hloop
        exact ⟨Y, Z, hloop, hmin⟩
    · have hj1 : 1 ≤ j := by omega
      have hprev : (if j = 0 then (xraw : Int)
          else ((iterNewton (aval xraw) (seedN xraw) (j - 1) : Nat) : Int))
          = ((iterNewton (aval xraw) (seedN xraw) (j - 1) : Nat) : Int) :=
        if_neg hj0
      have hf : 256 - j = (256 - (j + 1)) + 1 := by omega
      rw [hprev, hf]
      have e : j = (j - 1) + 1 := by omega
      have hcon2 : iterNewton (aval xraw) (seedN xraw) j
          = newton (aval xraw) (iterNewton (aval xraw) (seedN xraw) (j - 1)) := by
        rw [e]
        exact (newton_iter _ _ _).symm
      by_cases heq : ((iterNewton (aval xraw) (seedN xraw) j : Nat) : Int)
          = ((iterNewton (aval xraw) (seedN xraw) (j - 1) : Nat) : Int)
      · have hfix : newton (aval xraw) (iterNewton (aval xraw) (seedN xraw) (j - 1))
            = iterNewton (aval xraw) (seedN xraw) (j - 1) := by
          rw [← hcon2]
          exact Int.ofNat.inj heq
        have ht0 : 0 < iterNewton (aval xraw) (seedN xraw) (j - 1) := by
          have hlo := lo_pos (aval xraw) hs1 (j - 1) (seedN xraw) hseed0 hseed
          have h5 := sqrt_big hx1
          omega
        have hroot : iterNewton (aval xraw) (seedN xraw) (j - 1) =
            Nat.sqrt (aval xraw) := eq_sqrt_of_newton_eq_self ht0 hfix
        rw [heq, loop_stop]
        have hm0 : min (iterNewton (aval xraw) (seedN xraw) (j - 1))
            (iterNewton (aval xraw) (seedN xraw) (j - 1))
            = iterNewton (aval xraw) (seedN xraw) (j - 1) :=
          Nat.min_eq_left (Nat.le_refl _)
        refine ⟨_, _, rfl, ?_⟩
        rw [hm0]
        exact hroot
      · have hne : iterNewton (aval xraw) (seedN xraw) j
            ≠ iterNewton (aval xraw) (seedN xraw) (j - 1) :=
          fun c => heq (by rw [c])
        have ht0 : 0 < iterNewton (aval xraw) (seedN xraw) j :=
          (lo_pos (aval xraw) hs1 j (seedN xraw) hseed0 hseed).1
        have hts : Nat.sqrt (aval xraw) ≤ iterNewton (aval xraw) (seedN xraw) j :=
          (lo_pos (aval xraw) hs1 j (seedN xraw) hseed0 hseed).2
        have htu : iterNewton (aval xraw) (seedN xraw) j ≤ seedN xraw + 1 :=
          traj_up _ _ hs1 hseed hq j (seedN xraw) hseed0 hseed (Nat.le_succ _)
        have h' : xraw * 10 ^ 10 / iterNewton (aval xraw) (seedN xraw) j
            + iterNewton (aval xraw) (seedN xraw) j ≤ 2 ^ 167 - 1 :=
          range_sum hx1 hxb ht0 hts htu
        have hstep := loop_step (a := xraw)
          (y := iterNewton (aval xraw) (seedN xraw) (j - 1))
          (z := iterNewton (aval xraw) (seedN xraw) j)
          (256 - (j + 1)) ht0 hne h'
        rw [hstep]
        have hcon3 : iterNewton (aval xraw) (seedN xraw) (j + 1)
            = (xraw * 10 ^ 10 / iterNewton (aval xraw) (seedN xraw) j
              + iterNewton (aval xraw) (seedN xraw) j) / 2 := by
          have e2 : iterNewton (aval xraw) (seedN xraw) (j + 1)
              = newton (aval xraw) (iterNewton (aval xraw) (seedN xraw) j) :=
            (newton_iter _ _ _).symm
          rw [e2]
          show (iterNewton (aval xraw) (seedN xraw) j + aval xraw /
              iterNewton (aval xraw) (seedN xraw) j) / 2 =
            (aval xraw / iterNewton (aval xraw) (seedN xraw) j +
              iterNewton (aval xraw) (seedN xraw) j) / 2
          rw [Nat.add_comm]
        rw [← hcon3]
        obtain ⟨Y, Z, hloop, hmin⟩ := ih (j + 1) (by omega)
        have hj1' : (j + 1) - 1 = j := by omega
        rw [if_neg (by omega : ¬ j + 1 = 0), hj1'] at hloop
        exact ⟨Y, Z, hloop, hmin⟩

/-- The loop runs to completion and its last two iterates have minimum
`Nat.sqrt (aval xraw)`. -/
theorem loop_converges {xraw : Nat} (hx1 : 1 ≤ xraw) (hxb : xraw ≤ 2 ^ 167 - 1) :
    ∃ Y Z : Nat, loop (xraw : Int) 256 (xraw : Int)
      (((seedN xraw : Nat)) : Int) =
      some ((Y : Int), (Z : Int)) ∧ min Y Z = Nat.sqrt (aval xraw) := by
  have h := sim_aux hx1 hxb 256 0 (by omega)
  have h0 : iterNewton (aval xraw) (seedN xraw) 0 = seedN xraw := rfl
  have hf : 256 - 0 = 256 := by omega
  rw [if_pos rfl, h0, hf] at h
  exact h

/-- The value computed by `sqrt` on positive input is the exact root. -/
theorem sqrt_val {n : Nat} (hx1 : 1 ≤ n) (hxb : n ≤ 2 ^ 167 - 1) :
    sqrt (n : Int) = some ((Nat.sqrt (aval n) : Nat) : Int) := by
  show vyperSqrtWith (fun y z => if y < z then y else z) (n : Int) = _
  rw [vyperSqrtWith_pos _ (by omega) hxb]
  obtain ⟨Y, Z, hloop, hmin⟩ := loop_converges hx1 hxb
  have hseed : ((seedN n : Nat) : Int) = (((n / 2 + 5 * 10 ^ 9 : Nat)) : Int) := rfl
  rw [← hseed, hloop, ← hmin]
  show some (if (Y : Int) < (Z : Int) then (Y : Int) else (Z : Int)) =
    some ((min Y Z : Nat) : Int)
  rw [fin_eq]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hsqrt
  by_cases hxneg : x < 0
  · have hnone := req_sqrt_neg_reverts x hxneg
    rw [hnone] at hsqrt
    cases hsqrt
  · have hx0 : 0 ≤ x := by omega
    obtain ⟨n, rfl⟩ : ∃ n : Nat, x = (n : Int) := ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
    have hxb : n ≤ 2 ^ 167 - 1 := by
      have h2 := hx.2
      rw [max_decimal_eq] at h2
      exact_mod_cast h2
    by_cases hn : n = 0
    · subst hn
      have e0 : ((0 : Nat) : Int) = 0 := by simp
      have hs0 : sqrt ((0 : Nat) : Int) = some 0 := by
        rw [e0]
        exact sqrt_zero
      rw [hs0] at hsqrt
      have hr : r = 0 := (Option.some_inj.mp hsqrt).symm
      subst hr
      rw [e0]
      simp
    · have hn1 : 1 ≤ n := by omega
      have hval := sqrt_val hn1 hxb
      rw [hval] at hsqrt
      have hr : r = ((Nat.sqrt (aval n) : Nat) : Int) :=
        (Option.some_inj.mp hsqrt).symm
      subst hr
      have hle : Nat.sqrt (aval n) * Nat.sqrt (aval n) ≤ aval n := Nat.sqrt_le _
      have e : ((aval n : Nat) : Int) = (n : Int) * DIVISOR := by
        show ((n * 10 ^ 10 : Nat) : Int) = _
        rw [divisor_eq]
        exact Int.natCast_mul _ _
      have hleI : ((Nat.sqrt (aval n) : Nat) : Int) * ((Nat.sqrt (aval n) : Nat) : Int)
          ≤ (n : Int) * DIVISOR := by
        rw [← e]
        have hcast : ((Nat.sqrt (aval n) * Nat.sqrt (aval n) : Nat) : Int)
            = ((Nat.sqrt (aval n) : Nat) : Int) * ((Nat.sqrt (aval n) : Nat) : Int) := by
          exact_mod_cast rfl
        rw [← hcast]
        exact_mod_cast hle
      exact hleI

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hsqrt
  by_cases hxneg : x < 0
  · have hnone := req_sqrt_neg_reverts x hxneg
    rw [hnone] at hsqrt
    cases hsqrt
  · have hx0 : 0 ≤ x := by omega
    obtain ⟨n, rfl⟩ : ∃ n : Nat, x = (n : Int) := ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
    have hxb : n ≤ 2 ^ 167 - 1 := by
      have h2 := hx.2
      rw [max_decimal_eq] at h2
      exact_mod_cast h2
    by_cases hn : n = 0
    · subst hn
      have e0 : ((0 : Nat) : Int) = 0 := by simp
      have hs0 : sqrt ((0 : Nat) : Int) = some 0 := by
        rw [e0]
        exact sqrt_zero
      rw [hs0] at hsqrt
      have hr : r = 0 := (Option.some_inj.mp hsqrt).symm
      subst hr
      rw [e0]
      simp
    · have hn1 : 1 ≤ n := by omega
      have hval := sqrt_val hn1 hxb
      rw [hval] at hsqrt
      have hr : r = ((Nat.sqrt (aval n) : Nat) : Int) :=
        (Option.some_inj.mp hsqrt).symm
      subst hr
      have hlt : aval n < (Nat.sqrt (aval n) + 1) * (Nat.sqrt (aval n) + 1) :=
        Nat.lt_succ_sqrt _
      have e : ((aval n : Nat) : Int) = (n : Int) * DIVISOR := by
        show ((n * 10 ^ 10 : Nat) : Int) = _
        rw [divisor_eq]
        exact Int.natCast_mul _ _
      have e2 : ((Nat.sqrt (aval n) + 1 : Nat) : Int)
          = ((Nat.sqrt (aval n) : Nat) : Int) + 1 := by
        exact_mod_cast rfl
      have hltI : (n : Int) * DIVISOR
          < (((Nat.sqrt (aval n) : Nat) : Int) + 1) *
            (((Nat.sqrt (aval n) : Nat) : Int) + 1) := by
        rw [← e, ← e2]
        exact_mod_cast hlt
      exact hltI

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hx0
  obtain ⟨n, rfl⟩ : ∃ n : Nat, x = (n : Int) := ⟨x.toNat, (Int.toNat_of_nonneg hx0).symm⟩
  have hxb : n ≤ 2 ^ 167 - 1 := by
    have h2 := hx.2
    rw [max_decimal_eq] at h2
    exact_mod_cast h2
  by_cases hn : n = 0
  · subst hn
    have e0 : ((0 : Nat) : Int) = 0 := by simp
    show (sqrt ((0 : Nat) : Int)).isSome
    rw [e0, sqrt_zero]
    rfl
  · have hn1 : 1 ≤ n := by omega
    have hloop := loop_converges hn1 hxb
    show (sqrt (n : Int)).isSome
    show (vyperSqrtWith (fun y z => if y < z then y else z) (n : Int)).isSome
    rw [vyperSqrtWith_pos _ (by omega) hxb]
    have hseed : ((seedN n : Nat) : Int) = (((n / 2 + 5 * 10 ^ 9 : Nat)) : Int) := rfl
    rw [hseed] at hloop
    obtain ⟨Y, Z, hloop2, hmin⟩ := hloop
    rw [hloop2]
    rfl

end VyperSqrt

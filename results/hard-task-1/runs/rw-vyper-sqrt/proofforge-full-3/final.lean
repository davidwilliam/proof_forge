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

open ProofForgeFin.Sqrt

/-- Fixed `sqrt`: the deployed loop followed by the smaller of the last two iterates
(pull request 4486: `if y < z: z = y`). -/
def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-- Natural-number model of one Newton iteration for `A = a * 10^10`:
`(A / z + z) / 2`, matching `loop_step` syntactically. -/
def iter (a : Nat) : Nat → Nat
  | 0 => a / 2 + 5 * 10 ^ 9
  | (n + 1) => (a * 10 ^ 10 / iter a n + iter a n) / 2

/-- The seed stays in range. -/
theorem seed_le_M {a : Nat} (h : a ≤ 2 ^ 167 - 1) : a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := by
  have e : 5 * 10 ^ 9 + (2 ^ 167 - 1) / 2 ≤ 2 ^ 167 - 1 := by decide
  have h2 := Nat.div_le_div_right (c := 2) h
  generalize 2 ^ 167 - 1 = M at *
  omega

/-- `(t + 1) * (t + 1)` expanded. -/
theorem sq_succ (t : Nat) : (t + 1) * (t + 1) = t * t + 2 * t + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-- `(2 * u) * (2 * u) = 4 * (u * u)`. -/
theorem two_mul_sq (u : Nat) : (2 * u) * (2 * u) = 4 * (u * u) := by
  rw [Nat.mul_assoc 2 u (2 * u), Nat.mul_left_comm u 2 u, ← Nat.mul_assoc 2 2 (u * u)]

/-- The seed is above the root. -/
theorem seed_ge_sqrt (a : Nat) : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := by
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : Nat.sqrt (0 * 10 ^ 10) = 0 :=
      ProofForgeFin.Sqrt.sqrt_eq_of_bounds (Nat.zero_le _) (by decide)
    omega
  · have hpos : 0 < a := Nat.pos_of_ne_zero ha0
    have amgm := ProofForgeFin.Sqrt.four_mul_le_sq a (10 ^ 10)
    rw [Nat.mul_assoc] at amgm
    have h2 : a + 10 ^ 10 + 1 ≤ 2 * (a / 2 + 5 * 10 ^ 9 + 1) := by omega
    have h4 : (a + 10 ^ 10 + 1) * (a + 10 ^ 10 + 1)
        ≤ (2 * (a / 2 + 5 * 10 ^ 9 + 1)) * (2 * (a / 2 + 5 * 10 ^ 9 + 1)) :=
      Nat.mul_le_mul h2 h2
    have hmul2 : (a + 10 ^ 10 + 1) * (a + 10 ^ 10 + 1)
        ≤ (2 * (a / 2 + 5 * 10 ^ 9 + 1)) * (2 * (a / 2 + 5 * 10 ^ 9 + 1)) :=
      Nat.mul_le_mul h2 h2
    have e1 : (a + 10 ^ 10 + 1) * (a + 10 ^ 10 + 1)
        = (a + 10 ^ 10) * (a + 10 ^ 10) + 2 * (a + 10 ^ 10) + 1 := sq_succ _
    have e2 : (2 * (a / 2 + 5 * 10 ^ 9 + 1)) * (2 * (a / 2 + 5 * 10 ^ 9 + 1))
        = 4 * ((a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1)) := two_mul_sq _
    have amgm2 : 4 * (a * 10 ^ 10) ≤ (a + 10 ^ 10) * (a + 10 ^ 10) := by
      have h := ProofForgeFin.Sqrt.four_mul_le_sq a (10 ^ 10)
      rwa [Nat.mul_assoc] at h
    have h5 : 4 * (a * 10 ^ 10) < 4 * ((a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1)) := by
      omega
    have h6 : a * 10 ^ 10 < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) :=
      Nat.lt_of_mul_lt_mul_left h5
    have h7 : Nat.sqrt (a * 10 ^ 10) < a / 2 + 5 * 10 ^ 9 + 1 :=
      ProofForgeFin.Sqrt.sqrt_lt_of_lt_mul_self h6
    omega

/-- For `a ≥ 1`, the root is at least `10^5`. -/
theorem s_lower {a : Nat} (ha1 : 0 < a) : 10 ^ 5 ≤ Nat.sqrt (a * 10 ^ 10) := by
  apply ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le
  have h10 : (10 ^ 5) * (10 ^ 5) = 10 ^ 10 := by decide
  rw [h10]
  calc 10 ^ 10 = 1 * 10 ^ 10 := by omega
    _ ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ ha1

/-- The root is below `2^101`. -/
theorem s_upper {a : Nat} (hle : a ≤ 2 ^ 167 - 1) (ha1 : 0 < a) :
    Nat.sqrt (a * 10 ^ 10) < 2 ^ 101 := by
  apply ProofForgeFin.Sqrt.sqrt_lt_of_lt_mul_self
  have hD : (10 : Nat) ^ 10 ≤ 2 ^ 35 := by decide
  have h1 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 2 ^ 35 :=
    Nat.mul_le_mul hle hD
  have h2 : (2 ^ 167 - 1) * 2 ^ 35 < 2 ^ 167 * 2 ^ 35 := by
    have hX : (2 : Nat) ^ 167 = (2 ^ 167 - 1) + 1 := by
      have h1 : (1 : Nat) ≤ 2 ^ 167 := by decide
      omega
    have hK : (0 : Nat) < 2 ^ 35 := by decide
    have e : ((2 ^ 167 - 1) + 1) * 2 ^ 35 = (2 ^ 167 - 1) * 2 ^ 35 + 2 ^ 35 := by
      rw [Nat.add_mul, Nat.one_mul]
    generalize (2 ^ 167 - 1) = X at hX e ⊢
    rw [hX, e]
    omega
  have h3 : (2 : Nat) ^ 167 * 2 ^ 35 = 2 ^ (2 * 101) := by
    rw [← Nat.pow_add]
  have h4 : (2 : Nat) ^ (2 * 101) = 2 ^ 101 * 2 ^ 101 := by
    rw [show (2 : Nat) * 101 = 101 + 101 from rfl, Nat.pow_add]
  have h12 := Nat.lt_of_le_of_lt h1 h2
  rw [h3, h4] at h12
  exact h12

/-- `A ≤ s * (s + 2)`. -/
theorem A_le_s_mul {a : Nat} : a * 10 ^ 10 ≤ Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2) := by
  have hup := Nat.lt_succ_sqrt (a * 10 ^ 10)
  rw [Nat.succ_eq_add_one] at hup
  have hex := sq_succ (Nat.sqrt (a * 10 ^ 10))
  have hmul : Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2)
      = Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) + 2 * Nat.sqrt (a * 10 ^ 10) := by
    rw [Nat.mul_add]
    omega
  omega

/-- The quotient `A / z` is at most `s + 2` for `z ≥ s`. -/
theorem q_le {a z : Nat} (hzs : Nat.sqrt (a * 10 ^ 10) ≤ z) :
    a * 10 ^ 10 / z ≤ Nat.sqrt (a * 10 ^ 10) + 2 := by
  apply Nat.div_le_of_le_mul
  have hle := A_le_s_mul (a := a)
  have hmul : Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2)
      ≤ z * (Nat.sqrt (a * 10 ^ 10) + 2) :=
    Nat.mul_le_mul_right _ hzs
  have hcomm : z * (Nat.sqrt (a * 10 ^ 10) + 2) = (Nat.sqrt (a * 10 ^ 10) + 2) * z :=
    Nat.mul_comm _ _
  omega

/-- The Newton sum stays in range. -/
theorem sum_le_M {a z : Nat} (hle : a ≤ 2 ^ 167 - 1) (ha1 : 0 < a)
    (hz0 : z ≤ a / 2 + 5 * 10 ^ 9 + 1) (hzs : Nat.sqrt (a * 10 ^ 10) ≤ z) :
    a * 10 ^ 10 / z + z ≤ 2 ^ 167 - 1 := by
  have hq := q_le (a := a) (z := z) hzs
  have hsup := s_upper hle ha1
  have hseed : a / 2 + 1 ≤ 2 ^ 166 := by
    have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right (c := 2) hle
    have h2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
    generalize (2 : Nat) ^ 166 = Q at *
    omega
  have p1 : 5 * 10 ^ 9 + 2 ≤ 2 ^ 33 := by decide
  have p2 : (2 : Nat) ^ 33 ≤ 2 ^ 165 := by decide
  have p3 : (2 : Nat) ^ 101 ≤ 2 ^ 165 := by decide
  have p4 : (2 : Nat) ^ 166 = 2 ^ 165 * 2 := by decide
  have p5 : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by decide
  generalize (2 : Nat) ^ 33 = A at p1 p2
  generalize (2 : Nat) ^ 101 = B at hsup p3
  generalize (2 : Nat) ^ 165 = C at p2 p3 p4
  generalize (2 : Nat) ^ 166 = D at hseed p4 p5
  generalize (2 : Nat) ^ 167 = E at p5
  omega

/-- `iter` in terms of the library Newton step. -/
theorem iter_newton (a n : Nat) :
    iter a (n + 1) = ProofForgeFin.Sqrt.newton (a * 10 ^ 10) (iter a n) := by
  show (a * 10 ^ 10 / iter a n + iter a n) / 2 = _
  unfold ProofForgeFin.Sqrt.newton
  rw [Nat.add_comm (iter a n) (a * 10 ^ 10 / iter a n)]

/-- Every iterate is above the root. -/
theorem s_le {a : Nat} (ha1 : 0 < a) : ∀ j, Nat.sqrt (a * 10 ^ 10) ≤ iter a j
  | 0 => seed_ge_sqrt a
  | (j + 1) => by
    rw [iter_newton]
    apply ProofForgeFin.Sqrt.sqrt_le_newton
    have h1 := s_le ha1 j
    have h5 := s_lower ha1
    omega

/-- Every iterate is positive. -/
theorem cpos {a : Nat} (ha1 : 0 < a) (j : Nat) : 0 < iter a j := by
  have h1 := s_le ha1 j
  have h5 := s_lower ha1
  omega

/-- Halving error bound: after `k` steps the error is at most `2^(167-k) + 1`. -/
theorem err_le {a : Nat} (hle : a ≤ 2 ^ 167 - 1) (ha1 : 0 < a) :
    ∀ k, k ≤ 167 → iter a k - Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ (167 - k) + 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    show a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ 167 + 1
    have hs := seed_le_M hle
    omega
  | succ k IH =>
    intro hk
    have hk' : k ≤ 167 := by omega
    have ih := IH hk'
    have hm : 1 ≤ 167 - k := by omega
    have e1 : 167 - (k + 1) = (167 - k) - 1 := by omega
    have e2 : 167 - k = ((167 - k) - 1) + 1 := by omega
    have pw : (2 : Nat) ^ (167 - k) = 2 ^ ((167 - k) - 1) * 2 := by
      have h := congrArg (fun m => (2 : Nat) ^ m) e2
      rwa [Nat.pow_succ] at h
    have hpos : 0 < iter a k := cpos ha1 k
    have hsle : Nat.sqrt (a * 10 ^ 10) ≤ iter a k := s_le ha1 k
    have hstep : iter a (k + 1) - Nat.sqrt (a * 10 ^ 10)
        ≤ (iter a k - Nat.sqrt (a * 10 ^ 10)) / 2 + 1 := by
      have h := ProofForgeFin.Sqrt.newton_sub_sqrt_le_half hpos hsle
      rwa [← iter_newton a k] at h
    rw [e1]
    rw [pw] at ih
    omega

/-- After 167 halvings the error is at most 2. -/
theorem err167 {a : Nat} (hle : a ≤ 2 ^ 167 - 1) (ha1 : 0 < a) :
    iter a 167 - Nat.sqrt (a * 10 ^ 10) ≤ 2 := by
  have h167 := err_le hle ha1 167 (Nat.le_refl 167)
  have e167 : (167 : Nat) - 167 = 0 := by decide
  rw [e167, Nat.pow_zero] at h167
  omega

/-- Every iterate is at most one above the seed. -/
theorem cle {a : Nat} (ha1 : 0 < a) : ∀ j, iter a j ≤ a / 2 + 5 * 10 ^ 9 + 1
  | 0 => by
    show a / 2 + 5 * 10 ^ 9 ≤ a / 2 + 5 * 10 ^ 9 + 1
    exact Nat.le_succ _
  | (j + 1) => by
    have ih := cle ha1 j
    have hsj := s_le ha1 j
    have hs0 := seed_ge_sqrt a
    have hpos := cpos ha1 j
    rw [iter_newton]
    rcases Nat.lt_or_ge (Nat.sqrt (a * 10 ^ 10)) (iter a j) with hlt | hge
    · have hlt' := ProofForgeFin.Sqrt.newton_lt_self hlt
      omega
    · have heq : iter a j = Nat.sqrt (a * 10 ^ 10) := by omega
      have h2 : iter a j ≤ Nat.sqrt (a * 10 ^ 10) + 1 := by omega
      rcases ProofForgeFin.Sqrt.newton_of_mem hpos hsj h2 with h | ⟨_, h, _⟩
      · omega
      · omega

/-- Once in `{s, s+1}`, the next iterate stays there. -/
theorem mem_step {a : Nat} (ha1 : 0 < a) (j : Nat)
    (h : iter a j = Nat.sqrt (a * 10 ^ 10) ∨ iter a j = Nat.sqrt (a * 10 ^ 10) + 1) :
    iter a (j + 1) = Nat.sqrt (a * 10 ^ 10) ∨ iter a (j + 1) = Nat.sqrt (a * 10 ^ 10) + 1 := by
  have hpos := cpos ha1 j
  have hsle := s_le ha1 j
  have e : iter a (j + 1) = ProofForgeFin.Sqrt.newton (a * 10 ^ 10) (iter a j) :=
    iter_newton a j
  rcases h with hj | hj
  · have h2 : iter a j ≤ Nat.sqrt (a * 10 ^ 10) + 1 := by omega
    rcases ProofForgeFin.Sqrt.newton_of_mem hpos hsle h2 with hN | ⟨_, hN, _⟩
    · rw [e]
      exact Or.inl hN
    · rw [e]
      exact Or.inr hN
  · have h2 : iter a j ≤ Nat.sqrt (a * 10 ^ 10) + 1 := by omega
    rcases ProofForgeFin.Sqrt.newton_of_mem hpos hsle h2 with hN | ⟨hx, _, _⟩
    · rw [e]
      exact Or.inl hN
    · omega

/-- After 168 steps the iterate is the root or the root plus one. -/
theorem mem168 {a : Nat} (hle : a ≤ 2 ^ 167 - 1) (ha1 : 0 < a) :
    iter a 168 = Nat.sqrt (a * 10 ^ 10) ∨ iter a 168 = Nat.sqrt (a * 10 ^ 10) + 1 := by
  have herr := err167 hle ha1
  have hsup := s_upper hle ha1
  have hslo := s_lower ha1
  have hsle := s_le ha1 167
  have hpos := cpos ha1 167
  have hsq : (iter a 167 - Nat.sqrt (a * 10 ^ 10)) * (iter a 167 - Nat.sqrt (a * 10 ^ 10))
      ≤ Nat.sqrt (a * 10 ^ 10) := by
    have h4 : (iter a 167 - Nat.sqrt (a * 10 ^ 10)) * (iter a 167 - Nat.sqrt (a * 10 ^ 10))
        ≤ 2 * 2 :=
      Nat.mul_le_mul herr herr
    have h4' : (2 : Nat) * 2 ≤ 10 ^ 5 := by decide
    omega
  have hN := ProofForgeFin.Sqrt.newton_eq_or_succ hpos hsle hsq
  have e168 : iter a 168 = ProofForgeFin.Sqrt.newton (a * 10 ^ 10) (iter a 167) :=
    iter_newton a 167
  rw [e168]
  rcases hN with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- From step 168 on, every iterate is the root or the root plus one. -/
theorem mem_ge {a : Nat} (hle : a ≤ 2 ^ 167 - 1) (ha1 : 0 < a) :
    ∀ j, 168 ≤ j → iter a j = Nat.sqrt (a * 10 ^ 10) ∨ iter a j = Nat.sqrt (a * 10 ^ 10) + 1 := by
  have base : ∀ d, iter a (168 + d) = Nat.sqrt (a * 10 ^ 10)
      ∨ iter a (168 + d) = Nat.sqrt (a * 10 ^ 10) + 1 := by
    intro d
    induction d with
    | zero =>
      show iter a 168 = Nat.sqrt (a * 10 ^ 10) ∨ iter a 168 = Nat.sqrt (a * 10 ^ 10) + 1
      exact mem168 hle ha1
    | succ d IH =>
      show iter a ((168 + d) + 1) = Nat.sqrt (a * 10 ^ 10)
        ∨ iter a ((168 + d) + 1) = Nat.sqrt (a * 10 ^ 10) + 1
      exact mem_step ha1 (168 + d) IH
  intro j hj
  have e : j = 168 + (j - 168) := by omega
  rw [e]
  exact base (j - 168)

/-- Newton from the root plus one returns the root. -/
theorem newton_succ {a : Nat} (ha1 : 0 < a) :
    ProofForgeFin.Sqrt.newton (a * 10 ^ 10) (Nat.sqrt (a * 10 ^ 10) + 1)
      = Nat.sqrt (a * 10 ^ 10) := by
  have hpos : 0 < Nat.sqrt (a * 10 ^ 10) + 1 := by
    have hslo := s_lower ha1
    omega
  have h1 : Nat.sqrt (a * 10 ^ 10) ≤ Nat.sqrt (a * 10 ^ 10) + 1 := Nat.le_succ _
  have h2 : Nat.sqrt (a * 10 ^ 10) + 1 ≤ Nat.sqrt (a * 10 ^ 10) + 1 := Nat.le_refl _
  rcases ProofForgeFin.Sqrt.newton_of_mem hpos h1 h2 with h | ⟨hx, _, _⟩
  · exact h
  · omega

/-- The final choice on a diagonal pair. -/
theorem fin_diag (w : Int) : (if (w, w).1 < (w, w).2 then (w, w).1 else (w, w).2) = w := by
  have h : ¬ w < w := by omega
  have e1 : (w, w).1 = w := rfl
  have e2 : (w, w).2 = w := rfl
  rw [e1, e2]
  exact if_neg h

/-- The deployed loop from two consecutive iterates returns the root. -/
theorem fuel {a : Nat} (hle : a ≤ 2 ^ 167 - 1) (ha1 : 0 < a) :
    ∀ (n k : Nat), k + 1 + n ≥ 169 →
      ((loop (a : Int) n ((iter a k : Nat) : Int) ((iter a (k + 1) : Nat) : Int)).map
        fun p => if p.1 < p.2 then p.1 else p.2)
      = some ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  intro n
  induction n with
  | zero =>
    intro k hkn
    have hk : 168 ≤ k := by omega
    have hk1 : 168 ≤ k + 1 := by omega
    have m1 := mem_ge hle ha1 k hk
    have m2 := mem_ge hle ha1 (k + 1) hk1
    have eN : iter a (k + 1) = ProofForgeFin.Sqrt.newton (a * 10 ^ 10) (iter a k) :=
      iter_newton a k
    simp only [loop, Option.map_some]
    rcases m2 with hz | hz
    · have hzc : ((iter a (k + 1) : Nat) : Int) = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
        rw [hz]
      rw [hzc]
      by_cases hlt : ((iter a k : Nat) : Int) < ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int)
      · exfalso
        have hltN : iter a k < Nat.sqrt (a * 10 ^ 10) := Int.ofNat_lt.mp hlt
        have hsle := s_le ha1 k
        omega
      · rw [if_neg hlt]
    · have hy : iter a k = Nat.sqrt (a * 10 ^ 10) := by
        rcases m1 with hy | hy
        · exact hy
        · exfalso
          rw [hy] at eN
          have hNs := newton_succ ha1
          omega
      have hyc : ((iter a k : Nat) : Int) = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
        rw [hy]
      have hzc : ((iter a (k + 1) : Nat) : Int)
          = ((((Nat.sqrt (a * 10 ^ 10) + 1 : Nat))) : Int) := by
        rw [hz]
      rw [hyc, hzc]
      have hlt : ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int)
          < ((((Nat.sqrt (a * 10 ^ 10) + 1 : Nat))) : Int) :=
        Int.ofNat_lt.mpr (Nat.lt_succ_self _)
      rw [if_pos hlt]
  | succ n IH =>
    intro k hkn
    have hk1n : k + 1 + 1 + n ≥ 169 := by omega
    have ih := IH (k + 1) hk1n
    have hpos : 0 < iter a (k + 1) := cpos ha1 (k + 1)
    have hsle : Nat.sqrt (a * 10 ^ 10) ≤ iter a (k + 1) := s_le ha1 (k + 1)
    have hsum := sum_le_M hle ha1 (cle ha1 (k + 1)) hsle
    by_cases heq : ((iter a (k + 1) : Nat) : Int) = ((iter a k : Nat) : Int)
    · have heqN : iter a (k + 1) = iter a k := Int.ofNat.inj heq
      have eN : iter a (k + 1) = ProofForgeFin.Sqrt.newton (a * 10 ^ 10) (iter a k) :=
        iter_newton a k
      have hfix : ProofForgeFin.Sqrt.newton (a * 10 ^ 10) (iter a k) = iter a k := by
        omega
      have hs : iter a k = Nat.sqrt (a * 10 ^ 10) :=
        ProofForgeFin.Sqrt.eq_sqrt_of_newton_eq_self (cpos ha1 k) hfix
      have hloop : loop (a : Int) (n + 1) ((iter a k : Nat) : Int) ((iter a (k + 1) : Nat) : Int)
          = some ((((iter a (k + 1) : Nat) : Int)), (((iter a (k + 1) : Nat) : Int))) := by
        rw [heq]
        exact loop_stop _ _ _
      rw [hloop, Option.map_some]
      have hzc : ((iter a (k + 1) : Nat) : Int) = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
        rw [show iter a (k + 1) = Nat.sqrt (a * 10 ^ 10) from by omega]
      rw [hzc, fin_diag]
    · have hne : iter a (k + 1) ≠ iter a k := fun h => heq (by rw [h])
      have hstep := loop_step (a := a) (y := iter a k) (z := iter a (k + 1)) n hpos hne hsum
      rw [hstep]
      exact ih

/-- The deployed routine returns the integer square root on every non-negative decimal. -/
theorem sqrt_eq {a : Nat} (hle : a ≤ 2 ^ 167 - 1) :
    sqrt ((a : Nat) : Int) = some ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : Nat.sqrt (0 * 10 ^ 10) = 0 :=
      ProofForgeFin.Sqrt.sqrt_eq_of_bounds (Nat.zero_le _) (by decide)
    rw [h0]
    unfold sqrt vyperSqrtWith
    simp
  · have ha1 : 0 < a := Nat.pos_of_ne_zero ha0
    have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha1 hle
    have hfuel : ((loop (a : Int) 256 ((a : Nat) : Int) ((((a / 2 + 5 * 10 ^ 9 : Nat))) : Int)).map
        fun p => if p.1 < p.2 then p.1 else p.2)
        = some ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
      by_cases heq : ((((a / 2 + 5 * 10 ^ 9 : Nat))) : Int) = ((a : Nat) : Int)
      · have heqN : a / 2 + 5 * 10 ^ 9 = a := Int.ofNat.inj heq
        have hs0 : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := seed_ge_sqrt a
        have haD : a ≤ 10 ^ 10 := by omega
        have haa : a * a ≤ a * 10 ^ 10 := by
          have h := Nat.mul_le_mul_right a haD
          rwa [Nat.mul_comm (10 ^ 10) a] at h
        have hle2 : a ≤ Nat.sqrt (a * 10 ^ 10) :=
          ProofForgeFin.Sqrt.le_sqrt_of_mul_self_le haa
        have hge : Nat.sqrt (a * 10 ^ 10) ≤ a := by omega
        have has : a = Nat.sqrt (a * 10 ^ 10) := Nat.le_antisymm hle2 hge
        have hloop : loop (a : Int) 256 ((a : Nat) : Int) ((((a / 2 + 5 * 10 ^ 9 : Nat))) : Int)
            = some ((((a : Nat) : Int)), (((a : Nat) : Int))) := by
          rw [heq]
          exact loop_stop _ _ _
        rw [hloop, Option.map_some]
        have hasC : ((a : Nat) : Int) = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) :=
          congrArg _ has
        rw [hasC, fin_diag]
      · have hne : a / 2 + 5 * 10 ^ 9 ≠ a := fun h => heq (by rw [h])
        have hz0 : a / 2 + 5 * 10 ^ 9 ≤ a / 2 + 5 * 10 ^ 9 + 1 := Nat.le_succ _
        have hpos0 : 0 < a / 2 + 5 * 10 ^ 9 := by
          have h5 : (0 : Nat) < 5 * 10 ^ 9 := by decide
          omega
        have hsle0 : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := seed_ge_sqrt a
        have hsum0 := sum_le_M hle ha1 hz0 hsle0
        have hstep0 := loop_step (a := a) (y := a) (z := a / 2 + 5 * 10 ^ 9) 255 hpos0 hne hsum0
        have hfuel0 := fuel hle ha1 255 0 (by omega)
        exact (congrArg (fun l => l.map fun p => if p.1 < p.2 then p.1 else p.2) hstep0).trans hfuel0
    exact hpos.trans hfuel

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := by
  intro x r hx hxr
  have hnn : ¬ x < 0 := by
    intro hneg
    have hnone : sqrt x = none := by
      unfold sqrt vyperSqrtWith
      rw [if_pos hneg]
    rw [hnone] at hxr
    cases hxr
  have hx0 : 0 ≤ x := by omega
  have hxeq : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
  have ha : x.toNat ≤ 2 ^ 167 - 1 := by
    have hdec : MIN_DECIMAL ≤ x ∧ x ≤ MAX_DECIMAL := hx
    have hhi := hdec.2
    rw [max_decimal_eq] at hhi
    have h2 : ((x.toNat : Nat) : Int) ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
      rw [hxeq]
      exact hhi
    exact Int.ofNat_le.mp h2
  have e := sqrt_eq ha
  rw [hxeq] at e
  have hr : r = ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) :=
    Option.some.inj (hxr.symm.trans e)
  have hle := Nat.sqrt_le (x.toNat * 10 ^ 10)
  rw [← hxeq, hr, divisor_eq, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr hle

theorem req_sqrt_not_below   : SqrtNotBelow sqrt := by
  intro x r hx hxr
  have hnn : ¬ x < 0 := by
    intro hneg
    have hnone : sqrt x = none := by
      unfold sqrt vyperSqrtWith
      rw [if_pos hneg]
    rw [hnone] at hxr
    cases hxr
  have hx0 : 0 ≤ x := by omega
  have hxeq : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
  have ha : x.toNat ≤ 2 ^ 167 - 1 := by
    have hdec : MIN_DECIMAL ≤ x ∧ x ≤ MAX_DECIMAL := hx
    have hhi := hdec.2
    rw [max_decimal_eq] at hhi
    have h2 : ((x.toNat : Nat) : Int) ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
      rw [hxeq]
      exact hhi
    exact Int.ofNat_le.mp h2
  have e := sqrt_eq ha
  rw [hxeq] at e
  have hr : r = ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) :=
    Option.some.inj (hxr.symm.trans e)
  have hlt := Nat.lt_succ_sqrt (x.toNat * 10 ^ 10)
  rw [Nat.succ_eq_add_one] at hlt
  have e1 : ((Nat.sqrt (x.toNat * 10 ^ 10) + 1 : Nat) : Int)
      = ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) + 1 := by
    rw [Int.natCast_add, Int.natCast_one]
  rw [← hxeq, hr, divisor_eq, ← e1, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_lt.mpr hlt

theorem req_sqrt_total       : SqrtTotal sqrt := by
  intro x hx h0
  have hx0 : 0 ≤ x := by omega
  have hxeq : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
  have ha : x.toNat ≤ 2 ^ 167 - 1 := by
    have hdec : MIN_DECIMAL ≤ x ∧ x ≤ MAX_DECIMAL := hx
    have hhi := hdec.2
    rw [max_decimal_eq] at hhi
    have h2 : ((x.toNat : Nat) : Int) ≤ ((2 ^ 167 - 1 : Nat) : Int) := by
      rw [hxeq]
      exact hhi
    exact Int.ofNat_le.mp h2
  have e := sqrt_eq ha
  rw [hxeq] at e
  rw [e]
  rfl

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop    : DeployedLoop sqrt := by
  exact ⟨(fun y z => if y < z then y else z), fun x => rfl⟩

end VyperSqrt

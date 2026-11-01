import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
/-!
Port of the code the Vyper compiler v0.4.0 (commit e9db8d9f7486eae38f5b86531629019ad28f514e)
inlines for the builtin `sqrt(d: decimal) -> decimal`, `vyper/builtins/functions.py`, class
`Sqrt` (lines 2117 to 2172), with the fix of pull request 4486 (merge commit
2ffc8b3db8b7e32257a72560e9dcf81b5384, released in v0.4.1): after the loop,

```
    if y < z:
        z = y
```

i.e. the result is the smaller of the last two iterates, so the root is rounded down.
-/
namespace VyperSqrt

open ProofForgeFin.Sqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  simp only [sqrt, vyperSqrtWith]
  rw [if_pos hx]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨_, fun x => rfl⟩

/-! ## Natural-number helpers -/

/-- One Newton step stays positive when the radicand and iterate are positive. -/
theorem newton_pos {N x : Nat} (hN : 0 < N) (hx : 0 < x) : 0 < newton N x := by
  have h1 : x / 2 ≤ newton N x :=
    Nat.div_le_div_right (Nat.le_add_right x (N / x))
  rcases Nat.lt_or_ge x 2 with h | h
  · have hx1 : x = 1 := by omega
    have e : newton N 1 = (1 + N) / 2 := by
      show (1 + N / 1) / 2 = _
      rw [Nat.div_one]
    rw [hx1, e]
    omega
  · have h2 : 0 < x / 2 := by omega
    omega

/-- The seed-plus-one squared exceeds the scaled input. -/
theorem seed_gt {a : Nat} :
    a * 10 ^ 10 < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) := by
  have h10 : (10 : Nat) ^ 10 = 10000000000 := by decide
  have h5 : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  rw [h10, h5]
  show a * 10000000000 < (a / 2 + 5000000001) * (a / 2 + 5000000001)
  have hda : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hr : a % 2 ≤ 1 := by have h := Nat.mod_lt a (show 0 < 2 by decide); omega
  have key : ∀ u r : Nat, r ≤ 1 →
      (2 * u + r) * 10000000000 < (u + 5000000001) * (u + 5000000001) := by
    intro u r hr
    rcases Nat.le_total u 5000000001 with h | h
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      have e3 : 4 * (u * u) + 4 * u * d = 4 * u * 5000000001 := by
        have e : 4 * (u * u) + 4 * u * d = 4 * u * (u + d) := by grind
        rw [e, ← hd]
      have e2 : (u + (u + d)) * (u + (u + d)) = 4 * (u * u) + 4 * u * d + d * d := by
        grind
      have h4 : u + 5000000001 = u + (u + d) := by rw [hd]
      rw [h4, e2, e3]
      rcases Nat.lt_or_ge d 4 with hd4 | hd4
      · have hdd : d * d ≤ 9 := by
          have hle : d * d ≤ 3 * 3 := Nat.mul_le_mul (by omega) (by omega)
          have h9 : 3 * 3 = (9 : Nat) := by decide
          rwa [h9] at hle
        have hd3 : d ≤ 3 := by omega
        have hu : 4999999998 ≤ u := by omega
        omega
      · have hdd : 4 * d ≤ d * d := Nat.mul_le_mul (by omega) (Nat.le_refl d)
        omega
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      have e1 : (5000000001 + d + 5000000001) * (5000000001 + d + 5000000001) =
          10000000002 * 10000000002 + 2 * 10000000002 * d + d * d := by grind
      rw [hd, e1]
      omega
  have hfin := key (a / 2) (a % 2) hr
  rwa [hda] at hfin

/-- The root is below `2^101` on decimal inputs. -/
theorem sqrt_mag {a : Nat} (h : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (a * 10 ^ 10) < 2 ^ 101 := by
  have h10le : (10 : Nat) ^ 10 ≤ 2 ^ 34 := by decide
  have h1 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 := Nat.mul_le_mul_right _ h
  have hlt : (2 : Nat) ^ 167 - 1 < 2 ^ 167 :=
    Nat.sub_one_lt_of_le (Nat.pow_pos (by decide)) (Nat.le_refl _)
  have h2a : (2 ^ 167 - 1) * 10 ^ 10 ≤ (2 ^ 167 - 1) * 2 ^ 34 :=
    Nat.mul_le_mul (Nat.le_refl _) h10le
  have h2b : (2 ^ 167 - 1) * 2 ^ 34 < 2 ^ 167 * 2 ^ 34 :=
    Nat.mul_lt_mul_of_pos_right hlt (Nat.pow_pos (by decide))
  have h3 : 2 ^ 167 * 2 ^ 34 = 2 ^ 201 := by rw [← Nat.pow_add]
  have h2 : (2 ^ 167 - 1) * 10 ^ 10 < 2 ^ 201 := by
    rw [← h3]; exact Nat.lt_of_le_of_lt h2a h2b
  have h4 : (2 : Nat) ^ 201 < 2 ^ 202 := Nat.pow_lt_pow_succ (by decide)
  have hfin : a * 10 ^ 10 < 2 ^ 202 :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h2) (Nat.le_of_lt h4)
  exact sqrt_lt_two_pow (k := 101) hfin

/-- The seed is at least the root. -/
theorem s_le_z0 {a : Nat} : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := by
  have hlt := seed_gt (a := a)
  have h10 : (10 : Nat) ^ 10 = 10000000000 := by decide
  have h5 : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  rw [h10, h5] at *
  have h3 : a / 2 + 5000000000 + 1 = a / 2 + 5000000001 := by omega
  rw [h3] at hlt
  have h2 : Nat.sqrt (a * 10000000000) < a / 2 + 5000000001 :=
    sqrt_lt_of_lt_mul_self hlt
  omega

/-- On positive inputs the root is positive. -/
theorem sqrt_ge_one {a : Nat} (ha1 : 1 ≤ a) : 1 ≤ Nat.sqrt (a * 10 ^ 10) := by
  apply le_sqrt_of_mul_self_le
  have h1 : (1 : Nat) * 1 ≤ 1 * 10 ^ 10 := by decide
  have h2 : 1 * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul ha1 (Nat.le_refl _)
  exact Nat.le_trans h1 h2

/-- On positive inputs the root is at least two. -/
theorem sqrt_ge_two {a : Nat} (ha1 : 1 ≤ a) : 2 ≤ Nat.sqrt (a * 10 ^ 10) := by
  apply le_sqrt_of_mul_self_le
  have h1 : (2 : Nat) * 2 ≤ 1 * 10 ^ 10 := by decide
  have h2 : 1 * 10 ^ 10 ≤ a * 10 ^ 10 := Nat.mul_le_mul ha1 (Nat.le_refl _)
  exact Nat.le_trans h1 h2

/-- The seed stays in range on decimal inputs. -/
theorem seed_le {a : Nat} (ha : a ≤ 2 ^ 167 - 1) :
    a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := by
  have h5 : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  rw [h5]
  have haseed : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right ha
  have e : 5000000000 + (2 ^ 167 - 1) / 2 ≤ 2 ^ 167 - 1 := by decide
  generalize 2 ^ 167 - 1 = M at *
  omega

/-- When the seed equals the input, it is the root. -/
theorem seed_eq_self {a : Nat} (h : a = a / 2 + 5 * 10 ^ 9) :
    Nat.sqrt (a * 10 ^ 10) = a := by
  have h5 : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  rw [h5] at h
  have ha : a = 9999999999 ∨ a = 10000000000 := by omega
  rcases ha with rfl | rfl
  · apply sqrt_eq_of_bounds (r := 9999999999)
    · decide
    · decide
  · have e : (10000000000 : Nat) * 10 ^ 10 = 10000000000 * 10000000000 := by decide
    rw [e]
    exact sqrt_mul_self 10000000000

/-! ## Newton iteration sequence -/

/-- Newton iterates from a seed. -/
def newtonSeq (N z0 : Nat) : Nat → Nat
  | 0 => z0
  | k+1 => newton N (newtonSeq N z0 k)

theorem seq_succ (N z0 k : Nat) :
    newtonSeq N z0 (k + 1) = newton N (newtonSeq N z0 k) := by
  simp only [newtonSeq]

/-- Division-order form of one Newton step. -/
theorem newton_comm (N z : Nat) : (N / z + z) / 2 = newton N z := by
  have e : newton N z = (z + N / z) / 2 := rfl
  rw [e, Nat.add_comm]

theorem seq_shift (N x : Nat) (j k : Nat) :
    newtonSeq N x (j + k) = newtonSeq N (newtonSeq N x j) k := by
  induction k with
  | zero => simp [newtonSeq, Nat.add_zero]
  | succ k ih =>
    have e : j + (k + 1) = (j + k) + 1 := by omega
    rw [e]
    simp only [newtonSeq]
    rw [ih]

theorem seq_pos {N z0 : Nat} (hz : 0 < z0) (hN : 0 < N) (k : Nat) :
    0 < newtonSeq N z0 k := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    simp only [newtonSeq]
    exact newton_pos hN ih

theorem seq_ge {N z0 : Nat} (hle : Nat.sqrt N ≤ z0) (hz : 0 < z0) (hN : 0 < N)
    (k : Nat) : Nat.sqrt N ≤ newtonSeq N z0 k := by
  induction k with
  | zero => exact hle
  | succ k ih =>
    simp only [newtonSeq]
    exact sqrt_le_newton (seq_pos hz hN k)

theorem seq_le {N z0 : Nat} (hle : Nat.sqrt N ≤ z0) (hz : 0 < z0) (hN : 0 < N)
    (k : Nat) : newtonSeq N z0 k ≤ z0 + 1 := by
  induction k with
  | zero => exact Nat.le_succ _
  | succ k ih =>
    simp only [newtonSeq]
    have hge := seq_ge hle hz hN k
    have hpos := seq_pos hz hN k
    rcases Nat.lt_or_ge (Nat.sqrt N) (newtonSeq N z0 k) with hlt | hge'
    · have hlt' := newton_lt_self hlt
      omega
    · have hmem := newton_of_mem hpos (by omega) (by omega)
      rcases hmem with h | ⟨-, h2, -⟩
      · omega
      · omega

/-- After `m + 2` steps the error is at most one. -/
theorem conv {N : Nat} (hs2 : 2 ≤ Nat.sqrt N) (hN : 0 < N) (m : Nat) (x : Nat)
    (hge : Nat.sqrt N ≤ x) (hx : 0 < x) (hb : x - Nat.sqrt N ≤ 2 ^ m + 2) :
    newtonSeq N x (m + 2) ≤ Nat.sqrt N + 1 := by
  induction m generalizing x with
  | zero =>
    have hb3 : x - Nat.sqrt N ≤ 3 := by
      have hz : (2 : Nat) ^ 0 = 1 := Nat.pow_zero 2
      rwa [hz] at hb
    have hhalf := newton_sub_sqrt_le_half hx hge
    have e1 : newton N x - Nat.sqrt N ≤ 2 := by omega
    have hpos1 : 0 < newton N x := newton_pos hN hx
    have hge1 : Nat.sqrt N ≤ newton N x := sqrt_le_newton hx
    have emul : (newton N x - Nat.sqrt N) * (newton N x - Nat.sqrt N) ≤ 2 * 2 :=
      Nat.mul_le_mul e1 e1
    have hsq : (newton N x - Nat.sqrt N) * (newton N x - Nat.sqrt N) ≤
        2 * Nat.sqrt N := by omega
    have hfin := newton_le_sqrt_add_one hpos1 hge1 hsq
    have e02 : (0 : Nat) + 2 = 2 := rfl
    rw [e02]
    show newton N (newton N x) ≤ _
    exact hfin
  | succ m ih =>
    have hhalf := newton_sub_sqrt_le_half hx hge
    have hpos1 : 0 < newton N x := newton_pos hN hx
    have hge1 : Nat.sqrt N ≤ newton N x := sqrt_le_newton hx
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    have hb1 : newton N x - Nat.sqrt N ≤ 2 ^ m + 2 := by omega
    have e : m + 1 + 2 = 1 + (m + 2) := by omega
    rw [e, seq_shift]
    show newtonSeq N (newton N x) (m + 2) ≤ _
    exact ih (newton N x) hge1 hpos1 hb1

/-- From step 169 on, iterates stay within one of the root. -/
theorem seq_stay {a : Nat} (ha : a ≤ 2 ^ 167 - 1) (ha1 : 1 ≤ a) (d : Nat) :
    newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (169 + d) ≤
      Nat.sqrt (a * 10 ^ 10) + 1 := by
  have hN : 0 < a * 10 ^ 10 := Nat.mul_pos ha1 (by decide)
  have h5z : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  have hz0 : 0 < a / 2 + 5 * 10 ^ 9 := by
    rw [h5z]; clear h5z; omega
  have hsle : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := s_le_z0
  have hs2 : 2 ≤ Nat.sqrt (a * 10 ^ 10) := sqrt_ge_two ha1
  have hseed : a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := seed_le ha
  have hb : a / 2 + 5 * 10 ^ 9 - Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ 167 + 2 := by omega
  have h169 : newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (167 + 2) ≤
      Nat.sqrt (a * 10 ^ 10) + 1 :=
    conv hs2 hN 167 _ hsle hz0 hb
  have e169 : (167 : Nat) + 2 = 169 := by decide
  rw [e169] at h169
  induction d with
  | zero =>
    have e : 169 + 0 = 169 := by omega
    rw [e]; exact h169
  | succ d ih =>
    have e : 169 + (d + 1) = (169 + d) + 1 := by omega
    rw [e]
    simp only [newtonSeq]
    have hge := seq_ge hsle hz0 hN (169 + d)
    have hpos := seq_pos hz0 hN (169 + d)
    rcases newton_of_mem hpos hge ih with h | ⟨-, h2, -⟩
    · omega
    · omega

/-- Every iterate stays in range for the decimal operations. -/
theorem range_bound {a y : Nat} (ha : a ≤ 2 ^ 167 - 1)
    (hs1 : 1 ≤ Nat.sqrt (a * 10 ^ 10))
    (hge : Nat.sqrt (a * 10 ^ 10) ≤ y) (hle : y ≤ a / 2 + 5 * 10 ^ 9 + 1) :
    a * 10 ^ 10 / y + y ≤ 2 ^ 167 - 1 := by
  have hup : a * 10 ^ 10 < (Nat.sqrt (a * 10 ^ 10) + 1) * (Nat.sqrt (a * 10 ^ 10) + 1) := by
    have h := Nat.lt_succ_sqrt (a * 10 ^ 10)
    rwa [Nat.succ_eq_add_one] at h
  have e1 : (Nat.sqrt (a * 10 ^ 10) + 1) * (Nat.sqrt (a * 10 ^ 10) + 1) =
      Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) +
        2 * Nat.sqrt (a * 10 ^ 10) + 1 := by grind
  have hN1 : a * 10 ^ 10 ≤ Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2) := by
    have e2 : Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2) =
        Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) +
          2 * Nat.sqrt (a * 10 ^ 10) := by grind
    omega
  have hNy : a * 10 ^ 10 ≤ (Nat.sqrt (a * 10 ^ 10) + 2) * y := by
    have hss : Nat.sqrt (a * 10 ^ 10) * (Nat.sqrt (a * 10 ^ 10) + 2) ≤
        y * (Nat.sqrt (a * 10 ^ 10) + 2) :=
      Nat.mul_le_mul hge (Nat.le_refl _)
    have e3 : y * (Nat.sqrt (a * 10 ^ 10) + 2) =
        (Nat.sqrt (a * 10 ^ 10) + 2) * y := Nat.mul_comm _ _
    omega
  have hy0 : 0 < y := by omega
  have hdiv : a * 10 ^ 10 / y ≤ Nat.sqrt (a * 10 ^ 10) + 2 := by
    have hle2 : a * 10 ^ 10 / y ≤ ((Nat.sqrt (a * 10 ^ 10) + 2) * y) / y :=
      Nat.div_le_div_right hNy
    have heq : ((Nat.sqrt (a * 10 ^ 10) + 2) * y) / y =
        Nat.sqrt (a * 10 ^ 10) + 2 :=
      Nat.mul_div_cancel _ hy0
    omega
  have hmag := sqrt_mag ha
  have hfin : (2 ^ 101 - 1) + 2 + ((2 ^ 167 - 1) / 2 + 5000000000 + 1) ≤ 2 ^ 167 - 1 := by
    decide
  have hs101 : Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ 101 - 1 := by
    have hpos : (0 : Nat) < 2 ^ 101 := Nat.pow_pos (by decide)
    omega
  have haseed : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right ha
  have h5 : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  rw [h5] at hle
  clear h5 hmag hup e1 hN1 hNy
  omega

/-! ## Loop simulation -/

/-- The loop follows Newton steps; the minimum of the final pair is the root. -/
theorem loop_iter {a : Nat} (ha : a ≤ 2 ^ 167 - 1) (ha1 : 1 ≤ a) (n k : Nat)
    (hk : k + n ≥ 169) :
    ∃ b c : Nat, loop (a : Int) n (↑(newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k))
      (↑(newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1))) =
      some ((↑b : Int), (↑c : Int)) ∧ min b c = Nat.sqrt (a * 10 ^ 10) := by
  have hN : 0 < a * 10 ^ 10 := Nat.mul_pos ha1 (by decide)
  have h5z : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  have hz0 : 0 < a / 2 + 5 * 10 ^ 9 := by
    rw [h5z]; clear h5z; omega
  have hsle : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := s_le_z0
  have hs1 : 1 ≤ Nat.sqrt (a * 10 ^ 10) := sqrt_ge_one ha1
  induction n generalizing k with
  | zero =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 169 ≤ k)
    have h1 : newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (169 + d + 1) =
        newton (a * 10 ^ 10) (newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (169 + d)) :=
      seq_succ _ _ _
    refine ⟨_, _, rfl, ?_⟩
    rw [h1]
    exact min_newton_eq_sqrt (seq_pos hz0 hN _) (seq_ge hsle hz0 hN _)
      (seq_stay ha ha1 d)
  | succ n ih =>
    have hys : newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) =
        newton (a * 10 ^ 10) (newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k) :=
      seq_succ _ _ _
    by_cases heq : ((newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) : Nat) : Int) =
        ((newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k : Nat) : Int)
    · have hxy : newton (a * 10 ^ 10) (newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k) =
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k := by
        rw [← hys]; exact Int.ofNat_inj.mp heq
      have hxs : newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k =
          Nat.sqrt (a * 10 ^ 10) :=
        eq_sqrt_of_newton_eq_self (seq_pos hz0 hN k) hxy
      have hstop : loop (a : Int) (n + 1)
          (↑(newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k))
          (↑(newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1))) =
          some (((newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k : Nat) : Int),
            ((newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k : Nat) : Int)) := by
        rw [heq]
        exact loop_stop _ _ _
      refine ⟨_, _, hstop, ?_⟩
      omega
    · have hne : ((newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) : Nat) : Int) ≠
          ((newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k : Nat) : Int) := heq
      have hneNat : newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) ≠
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k :=
        fun c => hne (by rw [c])
      have hle' : newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) ≤
          a / 2 + 5 * 10 ^ 9 + 1 :=
        seq_le hsle hz0 hN (k + 1)
      have hge' : Nat.sqrt (a * 10 ^ 10) ≤
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) :=
        seq_ge hsle hz0 hN (k + 1)
      have hbound : a * 10 ^ 10 /
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) +
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) ≤ 2 ^ 167 - 1 :=
        range_bound ha hs1 hge' hle'
      have hpos' : 0 < newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) :=
        seq_pos hz0 hN (k + 1)
      have hstep := loop_step (a := a)
        (y := newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k)
        (z := newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1)) n hpos' hneNat hbound
      have hnx : (a * 10 ^ 10 /
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1) +
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1)) / 2 =
          newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1 + 1) := by
        rw [seq_succ (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) (k + 1)]
        exact newton_comm _ _
      rw [hnx] at hstep
      obtain ⟨b, c, hloop, hmin⟩ := ih (k + 1) (by omega)
      exact ⟨b, c, hstep.trans hloop, hmin⟩

/-- Top-level: the deployed loop from the seed ends with minimum the root. -/
theorem loop_total_floor {a : Nat} (ha : a ≤ 2 ^ 167 - 1) (ha1 : 1 ≤ a) :
    ∃ b c : Nat, loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) =
      some (((b : Int)), ((c : Int))) ∧ min b c = Nat.sqrt (a * 10 ^ 10) := by
  have hN : 0 < a * 10 ^ 10 := Nat.mul_pos ha1 (by decide)
  have h5z : 5 * (10 : Nat) ^ 9 = 5000000000 := by decide
  have hz0 : 0 < a / 2 + 5 * 10 ^ 9 := by
    rw [h5z]; clear h5z; omega
  have hsle : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := s_le_z0
  have hs1 : 1 ≤ Nat.sqrt (a * 10 ^ 10) := sqrt_ge_one ha1
  by_cases heq : ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) = (a : Int)
  · have haa : a / 2 + 5 * 10 ^ 9 = a := Int.ofNat_inj.mp heq
    have hss : Nat.sqrt (a * 10 ^ 10) = a := seed_eq_self haa.symm
    have hstop : loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) =
        some (((a : Int)), ((a : Int))) := by
      have e256 : (256 : Nat) = 255 + 1 := rfl
      rw [e256, heq]
      exact loop_stop _ _ _
    refine ⟨a, a, hstop, ?_⟩
    omega
  · have hne : ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) ≠ (a : Int) := heq
    have hneNat : a / 2 + 5 * 10 ^ 9 ≠ a := fun c => hne (by rw [c])
    have hbound : a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9) + (a / 2 + 5 * 10 ^ 9) ≤
        2 ^ 167 - 1 :=
      range_bound ha hs1 hsle (Nat.le_succ _)
    have hstep := loop_step (a := a) (y := a) (z := a / 2 + 5 * 10 ^ 9) 255 hz0
      hneNat hbound
    have e256 : (256 : Nat) = 255 + 1 := rfl
    have hnx : (a * 10 ^ 10 / (a / 2 + 5 * 10 ^ 9) + (a / 2 + 5 * 10 ^ 9)) / 2 =
        newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) 1 := by
      have e1 : newtonSeq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) 1 =
          newton (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) := rfl
      rw [e1]
      exact newton_comm _ _
    rw [e256, hstep, hnx] at ⊢
    obtain ⟨b, c, hloop, hmin⟩ := loop_iter ha ha1 255 0 (by omega)
    exact ⟨b, c, hloop, hmin⟩

/-- The choice returns the root as an integer. -/
theorem fin_eq_sqrt {a b c : Nat} {r : Int}
    (hmin : min b c = Nat.sqrt (a * 10 ^ 10))
    (hr : (if (b : Int) < (c : Int) then (b : Int) else (c : Int)) = r) :
    r = ((Nat.sqrt (a * 10 ^ 10) : Nat) : Int) := by
  by_cases h : (b : Int) < (c : Int)
  · rw [if_pos h] at hr
    have hbc : b < c := Int.ofNat_lt.mp h
    have hmb : min b c = b := Nat.min_eq_left (Nat.le_of_lt hbc)
    omega
  · rw [if_neg h] at hr
    have hcb : c ≤ b := Int.ofNat_le.mp (by omega)
    have hmc : min b c = c := Nat.min_eq_right hcb
    omega

/-! ## Main requirements -/

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hsome
  by_cases hx0 : 0 ≤ x
  · have hxa : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
    have ham : x.toNat ≤ 2 ^ 167 - 1 := by
      have hx2 := hx.2
      rw [max_decimal_eq, ← hxa] at hx2
      exact Int.ofNat_le.mp hx2
    rw [← hxa] at hsome ⊢
    rcases Nat.eq_zero_or_pos x.toNat with h0 | ha1
    · have hsqrt0 : sqrt (0 : Int) = some 0 := by
        unfold sqrt vyperSqrtWith
        rw [if_neg (by decide), if_pos rfl]
      have hz : ((0 : Nat) : Int) = 0 := Int.natCast_zero
      rw [h0] at hsome ⊢
      rw [hz, hsqrt0] at hsome
      have hr0 : (0 : Int) = r := Option.some_inj.mp hsome
      rw [← hr0]
      simp
    · have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha1 ham
      have hsq : sqrt ((x.toNat : Nat) : Int) =
          vyperSqrtWith (fun y z => if y < z then y else z) ((x.toNat : Nat) : Int) :=
        rfl
      rw [hsq, hpos] at hsome
      obtain ⟨b, c, hloop, hmin⟩ := loop_total_floor ham ha1
      rw [hloop] at hsome
      simp only [Option.map_some] at hsome
      have hfin : (if (b : Int) < (c : Int) then (b : Int) else (c : Int)) = r := by
        have h2 := Option.some_inj.mp hsome
        simpa using h2
      have hr : r = ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) :=
        fin_eq_sqrt hmin hfin
      rw [hr]
      have hN : Nat.sqrt (x.toNat * 10 ^ 10) * Nat.sqrt (x.toNat * 10 ^ 10) ≤
          x.toNat * 10 ^ 10 :=
        Nat.sqrt_le _
      rw [divisor_eq, ← Int.natCast_mul, ← Int.natCast_mul]
      exact Int.ofNat_le.mpr hN
  · have hnone := req_sqrt_neg_reverts x (by omega)
    rw [hnone] at hsome
    cases hsome

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hsome
  by_cases hx0 : 0 ≤ x
  · have hxa : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
    have ham : x.toNat ≤ 2 ^ 167 - 1 := by
      have hx2 := hx.2
      rw [max_decimal_eq, ← hxa] at hx2
      exact Int.ofNat_le.mp hx2
    rw [← hxa] at hsome ⊢
    rcases Nat.eq_zero_or_pos x.toNat with h0 | ha1
    · have hsqrt0 : sqrt (0 : Int) = some 0 := by
        unfold sqrt vyperSqrtWith
        rw [if_neg (by decide), if_pos rfl]
      have hz : ((0 : Nat) : Int) = 0 := Int.natCast_zero
      rw [h0] at hsome ⊢
      rw [hz, hsqrt0] at hsome
      have hr0 : (0 : Int) = r := Option.some_inj.mp hsome
      rw [← hr0]
      simp [divisor_eq]
    · have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha1 ham
      have hsq : sqrt ((x.toNat : Nat) : Int) =
          vyperSqrtWith (fun y z => if y < z then y else z) ((x.toNat : Nat) : Int) :=
        rfl
      rw [hsq, hpos] at hsome
      obtain ⟨b, c, hloop, hmin⟩ := loop_total_floor ham ha1
      rw [hloop] at hsome
      simp only [Option.map_some] at hsome
      have hfin : (if (b : Int) < (c : Int) then (b : Int) else (c : Int)) = r := by
        have h2 := Option.some_inj.mp hsome
        simpa using h2
      have hr : r = ((Nat.sqrt (x.toNat * 10 ^ 10) : Nat) : Int) :=
        fin_eq_sqrt hmin hfin
      rw [hr]
      have hup : x.toNat * 10 ^ 10 <
          (Nat.sqrt (x.toNat * 10 ^ 10) + 1) * (Nat.sqrt (x.toNat * 10 ^ 10) + 1) := by
        have h := Nat.lt_succ_sqrt (x.toNat * 10 ^ 10)
        rwa [Nat.succ_eq_add_one] at h
      have hcast : ((x.toNat * 10 ^ 10 : Nat) : Int) <
          (((Nat.sqrt (x.toNat * 10 ^ 10) + 1) * (Nat.sqrt (x.toNat * 10 ^ 10) + 1) : Nat) : Int) :=
        Int.ofNat_lt.mpr hup
      rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_add, Int.natCast_one] at hcast
      rw [divisor_eq]
      exact hcast
  · have hnone := req_sqrt_neg_reverts x (by omega)
    rw [hnone] at hsome
    cases hsome

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hx0
  have hxa : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
  have ham : x.toNat ≤ 2 ^ 167 - 1 := by
    have hx2 := hx.2
    rw [max_decimal_eq, ← hxa] at hx2
    exact Int.ofNat_le.mp hx2
  rw [← hxa]
  rcases Nat.eq_zero_or_pos x.toNat with h0 | ha1
  · have hsqrt0 : sqrt (0 : Int) = some 0 := by
      unfold sqrt vyperSqrtWith
      rw [if_neg (by decide), if_pos rfl]
    have hz : ((0 : Nat) : Int) = 0 := Int.natCast_zero
    rw [h0, hz, hsqrt0]
    rfl
  · have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha1 ham
    have hsq : sqrt ((x.toNat : Nat) : Int) =
        vyperSqrtWith (fun y z => if y < z then y else z) ((x.toNat : Nat) : Int) :=
      rfl
    rw [hsq, hpos]
    obtain ⟨b, c, hloop, -⟩ := loop_total_floor ham ha1
    rw [hloop, Option.map_some]
    rfl

end VyperSqrt



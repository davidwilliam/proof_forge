import VyperSqrt.Spec
/-!
# Helper lemmas (protected, agent-visible)

Proved facts about the protected definitions `ddiv`, `dadd`, `loop` and `vyperSqrtWith` on
non-negative values, where every operation is the operation on natural numbers. They say nothing
about the definition hole; a candidate may use them.

* `ddiv_nat`, `dadd_nat`: decimal division and addition of non-negative values that stay in range.
* `loop_stop`: the loop stops when the last two iterates are equal.
* `loop_step`: otherwise one iteration from a positive iterate `z` is the Newton step
  `(x * 10^10 / z + z) / 2` on natural numbers, when `x * 10^10 / z + z` is a decimal.
* `seed_div`, `seed_add`: the seed `x / 2.0 + 0.5` of a non-negative decimal `x` is
  `x / 2 + 5 * 10^9`.
* `vyperSqrtWith_pos`: on a positive decimal, the routine is the loop from the seed followed by
  the choice.
-/

namespace VyperSqrt

/-- `MAX_DECIMAL` as the cast of a natural number. -/
theorem max_decimal_eq : MAX_DECIMAL = ((2 ^ 167 - 1 : Nat) : Int) := rfl

/-- `DIVISOR` as the cast of a natural number. -/
theorem divisor_eq : DIVISOR = ((10 ^ 10 : Nat) : Int) := rfl

/-- A natural number up to `2^167 - 1` is a decimal. -/
theorem isDecimal_nat {a : Nat} (h : a ≤ 2 ^ 167 - 1) : IsDecimal (a : Int) := by
  unfold IsDecimal
  rw [max_decimal_eq]
  refine ⟨?_, by exact_mod_cast h⟩
  have : MIN_DECIMAL ≤ 0 := by decide
  omega

/-- Decimal division of non-negative values that stays in range is the division on natural
numbers of `a * 10^10` by `b`. -/
theorem ddiv_nat {a b : Nat} (hb : 0 < b) (h : a * 10 ^ 10 / b ≤ 2 ^ 167 - 1) :
    ddiv (a : Int) (b : Int) = some ((a * 10 ^ 10 / b : Nat) : Int) := by
  unfold ddiv
  rw [ite_eq_right (by omega), divisor_eq, ← Int.natCast_mul, ← Int.ofNat_tdiv]
  unfold clampDecimal
  rw [ite_eq_left (isDecimal_nat h)]

/-- Decimal addition of non-negative values that stays in range. -/
theorem dadd_nat {a b : Nat} (h : a + b ≤ 2 ^ 167 - 1) :
    dadd (a : Int) (b : Int) = some ((a + b : Nat) : Int) := by
  unfold dadd clampDecimal
  rw [← Int.natCast_add, ite_eq_left (isDecimal_nat h)]

/-- The loop stops when the last two iterates are equal. -/
theorem loop_stop (x : Int) (n : Nat) (y : Int) : loop x (n + 1) y y = some (y, y) := by
  rewrite [loop, ite_eq_left rfl]
  rfl

/-- One iteration of the loop from `z`, different from the previous iterate `y`, in terms of the
values of its three operations. -/
theorem loop_step_of {x y z q t z' : Int} (n : Nat) (hne : z ≠ y) (h1 : ddiv x z = some q)
    (h2 : dadd q z = some t) (h3 : ddiv t (2 * DIVISOR) = some z') :
    loop x (n + 1) y z = loop x n z z' := by
  rewrite [loop, ite_eq_right hne, h1, Option.bind_some, h2, Option.bind_some, h3, Option.bind_some]
  rfl

/-- One iteration of the loop from a positive iterate `z` different from the previous one `y`
is the Newton step on natural numbers. -/
theorem loop_step {a y z : Nat} (n : Nat) (hz : 0 < z) (hne : z ≠ y)
    (h : a * 10 ^ 10 / z + z ≤ 2 ^ 167 - 1) :
    loop (a : Int) (n + 1) (y : Int) (z : Int) =
      loop (a : Int) n (z : Int) (((a * 10 ^ 10 / z + z) / 2 : Nat) : Int) := by
  have hq : a * 10 ^ 10 / z ≤ 2 ^ 167 - 1 := Nat.le_trans (Nat.le_add_right _ _) h
  have h2 : (a * 10 ^ 10 / z + z) * 10 ^ 10 / (2 * 10 ^ 10) = (a * 10 ^ 10 / z + z) / 2 :=
    Nat.mul_div_mul_right _ _ (by decide)
  have h3 : (a * 10 ^ 10 / z + z) / 2 ≤ 2 ^ 167 - 1 := Nat.le_trans (Nat.div_le_self _ _) h
  have hd : (2 : Int) * DIVISOR = ((2 * 10 ^ 10 : Nat) : Int) := by decide
  have hz' : ((z : Nat) : Int) ≠ (y : Int) := fun c => hne (Int.ofNat.inj c)
  have e3 := ddiv_nat (a := a * 10 ^ 10 / z + z) (b := 2 * 10 ^ 10) (by decide)
    (Nat.le_trans (Nat.le_of_eq h2) h3)
  rw [← hd, h2] at e3
  exact loop_step_of n hz' (ddiv_nat hz hq) (dadd_nat h) e3

/-- The first operation of the seed, `x / 2.0`, on a non-negative decimal. -/
theorem seed_div {a : Nat} (h : a ≤ 2 ^ 167 - 1) :
    ddiv (a : Int) (2 * DIVISOR) = some ((a / 2 : Nat) : Int) := by
  have hd : (2 : Int) * DIVISOR = ((2 * 10 ^ 10 : Nat) : Int) := by decide
  have h2 : a * 10 ^ 10 / (2 * 10 ^ 10) = a / 2 := Nat.mul_div_mul_right _ _ (by decide)
  have h3 : a / 2 ≤ 2 ^ 167 - 1 := Nat.le_trans (Nat.div_le_self _ _) h
  have e := ddiv_nat (a := a) (b := 2 * 10 ^ 10) (by decide) (Nat.le_trans (Nat.le_of_eq h2) h3)
  rewrite [h2] at e
  rewrite [hd]
  exact e

/-- The second operation of the seed, `+ 0.5`. -/
theorem seed_add {a : Nat} (h : a ≤ 2 ^ 167 - 1) :
    dadd ((a / 2 : Nat) : Int) (DIVISOR / 2) = some ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) := by
  have hh : DIVISOR / 2 = ((5 * 10 ^ 9 : Nat) : Int) := by decide
  have h4 : a / 2 + 5 * 10 ^ 9 ≤ 2 ^ 167 - 1 := by
    have e : 5 * 10 ^ 9 + (2 ^ 167 - 1) / 2 ≤ 2 ^ 167 - 1 := by decide
    have := Nat.div_le_div_right (c := 2) h
    generalize 2 ^ 167 - 1 = M at *
    omega
  rewrite [hh]
  exact dadd_nat h4

/-- On a positive decimal `x`, the routine runs the loop from the seed `x / 2 + 5 * 10^9` and
applies the choice to the last two iterates. -/
theorem vyperSqrtWith_pos (fin : Int → Int → Int) {a : Nat} (ha : 0 < a) (h : a ≤ 2 ^ 167 - 1) :
    vyperSqrtWith fin (a : Int) =
      (loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)).map (fun p => fin p.1 p.2) := by
  have h1 : ¬ (a : Int) < 0 := by omega
  have h2 : ¬ (a : Int) = 0 := by omega
  unfold vyperSqrtWith
  rewrite [ite_eq_right h1, ite_eq_right h2, seed_div h, Option.bind_some, seed_add h, Option.bind_some]
  rfl

end VyperSqrt

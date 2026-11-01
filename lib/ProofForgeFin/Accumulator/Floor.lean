import ProofForgeFin.Rounding
import ProofForgeFin.Ledger
/-!
# Sums of amounts rounded down

Rewards credited account by account are rounded down one account at a time, while bounds on what
is owed are stated for the total, rounded down once. These lemmas relate the two for any list of
accounts and any function giving each account's scaled amount: the sum of the parts rounded down
is at most the total rounded down, and below it by less than the number of accounts.

* `sum_map_div_mul_le`, `sum_map_div_le_div`: the sum of the floors is at most the floor of the
  sum.
* `div_sum_map_eq`: the floor of the sum is the sum of the floors plus the sum of the remainders
  rounded down.
* `div_sum_map_lt`: the floor of the sum is below the sum of the floors plus the number of
  accounts.
* `sum_map_div_le_div_of_le`: a pointwise bound carried through the rounding.
-/

namespace ProofForgeFin.Accumulator

universe u

variable {α : Type u}

/-- The parts rounded down, scaled back, never exceed the total. -/
theorem sum_map_div_mul_le (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => f a / c).sum * c ≤ (l.map f).sum :=
  Ledger.sum_map_mul_le l (fun a => f a / c) f c (fun _ _ => Nat.div_mul_le_self _ _)

/-- The sum of the parts rounded down is at most the total rounded down. -/
theorem sum_map_div_le_div (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => f a / c).sum ≤ (l.map f).sum / c := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have h : ∀ l : List α, (l.map fun a => f a / 0).sum = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons] at ih ⊢
        rw [ih, Nat.div_zero]
    rw [h]
    exact Nat.zero_le _
  · exact (Nat.le_div_iff_mul_le hc).2 (sum_map_div_mul_le l f c)

/-- The total is the parts rounded down, scaled back, plus the remainders. -/
theorem sum_map_div_mul_add_mod (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => f a / c).sum * c + (l.map fun a => f a % c).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    have := Nat.div_add_mod (f a) c
    rw [Nat.mul_comm] at this
    omega

/-- The total rounded down is the sum of the parts rounded down plus the sum of the remainders
rounded down. -/
theorem div_sum_map_eq (l : List α) (f : α → Nat) {c : Nat} (hc : 0 < c) :
    (l.map f).sum / c = (l.map fun a => f a / c).sum + (l.map fun a => f a % c).sum / c := by
  rw [← sum_map_div_mul_add_mod l f c, Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.add_comm]

/-- The remainders sum to less than `c` per account. -/
theorem sum_map_mod_le (l : List α) (f : α → Nat) {c : Nat} (hc : 0 < c) :
    (l.map fun a => f a % c).sum ≤ l.length * (c - 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := Nat.mod_lt (f a) hc
    omega

/-- The total rounded down is below the sum of the parts rounded down plus the number of
accounts: rounding each of `n` parts down loses less than `n` units. -/
theorem div_sum_map_lt (l : List α) (f : α → Nat) {c : Nat} (hc : 0 < c) (hl : l ≠ []) :
    (l.map f).sum / c < (l.map fun a => f a / c).sum + l.length := by
  rw [div_sum_map_eq l f hc]
  have h1 := sum_map_mod_le l f hc
  have h2 : (l.map fun a => f a % c).sum / c < l.length := by
    apply (Nat.div_lt_iff_lt_mul hc).2
    have : 0 < l.length := List.length_pos_iff.2 hl
    have : l.length * (c - 1) < l.length * c :=
      Nat.mul_lt_mul_of_pos_left (by omega) this
    omega
  omega

/-- A pointwise bound carried through the rounding: when each part is at most the matching part
of a second function, the sum of the first rounded down part by part is at most the total of the
second rounded down. -/
theorem sum_map_div_le_div_of_le (l : List α) {f g : α → Nat} (c : Nat) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map fun a => f a / c).sum ≤ (l.map g).sum / c :=
  Nat.le_trans (sum_map_div_le_div l f c)
    (Nat.div_le_div_right (Ledger.sum_map_le_sum_map l h))

end ProofForgeFin.Accumulator

import ProofForgeFin.Machine.Accounts
/-!
# Sums by position

A payout or an allocation gives the account at position `i` of a list an amount that depends on
`i` (the first `amount % n` positions get one more unit, the share of the `i`-th weight), and
the requirement sums over accounts. These lemmas move between a sum over the elements of a
list and a sum over its positions `List.range l.length`, and evaluate the sums over positions
that recur: indicators of the first `m` positions, of one position, constants, counts.

* `sumOver_eq_sumOver_range`, `sum_map_eq_sum_range_of_getElem`: a sum over a list equals a sum
  over positions when the summand of the element at position `i` is `g i`. A position function
  that finds the first position of an element gives this hypothesis on a list without duplicates.
* `map_getD_range`, `sum_map_eq_sum_range`, `sumOver_eq_sumOver_range_getD`: the list read back
  by position.
* `sum_range_succ_head`, `sum_range_succ_tail` (and `_int`, `sumOver_range_succ_head`): the
  first or last position split off.
* `sum_range_indicator` (`min m n` positions below `m`), `sum_range_ite_eq` (one position),
  `sum_map_const`, `sum_map_ite_count` and `sum_map_add_ite` (a bonus `e` on the elements where
  a test holds is `e` times the number of them).
-/

namespace ProofForgeFin.Sums

open ProofForgeFin.Ledger

universe u

variable {α : Type u}

/-- A list read back position by position is the list. -/
theorem map_getD_range (d : α) : ∀ l : List α, (List.range l.length).map (fun i => l.getD i d) = l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have : ((fun i => (a :: l).getD i d) ∘ Nat.succ) = fun i => l.getD i d := by
      funext i; simp
    rw [this, map_getD_range d l]; simp

/-- A sum over a list is the sum over its positions of the summand of the element there, on
`Nat`. -/
theorem sum_map_eq_sum_range (f : α → Nat) (d : α) (l : List α) :
    (l.map f).sum = ((List.range l.length).map (fun i => f (l.getD i d))).sum := by
  conv => lhs; rw [← map_getD_range d l]
  rw [List.map_map]; rfl

/-- A sum over a list is the sum over its positions of the summand of the element there, on
`Int`. -/
theorem sum_map_eq_sum_range_int (f : α → Int) (d : α) (l : List α) :
    (l.map f).sum = ((List.range l.length).map (fun i => f (l.getD i d))).sum := by
  conv => lhs; rw [← map_getD_range d l]
  rw [List.map_map]; rfl

/-- `sumOver` a list is `sumOver` its positions of the summand of the element there. -/
theorem sumOver_eq_sumOver_range_getD (f : α → Int) (d : α) (l : List α) :
    sumOver l f = sumOver (List.range l.length) (fun i => f (l.getD i d)) := by
  rw [sumOver_eq_sum_map, sumOver_eq_sum_map, sum_map_eq_sum_range_int f d l]

/-- A sum over a list equals the sum of `g` over its positions when the summand of the element
at every position `i` is `g i` (for example a share looked up by the element's position). -/
theorem sumOver_eq_sumOver_range (l : List α) (h : α → Int) (g : Nat → Int)
    (hg : ∀ i (hi : i < l.length), h l[i] = g i) : sumOver l h = sumOver (List.range l.length) g := by
  induction l generalizing g with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, sumOver_cons, sumOver_cons, Machine.sumOver_map]
    have h0 := hg 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h0, ih (fun i => g (i + 1)) (fun i hi => by
      have h1 := hg (i + 1) (by simp; omega)
      rwa [List.getElem_cons_succ] at h1)]

/-- A sum over a list equals the sum of `g` over its positions when the summand of the element
at every position `i` is `g i`, on `Nat`. -/
theorem sum_map_eq_sum_range_of_getElem (l : List α) (h : α → Nat) (g : Nat → Nat)
    (hg : ∀ i (hi : i < l.length), h l[i] = g i) : (l.map h).sum = ((List.range l.length).map g).sum := by
  induction l generalizing g with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    have h0 := hg 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    simp only [List.map_cons, List.sum_cons, List.map_map, h0]
    rw [ih (fun i => g (i + 1)) (fun i hi => by
      have h1 := hg (i + 1) (by simp; omega)
      rwa [List.getElem_cons_succ] at h1)]
    rfl

/-- The first position of a sum over `List.range (n + 1)` split off, the rest shifted by one,
on `Nat`. -/
theorem sum_range_succ_head (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map (fun i => f (i + 1))).sum := by
  rw [List.range_succ_eq_map]; simp [List.map_map]; rfl

/-- The first position of a sum over `List.range (n + 1)` split off, on `Int`. -/
theorem sum_range_succ_head_int (f : Nat → Int) (n : Nat) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map (fun i => f (i + 1))).sum := by
  rw [List.range_succ_eq_map]; simp [List.map_map]; rfl

/-- The first position of `sumOver (List.range (n + 1)) f` split off. -/
theorem sumOver_range_succ_head (f : Nat → Int) (n : Nat) :
    sumOver (List.range (n + 1)) f = f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by
  rw [sumOver_eq_sum_map, sumOver_eq_sum_map, sum_range_succ_head_int]

/-- The last position of a sum over `List.range (n + 1)` split off, on `Nat`. -/
theorem sum_range_succ_tail (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  simp [List.range_succ]

/-- The last position of a sum over `List.range (n + 1)` split off, on `Int`. -/
theorem sum_range_succ_tail_int (f : Nat → Int) (n : Nat) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  simp [List.range_succ]

/-- Of `n` positions, `min m n` are below `m`: the indicator of the first `m` positions sums to
`min m n`, on `Nat`. -/
theorem sum_range_indicator (m : Nat) : ∀ n : Nat,
    ((List.range n).map (fun i => if i < m then 1 else 0)).sum = min m n
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ_tail, sum_range_indicator m n]
    split <;> omega

/-- The indicator of the first `m` positions sums to `min m n` over `n` positions, on `Int`. -/
theorem sum_range_indicator_int (m : Nat) (n : Nat) :
    ((List.range n).map (fun i => if i < m then (1 : Int) else 0)).sum = (min m n : Nat) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ_tail_int, ih]
    split <;> omega

/-- The indicator of the first `m` positions sums to `min m n` over `n` positions, as
`sumOver`. -/
theorem sumOver_range_indicator (m n : Nat) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (min m n : Nat) := by
  rw [sumOver_eq_sum_map, sum_range_indicator_int]

/-- A value at one position `x`, summed over `n` positions, is the value if `x < n` and zero
otherwise, on `Nat`. -/
theorem sum_range_ite_eq (x c : Nat) : ∀ n : Nat,
    ((List.range n).map (fun i => if i = x then c else 0)).sum = if x < n then c else 0
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ_tail, sum_range_ite_eq x c n]
    by_cases h1 : x < n
    · have : n ≠ x := by omega
      simp [h1, this, show x < n + 1 by omega]
    · by_cases h2 : x = n
      · subst h2; simp
      · simp [h1, show ¬ x < n + 1 by omega, Ne.symm h2]

/-- A value at one position `x`, summed over `n` positions, on `Int`. -/
theorem sum_range_ite_eq_int (x : Nat) (c : Int) (n : Nat) :
    ((List.range n).map (fun i => if i = x then c else 0)).sum = if x < n then c else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ_tail_int, ih]
    by_cases h1 : x < n
    · have : n ≠ x := by omega
      simp [h1, this, show x < n + 1 by omega]
    · by_cases h2 : x = n
      · subst h2; simp
      · simp [h1, show ¬ x < n + 1 by omega, Ne.symm h2]

/-- A constant summed over a list is the length times the constant, on `Nat`. -/
theorem sum_map_const (c : Nat) (l : List α) : (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.succ_mul]; omega

/-- A constant summed over a list is the length times the constant, on `Int`. -/
theorem sum_map_const_int (c : Int) (l : List α) : (l.map (fun _ => c)).sum = (l.length : Int) * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.add_mul]; omega

/-- `e` on the elements where a test holds, summed, is `e` times the number of them, on
`Nat`. -/
theorem sum_map_ite_count (p : α → Bool) (e : Nat) (l : List α) :
    (l.map (fun a => if p a then e else 0)).sum = e * (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih, Nat.mul_succ] <;> omega

/-- `e` on the elements where a test holds, summed, is `e` times the number of them, on
`Int`. -/
theorem sum_map_ite_count_int (p : α → Bool) (e : Int) (l : List α) :
    (l.map (fun a => if p a then e else 0)).sum = e * (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih, Int.mul_add] <;> omega

/-- A base amount plus a bonus `e` on the elements where a test holds, summed: the base sum plus
`e` times the number of elements with the bonus, on `Nat`. -/
theorem sum_map_add_ite (b : α → Nat) (p : α → Bool) (e : Nat) (l : List α) :
    (l.map (fun a => b a + if p a then e else 0)).sum = (l.map b).sum + e * (l.filter p).length := by
  rw [← sum_map_ite_count]; exact Machine.sum_map_add l b _

/-- A base amount plus a bonus `e` on the elements where a test holds, summed, on `Int`. -/
theorem sum_map_add_ite_int (b : α → Int) (p : α → Bool) (e : Int) (l : List α) :
    (l.map (fun a => b a + if p a then e else 0)).sum = (l.map b).sum + e * (l.filter p).length := by
  rw [← sum_map_ite_count_int]
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

end ProofForgeFin.Sums

import ProofForgeFin.Machine.Accounts
/-!
# Sums after one entry changes

A step changes one entry of a ledger: one position of a list of balances (`List.set`), or one
account of a balance function, written by the specification as a function with an `if` on the
account. These lemmas give the new total from the old total and the change, the shape every
conservation and bound argument over a step reduces to.

* Positions: `sum_set_add` and `sum_map_set_add` (`Nat`, with the old entry added on the left
  so no subtraction is needed), `sum_set_int`, `sum_map_set_int` and `sumOver_set` (`Int`),
  `sum_map_set_eq` (an entry replaced by one with the same summand).
* Accounts, over a list without duplicates: `sumOver_add_ite` and `sumOver_sub_ite` (a delta
  on one account), `sumOver_ite_update` (one account overwritten), `sumOver_move` (an amount
  moved between two accounts, as the specification writes it).

`ProofForgeFin.Ledger` has the same facts for its named updates (`adjust`, `transfer`, `upd`,
`List.modify`); `lib_defs` turns a restated update into those.
-/

namespace ProofForgeFin.Sums

open ProofForgeFin.Ledger

universe u

variable {α : Type u}

/-- A list of `Nat` with the entry at position `i` set to `x`: the new sum plus the old entry
is the old sum plus `x`. -/
theorem sum_set_add : ∀ (l : List Nat) (i x : Nat) (h : i < l.length), (l.set i x).sum + l[i] = l.sum + x
  | [], _, _, h => absurd h (by simp)
  | a :: l, 0, x, _ => by simp; omega
  | a :: l, i + 1, x, h => by
    have := sum_set_add l i x (by simpa using h)
    simp; omega

/-- A list of `Int` with the entry at position `i` set to `x`: the sum changes by `x` minus the
old entry. -/
theorem sum_set_int : ∀ (l : List Int) (i : Nat) (x : Int) (h : i < l.length), (l.set i x).sum = l.sum - l[i] + x
  | [], _, _, h => absurd h (by simp)
  | a :: l, 0, x, _ => by simp; omega
  | a :: l, i + 1, x, h => by
    have := sum_set_int l i x (by simpa using h)
    simp [this]; omega

/-- A list of records with the record at position `i` replaced by `x`, summed through a field
`g` (on `Nat`): the new sum plus the old summand is the old sum plus the new summand. -/
theorem sum_map_set_add (g : α → Nat) : ∀ (l : List α) (i : Nat) (x : α) (h : i < l.length),
    ((l.set i x).map g).sum + g l[i] = (l.map g).sum + g x
  | [], _, _, h => absurd h (by simp)
  | a :: l, 0, x, _ => by
    simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]; omega
  | a :: l, i + 1, x, h => by
    have := sum_map_set_add g l i x (by simpa using h)
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]; omega

/-- A list of records with the record at position `i` replaced by `x`, summed through `g` (on
`Int`): the sum changes by the new summand minus the old. -/
theorem sum_map_set_int (g : α → Int) : ∀ (l : List α) (i : Nat) (x : α) (h : i < l.length),
    ((l.set i x).map g).sum = (l.map g).sum - g l[i] + g x
  | [], _, _, h => absurd h (by simp)
  | a :: l, 0, x, _ => by
    simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]; omega
  | a :: l, i + 1, x, h => by
    have := sum_map_set_int g l i x (by simpa using h)
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]; omega

/-- `sumOver` a list with the element at position `i` replaced by `x`. -/
theorem sumOver_set (g : α → Int) (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    sumOver (l.set i x) g = sumOver l g - g l[i] + g x := by
  rw [sumOver_eq_sum_map, sumOver_eq_sum_map, sum_map_set_int g l i x h]

/-- Replacing the record at position `i` by one with the same summand leaves the sum unchanged
(a position past the end leaves the list unchanged). -/
theorem sum_map_set_eq (g : α → Nat) (l : List α) (i : Nat) (x : α)
    (h : ∀ hi : i < l.length, g x = g l[i]) : ((l.set i x).map g).sum = (l.map g).sum := by
  by_cases hi : i < l.length
  · have := sum_map_set_add g l i x hi; have := h hi; omega
  · rw [List.set_eq_of_length_le (by omega)]

/-- Over accounts without duplicates, adding `d` to the balance of one account `x` adds `d` to
the total if `x` is an account. -/
theorem sumOver_add_ite [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → Int) (x : α) (d : Int) :
    sumOver l (fun a => f a + if a = x then d else 0) = sumOver l f + if x ∈ l then d else 0 := by
  rw [sumOver_add, sumOver_ite_eq hl]

/-- Over accounts without duplicates, subtracting `d` from the balance of one account `x`
subtracts `d` from the total if `x` is an account. -/
theorem sumOver_sub_ite [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → Int) (x : α) (d : Int) :
    sumOver l (fun a => f a - if a = x then d else 0) = sumOver l f - if x ∈ l then d else 0 := by
  rw [sumOver_sub, sumOver_ite_eq hl]

/-- Over accounts without duplicates, overwriting the balance of an account `x` with `v`
changes the total by `v` minus the old balance. -/
theorem sumOver_ite_update [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → Int) (x : α) (v : Int)
    (hx : x ∈ l) : sumOver l (fun a => if a = x then v else f a) = sumOver l f - f x + v :=
  Machine.sumOver_upd hl f hx v

/-- Over accounts without duplicates, moving `x` from one account to another (both accounts,
possibly equal), written with an `if` on each, leaves the total unchanged. -/
theorem sumOver_move [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → Int) {src dst : α} (x : Int)
    (hs : src ∈ l) (hd : dst ∈ l) :
    sumOver l (fun a => (f a - if a = src then x else 0) + if a = dst then x else 0) = sumOver l f :=
  sumOver_transfer hl f x hs hd

end ProofForgeFin.Sums

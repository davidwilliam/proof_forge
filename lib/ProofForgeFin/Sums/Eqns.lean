import ProofForgeFin.Ledger
/-!
# Sums identified by their equations

Specifications and proofs often define their own sums: a sum by pattern matching on a list,
a sum over the first `n` indices by recursion on `n`, a running total by `List.foldl`. The library states its sum
facts over `List.sum` of a mapped list and over `ProofForgeFin.Ledger.sumOver`; a recursive
restatement is not definitionally equal to them, so neither `exact?` nor the `lib_defs` tactic
connects the two.

The lemmas here connect them by the defining equations alone: a function on lists with
`F [] = 0` and `F (a :: l) = f a + F l` is `(l.map f).sum`, and a function on `Nat` with
`F 0 = 0` and `F (n + 1) = F n + f n` is the sum of `f` over `List.range n`. For a restatement
the equations usually hold by `rfl`: for `S` defined by `S [] = 0` and `S (x :: xs) = x + S xs`,

```
example (l : List Nat) : S l = l.sum := by
  simpa using eq_sum_map_of_eqns (F := S) id rfl (fun _ _ => rfl) l
```

Folds that accumulate from the left are sums too (`foldl_add_eq`).
-/

namespace ProofForgeFin.Sums

open ProofForgeFin.Ledger

universe u

variable {α : Type u}

/-- A function on lists with `F [] = 0` and `F (a :: l) = f a + F l` (a sum restated by
recursion) is the sum of the mapped list, on `Nat`. -/
theorem eq_sum_map_of_eqns {F : List α → Nat} (f : α → Nat) (h0 : F [] = 0)
    (hc : ∀ a l, F (a :: l) = f a + F l) : ∀ l, F l = (l.map f).sum
  | [] => by simp [h0]
  | a :: l => by simp [hc, eq_sum_map_of_eqns f h0 hc l]

/-- A function on lists with `F [] = 0` and `F (a :: l) = f a + F l` is the sum of the mapped
list, on `Int`. -/
theorem eq_sum_map_of_eqns_int {F : List α → Int} (f : α → Int) (h0 : F [] = 0)
    (hc : ∀ a l, F (a :: l) = f a + F l) : ∀ l, F l = (l.map f).sum
  | [] => by simp [h0]
  | a :: l => by simp [hc, eq_sum_map_of_eqns_int f h0 hc l]

/-- A function on lists with `F [] = 0` and `F (a :: l) = f a + F l` is `sumOver l f`. -/
theorem eq_sumOver_of_eqns {F : List α → Int} (f : α → Int) (h0 : F [] = 0)
    (hc : ∀ a l, F (a :: l) = f a + F l) (l : List α) : F l = sumOver l f := by
  rw [eq_sum_map_of_eqns_int f h0 hc l, sumOver_eq_sum_map]

/-- A function on `Nat` with `F 0 = 0` and `F (n + 1) = F n + f n` (a sum over the first `n`
indices restated by recursion) is the sum of `f` over `List.range n`, on `Nat`. -/
theorem eq_sum_range_of_eqns {F : Nat → Nat} (f : Nat → Nat) (h0 : F 0 = 0)
    (hs : ∀ n, F (n + 1) = F n + f n) : ∀ n, F n = ((List.range n).map f).sum
  | 0 => by simp [h0]
  | n + 1 => by simp [hs, eq_sum_range_of_eqns f h0 hs n, List.range_succ]

/-- A function on `Nat` with `F 0 = 0` and `F (n + 1) = F n + f n` is the sum of `f` over
`List.range n`, on `Int`. -/
theorem eq_sum_range_of_eqns_int {F : Nat → Int} (f : Nat → Int) (h0 : F 0 = 0)
    (hs : ∀ n, F (n + 1) = F n + f n) : ∀ n, F n = ((List.range n).map f).sum
  | 0 => by simp [h0]
  | n + 1 => by simp [hs, eq_sum_range_of_eqns_int f h0 hs n, List.range_succ]

/-- A function on `Nat` with `F 0 = 0` and `F (n + 1) = F n + f n` is
`sumOver (List.range n) f`. -/
theorem eq_sumOver_range_of_eqns {F : Nat → Int} (f : Nat → Int) (h0 : F 0 = 0)
    (hs : ∀ n, F (n + 1) = F n + f n) (n : Nat) : F n = sumOver (List.range n) f := by
  rw [eq_sum_range_of_eqns_int f h0 hs n, sumOver_eq_sum_map]

/-- A left fold that adds `f a` for every element is the start value plus the sum, on `Nat`. -/
theorem foldl_add_eq (f : α → Nat) : ∀ (l : List α) (c : Nat),
    l.foldl (fun acc a => acc + f a) c = c + (l.map f).sum
  | [], c => by simp
  | a :: l, c => by simp [foldl_add_eq f l (c + f a)]; omega

/-- A left fold that adds `f a` for every element is the start value plus the sum, on `Int`. -/
theorem foldl_add_eq_int (f : α → Int) : ∀ (l : List α) (c : Int),
    l.foldl (fun acc a => acc + f a) c = c + (l.map f).sum
  | [], c => by simp
  | a :: l, c => by simp [foldl_add_eq_int f l (c + f a)]; omega

/-- A right fold that adds `f a` for every element, from `0`, is the sum, on `Nat` (the `Nat`
counterpart of `sumOver`). -/
theorem foldr_add_eq (f : α → Nat) (l : List α) :
    l.foldr (fun a acc => f a + acc) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

end ProofForgeFin.Sums

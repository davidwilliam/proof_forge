Order-independence follows because `step` depends on the entry list only through `decision`, which depends only through `best` on the maximum depth in the filtered allow/deny lists. A permutation preserves the filtered lists up to permutation, and folding `max` over a list is invariant under permutation; the adjacent-swap case is just commutativity/associativity of `max`.

```lean
theorem plan3_fold_max_swap (x y : Entry) (F : List Entry) (m : Option Nat) :
    (y :: x :: F).foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m =
    (x :: y :: F).foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) m := by sorry

theorem plan3_fold_max_perm {F1 F2 : List Entry} (h : F1.Perm F2) :
    F1.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none =
    F2.foldl (fun (o : Option Nat) (e : Entry) => some (max (o.getD 0) (depth e))) none := by sorry

theorem plan3_best_perm (eff : Effect) (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : best eff r l1 = best eff r l2 := by sorry

theorem plan3_decision_perm (r : Request) {l1 l2 : List Entry}
    (h : l1.Perm l2) : decision l1 r = decision l2 r := by sorry

theorem plan3_step_fst_of_perm (s : State) (r : Request) (l : List Entry)
    (h : l.Perm s.entries) :
    (step { s with entries := l } r).1 = (step s r).1 := by sorry
```